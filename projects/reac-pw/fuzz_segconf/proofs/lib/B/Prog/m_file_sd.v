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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v; 548 of its 606 lines of code are new or changed and 395 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3): the shared mid-walk seed of its segment lanes, the
   image-B twin of the image-A m_file-family lane's lib/A/Prog/m_file_sd.v (commit c2b1bbf6257f, its version 3),
   after plugin-hostd/fuzz_command's lib/A/Prog/check_reply_sd.v cr_seed (origin/ossv/recipes 501c0d516c69): from the
   cut facts of lib/B/Prog/m_file_m.v (mf_cx, mf_core, mf_cells, mf_np and the base registers) the symbolic state
   st_ok_pi at ANY listing offset pc after the frame call (0x861b4). A walk lane of the image-B m_file-family owner's G2B, the one
   writer of this file and of m_file_m.v. Statement text and its proof; no instruction is executed here.

   CHANGE LOG (newest first):
   - 1: the first text: image A's version 3 at image B's frame (320 bytes, s1 = (sp0 - 320) & -32), image B's frame
     cells (the image-B m_file cut map table C.1) and SegInstB's values (STK_m_file 8,592, wordsA 0xa2040), plus what the strip
     and fold call sites need of the frame (mf_stk_sh0, mf_slot_addr, mf_low_addr).

   THE ATOMS (0..31 are the registers at pc; mfE regs1 v lyc pos cur np xs), image A's numbering:
     32 SB = SHADOW_OFF     33 c (the mconf block)     34 FB = frame_addr lyc 1 pos (the side-stack frame)
     35 FL = flag_addr lyc 1 pos (its flag cell)        36 SF = SHADOW_OFF + FB / 8 (its shadow)
     37 the 136(s1) value mf_cur_ptr c cur              38 np (the 152(s1) value when hnp = true)
     39 .. 51 the entry's ra, s0, .., s11 (stored at sp0 - 8, .., sp0 - 104)
     52 .. the caller's extra values xs, in order (52 + i = nth i xs)
   and from A_TEXT = 240 the listing's image values (Eimg): A_OBJ 15 = m_key.words 0xa2040 (SegInstB.wordsA), etc.
   THE REGISTERS: only s1 = sp (SOff 2 0) and s2 = SB (SOff 32 0) are symbolic; every other register is its own atom
   (s0 = atom 8 = sp0). Pin more with ast_ok_pi_set_reg_fp (PaLibF.v): s7 = atom 34, s8 = atom 36, s9 = atom 33 at
   every cut (mf_regs_at).
   THE REGIONS (ss_mf pc cells hnp slx hw lw lowcs shw lowsh; mf_regions):
     0 the saved registers, base atom 8, [-104, 0), read-only, chunk -8 - 8 j = atom 39 + j
     1 the frame cells, base atom 2 (s1 = sp), [16, 216), WRITABLE: 120 = FB always; with cells = true the cells of
       mf_cells: 16 ~c as (-1) - c (mf_notx), 24 c + 0x2004, 32 c + 0x238c, 40 ~(c + 0x238c), 48 c + 0x23ac, 56
       c + 0x23b0, 64 c + 0x23b4, 72 shadow(words) as (A_OBJ 15 >> 3) + SB, 80 A_OBJ 15, 88 SF, 96 FB, 104
       shadow(c + 0x23b0) as (c + 0x23b0 >> 3) + SB (so `ld; lb` reads as a shadow check), 112 c, 128 c + 0x2000, 136
       atom 37, 144 FB + 32; with hnp = true 152 = atom 38; then the caller's chunks slx (the per-line cells 168 ..
       208 that strip reads and writes)
     2 the frame header, base atom 34, [0, 32), writable iff hw
     3 low.i, base atom 34, [32, 96), writable iff lw, the caller's chunks lowcs
     4 the frame tail, base atom 34, [96, 128), read-only, 120 = atom 35 (the flag pointer)
     5 the frame's shadow, base atom 36, [0, 16), writable iff shw (keep shw = false for a token run: a writable
       region in the shadow span is outside sh_static_ok), bytes 4 .. 11 = lowsh (low.i's shadow)
   No region of the mconf block, of the text or of the flag cell: add yours with st_ok_pi_add_region (SegPaLib.v)
   at atom 33 / your xs atoms / atom 35 (mf_txt_region gives a text region).
   FACTS: 2 (s1) in [2^46, 2^47], 32-aligned; 8 (sp0) 16-aligned; 32 = SB; 33 c (HPTR 4); 34 FB (HPTR 5); 35 FL
   (HPTR 0); 36 SF in [SB + 512, SB + 2^44], 4-aligned.
   THE SHADOW ENTRY mf_she_blk: the block [c, c + hi) (atom 33), from mf_core's sa_addr.
   THE LITERAL BRIDGE: MF_LIT_OBJS (m_file's literals with their listing object; image B's lib/B/Prog/SegAddr.v
   seg_objs numbers them as image A's does: 13 0x210a0 .. 28 0x210e0, words 15 0xa2040, role 18 0x211e0, each
   checked against the twin's .symtab), mf_lit_obj, mf_words_obj, mf_roles_obj, all under the shared Section
   hypothesis VOBJS : seg_val_objs.
   THE STRIP AND FOLD CALL SITES (image B only; strip_c.v / fold_c.v of the image-B contracts lane): mf_slot_addr gives each
   8-byte frame cell [s1 + 16, s1 + 216) addressable (sa_addr: the thread stack's shadow is 0 by AR's zshadow_ok,
   mf_stk_sh0), present and at or above sp, which strip_args / strip_slot ask of the cells 176 / 168, 208 / 200,
   192 / 184 (s1 is 32-aligned, so the cells are 8-aligned); mf_low_addr gives low.i's first k <= 64 bytes
   addressable and inside the live side-stack frame (1, pos) when its shadow is 0 (the K cuts), which fold_pre asks
   of out = FB + 32 at 0x86738 (cap 64) and 0x8686c (cap 24). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ===================================== the literal bridge ===================================== *)
(* m_file's literals (m_file_c.M_FILE_LITS) with the listing object the code forms each at (image B's SegAddr.v
   seg_objs: 14 0x21080 "%s", 13 0x210a0 "reac-pw.conf", 16 0x21100 "segment", 17 0x21120 "role", 19 0x21220
   "model", 20 0x21240 "ignore", 21 0x21260 "yes", 22 0x21280 "true", 23 0x212a0 "no", 24 0x212c0 "false", 25
   0x212e0 "knock", 27 0x210c0 "%s:%d: ", 28 0x210e0 "%s: "); m_key.words is object 15 (0xa2040), m_key.role object
   18 (0x211e0) *)
Definition MF_LIT_OBJS : list (list Z * nat) :=
  [(F_s, 14%nat); (S_base, 13%nat); (S_segment, 16%nat); (S_role, 17%nat); (S_model, 19%nat);
   (S_ignore, 20%nat); (S_yes, 21%nat); (S_true, 22%nat); (S_no, 23%nat); (S_false, 24%nat);
   (S_knock, 25%nat); (F_addr_line, 27%nat); (F_addr, 28%nat)].
Definition MF_WORDS_OBJ : nat := 15.
Definition MF_ROLES_OBJ : nat := 18.

(* ===================================== the seed's shape ===================================== *)
(* the symbolic registers: s1 = sp, s2 = SB, the rest their own atoms *)
Definition sr_mf : list sv := Eval vm_compute in
sr_set (sr_set sr_atoms (9%bv : bv 5) (SOff 2 0)) (18%bv : bv 5) (SOff 32 0).
(* the shadow address of a byte at atom n + k, as the code forms it: (x >> 3) + SB *)
Definition mf_shx (n : nat) (k : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff n k) (SLit 3)) (SOff 32 0).
(* the bitwise complement of atom n + k (the code's `not`: 0x86320, 0x86364): (-1) - x *)
Definition mf_notx (n : nat) (k : Z) : sv := SAlu ALU_SUB (SLit (-1)) (SOff n k).
Definition mf_r_saved : YP09.region := Eval vm_compute in
YP09.mkRegion (Some 8%nat) (-104) 0 0 0
(map (fun j => YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (39 + j) 0))) (seq 0 13)).
Definition mf_chunk120 : YP09.chunk := YP09.mkChunk 120 (CVal 8 (SOff 34 0)).
Definition mf_chunk152 : YP09.chunk := YP09.mkChunk 152 (CVal 8 (SOff 38 0)).
Definition mf_cell_chunks : list YP09.chunk :=
[YP09.mkChunk 16 (CVal 8 (mf_notx 33 0)); YP09.mkChunk 24 (CVal 8 (SOff 33 seg_spec.MC_OVERFLOW));
 YP09.mkChunk 32 (CVal 8 (SOff 33 seg_spec.MC_KNOCK)); YP09.mkChunk 40 (CVal 8 (mf_notx 33 seg_spec.MC_KNOCK));
 YP09.mkChunk 48 (CVal 8 (SOff 33 seg_spec.MC_NKEPT)); YP09.mkChunk 56 (CVal 8 (SOff 33 seg_spec.MC_GEN));
 YP09.mkChunk 64 (CVal 8 (SOff 33 seg_spec.MC_READING)); YP09.mkChunk 72 (CVal 8 (mf_shx (A_OBJ MF_WORDS_OBJ) 0));
 YP09.mkChunk 80 (CVal 8 (SOff (A_OBJ MF_WORDS_OBJ) 0)); YP09.mkChunk 88 (CVal 8 (SOff 36 0));
 YP09.mkChunk 96 (CVal 8 (SOff 34 0)); YP09.mkChunk 104 (CVal 8 (mf_shx 33 seg_spec.MC_GEN));
 YP09.mkChunk 112 (CVal 8 (SOff 33 0)); YP09.mkChunk 128 (CVal 8 (SOff 33 seg_spec.MC_N));
 YP09.mkChunk 136 (CVal 8 (SOff 37 0)); YP09.mkChunk 144 (CVal 8 (SOff 34 32))].
Definition mf_r_slots (cells hnp : bool) (slx : list YP09.chunk) : YP09.region :=
YP09.mkRegion (Some 2%nat) 16 216 16 216
(mf_chunk120 :: (if cells then mf_cell_chunks else []) ++ (if hnp then [mf_chunk152] else []) ++ slx).
Definition mf_r_fh (hw : bool) : YP09.region := YP09.mkRegion (Some 34%nat) 0 32 0 (if hw then 32 else 0) [].
Definition mf_r_low (lw : bool) (lowcs : list YP09.chunk) : YP09.region :=
YP09.mkRegion (Some 34%nat) 32 96 (if lw then 32 else 0) (if lw then 96 else 0) lowcs.
Definition mf_r_ft : YP09.region := YP09.mkRegion (Some 34%nat) 96 128 0 0 [YP09.mkChunk 120 (CVal 8 (SOff 35 0))].
Definition mf_r_fs (shw : bool) (lowsh : Z) : YP09.region :=
YP09.mkRegion (Some 36%nat) 0 16 0 (if shw then 16 else 0)
(map (fun k => YP09.mkChunk (4 + Z.of_nat k) (CVal 1 (SLit lowsh))) (seq 0 8)).
Definition mf_regions (cells hnp : bool) (slx : list YP09.chunk) (hw lw : bool) (lowcs : list YP09.chunk)
(shw : bool) (lowsh : Z) : smem :=
[mf_r_saved; mf_r_slots cells hnp slx; mf_r_fh hw; mf_r_low lw lowcs; mf_r_ft; mf_r_fs shw lowsh].
Definition mf_facts : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (8%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
          (33%nat, HPTR 4); (34%nat, HPTR 5); (35%nat, HPTR 0);
          (36%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 2) ] [] [].
Definition ss_mf (pc : Z) (cells hnp : bool) (slx : list YP09.chunk) (hw lw : bool) (lowcs : list YP09.chunk)
(shw : bool) (lowsh : Z) : sstate :=
mkSS pc sr_mf (mf_regions cells hnp slx hw lw lowcs shw lowsh) None mf_facts.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the environment of the seed *)
Definition mf_extra (v : mfv) (lyc : alayout) (pos : Z) (cur : option nat) (np : Z) (xs : list Z) : list word :=
map (Z_to_bv 64) [SHADOW_OFF; mv_c v; frame_addr lyc 1 pos; flag_addr lyc 1 pos;
  SHADOW_OFF + frame_addr lyc 1 pos / 8; mf_cur_ptr (mv_c v) cur; np]
++ map (fun r => getr (mv_regs v) (Z_to_bv 5 r)) mf_saved_regs ++ map (Z_to_bv 64) xs.
Definition mfE (regs1 : bvmap 5 word) (v : mfv) (lyc : alayout) (pos : Z) (cur : option nat) (np : Z)
(xs : list Z) : env :=
Eimg (Ereg regs1 (mf_extra v lyc pos cur np xs)).
(* the registers the seed takes: sp = s1, s0 = sp0, s1, s2 = SB *)
Definition mf_regs_base (v : mfv) (regs1 : bvmap 5 word) : Prop :=
getr regs1 2 = w64 (mf_s1 (mv_sp v)) /\ getr regs1 8 = w64 (mv_sp v) /\ getr regs1 9 = w64 (mf_s1 (mv_sp v)) /\
getr regs1 18 = w64 SHADOW_OFF.

Lemma mfE_low : forall regs1 v lyc pos cur np xs k, (k < A_TEXT)%nat ->
ew (mfE regs1 v lyc pos cur np xs) k = ew (Ereg regs1 (mf_extra v lyc pos cur np xs)) k.
Proof. intros. unfold mfE. apply Eimg_low. exact H. Qed.
Lemma mfE_reg : forall regs1 v lyc pos cur np xs k (r : bv 5), Z.of_nat k = bv_unsigned r ->
ew (mfE regs1 v lyc pos cur np xs) k = getr regs1 r.
Proof.
intros regs1 v lyc pos cur np xs k r Hk. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
rewrite mfE_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk.
Qed.
Lemma mfE_extra : forall regs1 v lyc pos cur np xs j, (32 + j < A_TEXT)%nat ->
ew (mfE regs1 v lyc pos cur np xs) (32 + j) = nth j (mf_extra v lyc pos cur np xs) (Z_to_bv 64 0).
Proof. intros. rewrite mfE_low by exact H. apply ew_Ereg_extra. Qed.
Lemma mfE_img : forall regs1 v lyc pos cur np xs n, (A_TEXT <= n < A_LIM)%nat ->
ew (mfE regs1 v lyc pos cur np xs) n = Z_to_bv 64 (VAL n).
Proof. intros. unfold mfE. apply Eimg_img. exact H. Qed.
(* the caller's extra value i *)
Lemma mfE_xs : forall regs1 v lyc pos cur np xs i, (52 + i < A_TEXT)%nat ->
ew (mfE regs1 v lyc pos cur np xs) (52 + i) = Z_to_bv 64 (nth i xs 0).
Proof.
intros regs1 v lyc pos cur np xs i Hi.
replace (52 + i)%nat with (32 + (20 + i))%nat by lia. rewrite mfE_extra by lia.
unfold mf_extra. rewrite app_assoc.
assert (HL : length (map (Z_to_bv 64) [SHADOW_OFF; mv_c v; frame_addr lyc 1 pos; flag_addr lyc 1 pos;
  SHADOW_OFF + frame_addr lyc 1 pos / 8; mf_cur_ptr (mv_c v) cur; np] ++
  map (fun r => getr (mv_regs v) (Z_to_bv 5 r)) mf_saved_regs) = 20%nat)
  by (rewrite length_app, !length_map; reflexivity).
rewrite app_nth2 by (rewrite HL; lia). rewrite HL. replace (20 + i - 20)%nat with i by lia.
exact (map_nth (Z_to_bv 64) xs 0%Z i).
Qed.

Section e.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* the literal bridge *)
Lemma mf_lit_obj : forall x i, In (x, i) MF_LIT_OBJS -> SegInstB.seg_litA_fz x = VAL (A_OBJ i).
Proof.
intros x i H. unfold MF_LIT_OBJS in H.
repeat (destruct H as [H|H];
  [ inversion H; subst; erewrite VOBJS by (apply Nat.ltb_lt; vm_compute; reflexivity); vm_compute; reflexivity | ]).
destruct H.
Qed.
Lemma mf_words_obj : SegInstB.wordsA = VAL (A_OBJ MF_WORDS_OBJ).
Proof. erewrite VOBJS by (apply Nat.ltb_lt; vm_compute; reflexivity). vm_compute. reflexivity. Qed.
Lemma mf_roles_obj : SegInstB.rolesA = VAL (A_OBJ MF_ROLES_OBJ).
Proof. erewrite VOBJS by (apply Nat.ltb_lt; vm_compute; reflexivity). vm_compute. reflexivity. Qed.

(* mf_regs_ex (and so mf_regs_at) gives the seed's registers *)
Lemma mf_regs_base_of_ex : forall v lyc pos regs1, mf_regs_ex B v lyc pos regs1 -> mf_regs_base v regs1.
Proof. intros v lyc pos regs1 (R2 & _ & _ & R8 & R9 & R18 & _). repeat split; assumption. Qed.
Lemma mf_regs_base_of : forall v lyc pos regs1, mf_regs_at B v lyc pos regs1 -> mf_regs_base v regs1.
Proof. intros v lyc pos regs1 [H _]. exact (mf_regs_base_of_ex v lyc pos regs1 H). Qed.

Lemma mf_regs_ok : forall v regs1 lyc pos cur np xs, mf_regs_base v regs1 ->
regs_ok (mfE regs1 v lyc pos cur np xs) sr_mf regs1.
Proof.
intros v regs1 lyc pos cur np xs (R2 & R8 & R9 & R18).
set (E := mfE regs1 v lyc pos cur np xs).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros; apply mfE_reg; assumption).
pose proof (mfE_extra regs1 v lyc pos cur np xs 0 ltac:(unfold A_TEXT; lia)) as E32.
cbn [Nat.add nth mf_extra map app] in E32. fold E in E32.
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr];
[ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) => let w := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with w end;
  cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
  first [ symmetry; apply EE; reflexivity | symmetry; apply getr_zero | reflexivity
  | rewrite (EE 2%nat 2%bv eq_refl), R9, R2; reflexivity
  | rewrite E32; exact R18 ]
| ]); try (destruct Hr; fail).
Qed.

(* an 8-byte chunk holding atom n + k *)
Lemma mf_chunk_atom : forall E m base off (n : nat) k x,
ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + k < 2 ^ 64 ->
val_mem SEGS m (base + off) 8 (x + k) -> YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal 8 (SOff n k))).
Proof.
intros E m base off n k x Hn Hx Hxk Hv.
apply (chunk_ok_val SEGS E m base off 8 (SOff n k) (x + k)); [| exact Hxk | cbn; lia | exact Hv].
cbn [sv_denot]. rewrite Hn. rewrite unsigned_lit_small by lia. reflexivity.
Qed.
(* the shadow address expression of atom n + k *)
Lemma mf_denot_shx : forall E (n : nat) x k, ew E n = Z_to_bv 64 x -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
0 <= x < 2 ^ 47 -> 0 <= k -> x + k < 2 ^ 47 ->
sv_denot E (mf_shx n k) = Z_to_bv 64 (SHADOW_OFF + (x + k) / 8).
Proof.
intros E n x k Hn H32 Hx Hk Hxk. rewrite denot_lit_U. f_equal. unfold mf_shx.
rewrite U_SAlu, U_srl3, !U_SOff, Hn, H32.
rewrite (unsigned_lit_small x) by lia. rewrite (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
rewrite Z.add_0_r. rewrite (zcanon_id (x + k)) by (unfold M64; lia).
rewrite (zcanon_id SHADOW_OFF) by (unfold M64, SHADOW_OFF; lia).
cbn [zalu_raw].
pose proof (Z.div_pos (x + k) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound (x + k) 8 (2 ^ 47) ltac:(lia) ltac:(lia)).
rewrite zcanon_id; [lia|]. unfold M64, SHADOW_OFF. lia.
Qed.
(* the complement expression of atom n + k *)
Lemma mf_denot_not : forall E (n : nat) x k, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + k < 2 ^ 64 ->
sv_denot E (mf_notx n k) = Z_to_bv 64 (2 ^ 64 - 1 - (x + k)).
Proof.
intros E n x k Hn Hx Hxk. rewrite denot_lit_U. f_equal. unfold mf_notx.
rewrite U_SAlu, U_SLit, U_SOff, Hn. rewrite (unsigned_lit_small x) by lia.
rewrite (zcanon_id (x + k)) by (unfold M64; lia).
replace (zcanon (-1)) with (2 ^ 64 - 1) by reflexivity.
cbn [zalu_raw]. apply zcanon_id. unfold M64. lia.
Qed.

(* the seed: the symbolic state at any listing offset pc after the frame call *)
Lemma mf_seed : forall v lyc Sc Wc regs1 memc mdc pos lowsh mcc cur np xs pc cells hnp slx hw lw lowcs shw,
mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> mf_regs_base v regs1 ->
(cells = true -> mf_cells v lyc pos memc Wc cur) -> 0 <= mf_cur_ptr (mv_c v) cur < 2 ^ 64 ->
(hnp = true -> mf_np v memc Wc np) -> 0 <= np < 2 ^ 64 -> 0 <= lowsh < 256 ->
Forall (YP09.chunk_ok SEGS (mfE regs1 v lyc pos cur np xs) (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v))) slx ->
Forall (YP09.chunk_ok SEGS (mfE regs1 v lyc pos cur np xs) (mrestrict (w_H Wc) memc) (frame_addr lyc 1 pos)) lowcs ->
regions_wf (mf_regions cells hnp slx hw lw lowcs shw lowsh) = true ->
st_ok_pi SEGS VAL (mfE regs1 v lyc pos cur np xs) (ss_mf pc cells hnp slx hw lw lowcs shw lowsh)
(restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros v lyc Sc Wc regs1 memc mdc pos lowsh mcc cur np xs pc cells hnp slx hw lw lowcs shw
  CX CORE RB HCELLS Hcur HNP Hnp Hlow FSLX FLOW HWF.
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _ & _ & _ & _ & HMP & _).
pose proof HMP as (Hc0 & Hc16 & _ & Hheap & _).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof CORE as (HJ & HPerm & VFL & VSH & VSV & V120 & _ & _ & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof RB as (R2 & R8 & R9 & R18).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity).
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HFal & _ & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HF4096 & HFceil & HFapp).
destruct (al_flag _ _ LAWS _ _ _ _ _ 1 pos HAR Hfin) as (_ & _ & HFLapp & HFLc).
destruct Hheap as (bb & bm & Hbin & Hb1 & Hb2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb bm HAR0 Hbin) as (_ & Hb4096 & Hbceil & Hbapp & _ & _ & Hbm).
pose proof (req_size_pos bm ltac:(lia)) as [_ Hreq].
change (fs_frame_bytes 1) with 128 in *. unfold in_app in HFLapp, HFapp, Hbapp.
set (sp0 := mv_sp v) in *. set (F := frame_addr lyc 1 pos) in *. set (FL := flag_addr lyc 1 pos) in *.
set (c := mv_c v) in *. set (s1 := mf_s1 sp0) in *.
unfold mv_sp in sp0. fold sp0 in Hstk, Hal16, Hslo, Hshi, Hbot, Htop, Hpres0, Hch.
rewrite HSTK in Hslo, Hpres, Hbot.
assert (Hs1 : s1 = sp0 - 320 - sp0 mod 32 /\ (sp0 mod 32 = 0 \/ sp0 mod 32 = 16)).
{ unfold s1, mf_s1. replace ((sp0 - 320) mod 32) with (sp0 mod 32)
    by (rewrite Zminus_mod; change (320 mod 32) with 0; rewrite Z.sub_0_r, Z.mod_mod by lia; reflexivity).
  split; [reflexivity|]. pose proof (Z.mod_pos_bound sp0 32 ltac:(lia)).
  pose proof (Z.div_mod sp0 32 ltac:(lia)). pose proof (Z.div_mod sp0 16 ltac:(lia)). lia. }
rewrite restrict_mkst_fx.
set (E := mfE regs1 v lyc pos cur np xs).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros; apply mfE_reg; assumption).
assert (EX : forall j, (32 + j < A_TEXT)%nat -> ew E (32 + j) = nth j (mf_extra v lyc pos cur np xs) (Z_to_bv 64 0))
  by (intros; apply mfE_extra; assumption).
pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (EX 1%nat ltac:(unfold A_TEXT; lia)) as E33.
pose proof (EX 2%nat ltac:(unfold A_TEXT; lia)) as E34. pose proof (EX 3%nat ltac:(unfold A_TEXT; lia)) as E35.
pose proof (EX 4%nat ltac:(unfold A_TEXT; lia)) as E36. pose proof (EX 5%nat ltac:(unfold A_TEXT; lia)) as E37.
pose proof (EX 6%nat ltac:(unfold A_TEXT; lia)) as E38.
cbn [Nat.add nth mf_extra map app] in E32, E33, E34, E35, E36, E37, E38.
fold c F FL in E33, E34, E35, E36, E37.
assert (EW : ew E (A_OBJ MF_WORDS_OBJ) = Z_to_bv 64 SegInstB.wordsA).
{ unfold E. rewrite mfE_img by (unfold A_OBJ, MF_WORDS_OBJ, A_TEXT, A_LIM; lia). rewrite mf_words_obj. reflexivity. }
assert (HWv : SegInstB.wordsA = 0xa2040) by reflexivity.
assert (E2 : ew E 2 = getr regs1 2) by (apply EE; reflexivity).
assert (E8 : ew E 8 = getr regs1 8) by (apply EE; reflexivity).
assert (Hsp64 : 0 <= sp0 < 2 ^ 64) by lia.
assert (U2 : bv_unsigned (ew E 2) = s1) by (rewrite E2, R2; unfold w64; apply unsigned_lit_small; destruct Hs1 as [Hs1a Hs1b]; rewrite Hs1a; lia).
assert (U8 : bv_unsigned (ew E 8) = sp0) by (rewrite E8, R8; unfold w64; apply unsigned_lit_small; lia).
assert (VB : forall k z, ew E k = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> base_val E (Some k) = z).
{ intros k z Hk Hz. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hz. }
assert (B2 : base_val E (Some 2%nat) = s1) by (cbn [base_val]; exact U2).
assert (B8 : base_val E (Some 8%nat) = sp0) by (cbn [base_val]; exact U8).
assert (HF8 : 512 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
assert (HSB : SHADOW_OFF = 0x7fff8000) by reflexivity.
assert (B34 : base_val E (Some 34%nat) = F) by (apply VB; [exact E34 | lia]).
assert (B36 : base_val E (Some 36%nat) = SHADOW_OFF + F / 8) by (apply VB; [exact E36 | rewrite HSB; lia]).
assert (Hc4096 : 4096 <= c) by lia.
assert (Hchi : c + seg_spec.SEG_M_SIZE <= alloc_ceiling) by lia.
unfold seg_spec.SEG_M_SIZE in Hchi.
assert (Hwr : forall o, sp0 - 8592 <= o < sp0 -> writable_at SEGS (mrestrict (w_H Wc) memc) o)
  by (intros o Ho; apply (apresent_writable SEGS); apply Hpres; exact Ho).
unfold ss_mf. apply pa_entry_st_ok_full.
- apply mf_regs_ok. exact RB.
- exact HWF.
- unfold mf_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok.
  + (* the saved registers *)
    unfold mf_r_saved. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B8.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil;
    lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
    let j := eval compute in (n - 39)%nat in let r := eval compute in (nth j mf_saved_regs 0) in
    apply (chunk_ok_val SEGS E _ sp0 off 8 (SOff n 0) (bv_unsigned (ew E n)));
    [ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | let HR := fresh in pose proof (bv_unsigned_in_range 64 (ew E n)) as HR; clear - HR; change (bv_modulus 64) with (2 ^ 64) in HR; exact HR
    | cbn; lia
    | replace (sp0 + off) with (sp0 - 8 - 8 * Z.of_nat j) by (cbn; lia);
      let k := eval compute in (n - 32)%nat in change (ew E n) with (ew E (32 + k)); rewrite (EX k ltac:(unfold A_TEXT; lia));
      cbn [Nat.sub nth mf_extra map app mf_saved_regs];
      exact (VSV j r eq_refl) ] end.
  + (* the frame cells *)
    unfold mf_r_slots. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B2.
    destruct Hs1 as [Hs1a Hs1b].
    split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hwr; lia|].
    apply Forall_cons.
    { unfold mf_chunk120. apply (mf_chunk_atom E _ s1 120 34 0 F E34); [lia | lia | rewrite Z.add_0_r; exact V120]. }
    apply Forall_app. split.
    { destruct cells; [|apply Forall_nil].
      destruct (HCELLS eq_refl) as (C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & C88 & C96 & C104 & C112 &
        C128 & C136 & C144).
      fold sp0 s1 c F in C16, C24, C32, C40, C48, C56, C64, C72, C80, C88, C96, C104, C112, C128, C136, C144.
      unfold mf_cell_chunks. unfold seg_spec.MC_KNOCK, seg_spec.MC_OVERFLOW, seg_spec.MC_NKEPT, seg_spec.MC_GEN,
        seg_spec.MC_READING, seg_spec.MC_N in *.
      repeat apply Forall_cons; try apply Forall_nil.
      - apply (chunk_ok_val SEGS E _ s1 16 8 (mf_notx 33 0) (2 ^ 64 - 1 - c));
          [ rewrite (mf_denot_not E 33 c 0 E33) by lia; rewrite Z.add_0_r; reflexivity | cbn; lia | cbn; lia | exact C16 ].
      - apply (mf_chunk_atom E _ s1 24 33 _ c E33); [lia | lia | exact C24].
      - apply (mf_chunk_atom E _ s1 32 33 _ c E33); [lia | lia | exact C32].
      - apply (chunk_ok_val SEGS E _ s1 40 8 (mf_notx 33 0x238c) (2 ^ 64 - 1 - (c + 0x238c)));
          [ apply mf_denot_not; [exact E33 | lia | lia] | cbn; lia | cbn; lia | exact C40 ].
      - apply (mf_chunk_atom E _ s1 48 33 _ c E33); [lia | lia | exact C48].
      - apply (mf_chunk_atom E _ s1 56 33 _ c E33); [lia | lia | exact C56].
      - apply (mf_chunk_atom E _ s1 64 33 _ c E33); [lia | lia | exact C64].
      - apply (chunk_ok_val SEGS E _ s1 72 8 (mf_shx (A_OBJ MF_WORDS_OBJ) 0) (SHADOW_OFF + SegInstB.wordsA / 8));
          [ replace (SHADOW_OFF + SegInstB.wordsA / 8) with (SHADOW_OFF + (SegInstB.wordsA + 0) / 8) by (rewrite Z.add_0_r; reflexivity);
            apply mf_denot_shx; [exact EW | exact E32 | rewrite HWv; lia | lia | rewrite HWv; lia]
          | rewrite HSB, HWv; vm_compute; split; [discriminate | reflexivity] | cbn; lia | exact C72 ].
      - apply (mf_chunk_atom E _ s1 80 (A_OBJ MF_WORDS_OBJ) 0 SegInstB.wordsA EW); [rewrite HWv; lia | rewrite HWv; lia | rewrite Z.add_0_r; exact C80].
      - apply (mf_chunk_atom E _ s1 88 36 0 (SHADOW_OFF + F / 8) E36); [rewrite HSB; lia | rewrite HSB; lia | rewrite Z.add_0_r; exact C88].
      - apply (mf_chunk_atom E _ s1 96 34 0 F E34); [lia | lia | rewrite Z.add_0_r; exact C96].
      - apply (chunk_ok_val SEGS E _ s1 104 8 (mf_shx 33 0x23b0) (SHADOW_OFF + (c + 0x23b0) / 8));
          [ apply mf_denot_shx; [exact E33 | exact E32 | lia | lia | lia]
          | pose proof (Z.div_pos (c + 0x23b0) 8 ltac:(lia) ltac:(lia)); pose proof (Z.div_le_upper_bound (c + 0x23b0) 8 (2 ^ 47) ltac:(lia) ltac:(lia)); rewrite HSB; cbn; lia
          | cbn; lia | exact C104 ].
      - apply (mf_chunk_atom E _ s1 112 33 0 c E33); [lia | lia | rewrite Z.add_0_r; exact C112].
      - apply (mf_chunk_atom E _ s1 128 33 _ c E33); [lia | lia | exact C128].
      - apply (mf_chunk_atom E _ s1 136 37 0 (mf_cur_ptr c cur) E37); [lia | lia | rewrite Z.add_0_r; exact C136].
      - apply (mf_chunk_atom E _ s1 144 34 32 F E34); [lia | lia | exact C144]. }
    apply Forall_app. split; [|exact FSLX].
    destruct hnp; [|apply Forall_nil]. apply Forall_cons; [|apply Forall_nil].
    unfold mf_chunk152. apply (mf_chunk_atom E _ s1 152 38 0 np E38); [lia | lia | rewrite Z.add_0_r; exact (HNP eq_refl)].
  + (* the frame header *)
    unfold mf_r_fh. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B34.
    split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. destruct hw; [|lia]. apply (apresent_writable SEGS). apply (proj1 (HFpres (F + o) ltac:(lia))).
  + (* low.i *)
    unfold mf_r_low. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B34.
    split; [lia|]. split; [lia|]. split; [|exact FLOW].
    intros o Ho. destruct lw; [|lia]. apply (apresent_writable SEGS). apply (proj1 (HFpres (F + o) ltac:(lia))).
  + (* the frame tail with the flag pointer *)
    unfold mf_r_ft. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B34.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (mf_chunk_atom E _ F 120 35 0 FL E35); [lia | lia | rewrite Z.add_0_r; exact VFL].
  + (* the frame's shadow *)
    unfold mf_r_fs. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B36.
    split; [rewrite HSB; lia|]. split; [rewrite HSB; lia|]. split.
    { intros o Ho. destruct shw; [|lia]. apply (apresent_writable SEGS).
      unfold shadow_addr in HFSpres. apply (proj1 (HFSpres o ltac:(change (128 / 8) with 16; lia))). }
    cbn [seq map Z.of_nat Z.add].
    repeat apply Forall_cons; try apply Forall_nil;
    lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 1 (SLit lowsh))) =>
    apply (chunk_ok_val SEGS E _ (SHADOW_OFF + F / 8) off 1 (SLit lowsh) lowsh);
    [ reflexivity | cbn; lia | cbn; lia | apply VSH; lia ] end.
- apply pairwise_disjoint_of_extents. unfold mf_regions, mf_r_saved, mf_r_slots, mf_r_fh, mf_r_low, mf_r_ft, mf_r_fs,
    extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite B2, B8, B34, B36.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  destruct Hs1 as [Hs1a Hs1b].
  unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. rewrite HSB.
  pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.mod_pos_bound F 8 ltac:(lia)).
  repeat split; lia.
- split; [|split; exact I].
  cbn [mf_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
  assert (HFm : F mod 32 = 0) by exact HFal.
  assert (HF8m : (F / 8) mod 4 = 0).
  { pose proof (Z.div_mod F 32 ltac:(lia)). replace F with ((F / 32) * 4 * 8) at 1 by lia.
    rewrite Z.div_mul by lia. rewrite Z.mod_mul by lia. reflexivity. }
  rewrite U2, U8.
  rewrite E32, E33, E34, E35, E36.
  rewrite (unsigned_lit_small SHADOW_OFF) by (rewrite HSB; lia). rewrite (unsigned_lit_small c) by lia.
  rewrite (unsigned_lit_small F) by lia. rewrite (unsigned_lit_small FL) by lia.
  rewrite (unsigned_lit_small (SHADOW_OFF + F / 8)) by (rewrite HSB; lia).
  destruct Hs1 as [Hs1a Hs1b].
  change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
  rewrite HSB in *.
  repeat match goal with |- _ /\ _ => split end; try lia; try reflexivity.
  all: try (rewrite Hs1a; replace (sp0 - 320 - sp0 mod 32) with ((sp0 / 32 - 10) * 32) by (pose proof (Z.div_mod sp0 32 ltac:(lia)); lia); apply Z_mod_mult).
  all: try (replace (2147450880 + F / 8) with ((536862720 + F / 32) * 4) by (pose proof (Z.div_mod F 32 ltac:(lia)); pose proof (Z.div_mod F 8 ltac:(lia)); pose proof (Z.mod_pos_bound F 8 ltac:(lia)); lia); apply Z_mod_mult).
Qed.

(* the shadow base is atom 32 *)
Lemma mfE_U32 : forall regs1 v lyc pos cur np xs, U (mfE regs1 v lyc pos cur np xs) (SOff 32 0) = SHADOW_OFF.
Proof.
intros. pose proof (mfE_extra regs1 v lyc pos cur np xs 0 ltac:(unfold A_TEXT; lia)) as E32.
cbn [Nat.add nth mf_extra map app] in E32. apply (U_atom _ 32 SHADOW_OFF E32). unfold SHADOW_OFF. lia.
Qed.
(* a shadow entry at any atom n holding p, from the range's addressability *)
Lemma mf_she_at : forall E (Wc : world SEGS) (memc : word -> option byte) (n : nat) p len,
U E (SOff 32 0) = SHADOW_OFF -> ew E n = Z_to_bv 64 p -> 0 <= p < 2 ^ 64 -> 0 <= len ->
range_addressable (rdW Wc memc) SHADOW_OFF p len ->
(forall x, p <= x < p + len -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)) ->
shent_ok SEGS (SOff 32 0) E (mrestrict (w_H Wc) memc) (mkSHE n 0 len).
Proof.
intros E Wc memc n p len HB Hn Hp Hlen HRA Happ.
apply (shent_ok_of_range SEGS (w_H Wc) memc E (SOff 32 0) n p len p 0 len HRA HB (U_atom E n p Hn Hp)); [lia | lia |].
intros y Hy. apply Happ. rewrite Z.min_l, Z.max_r in Hy by lia. lia.
Qed.
(* the bytes of the mconf block lie outside the shadow span *)
Lemma mf_blk_app : forall v, mf_cx B v ->
forall x, mv_c v <= x < mv_c v + seg_spec.SEG_M_SIZE -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416).
Proof.
intros v CX x Hx.
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMP & _).
pose proof HMP as (_ & _ & _ & Hheap & _). pose proof HPRE as (HAR0 & _).
destruct Hheap as (bb & bm & Hbin & Hb1 & Hb2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb bm HAR0 Hbin) as (_ & Hb4096 & Hbceil & Hbapp & _ & _ & Hbm).
pose proof (req_size_pos bm ltac:(lia)) as [_ Hreq].
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF, seg_spec.SEG_M_SIZE in *. lia.
Qed.
(* the bytes of the text left lie in the text's block, outside the shadow span *)
Lemma mf_txt_blk : forall v Wc memc mcc cur line p rest, mf_cx B v -> mf_loop v Wc memc mcc cur line p rest ->
exists bb bm, In (bb, bm) (ablocks B (mv_ly v) (mv_S v)) /\ bb <= p /\ p + Z.of_nat (length rest) + 1 <= bb + bm.
Proof.
intros v Wc memc mcc cur line p rest CX LP.
pose proof CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ht64 & _ & _ & HMP & _).
pose proof HMP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ht0 & _ & Hlen & Htheap & _).
pose proof LP as (Hlr & _ & Hp & _).
destruct Htheap as (bb & bm & Hbin & Hb1 & Hb2).
exists bb, bm. split; [exact Hbin|]. rewrite Hp. lia.
Qed.
Lemma mf_txt_app : forall v Wc memc mcc cur line p rest, mf_cx B v -> mf_loop v Wc memc mcc cur line p rest ->
forall x, p <= x < p + Z.of_nat (length rest) + 1 -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416).
Proof.
intros v Wc memc mcc cur line p rest CX LP x Hx.
destruct (mf_txt_blk v Wc memc mcc cur line p rest CX LP) as (bb & bm & Hbin & Hb1 & Hb2).
pose proof CX as (HPRE & _). pose proof HPRE as (HAR0 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb bm HAR0 Hbin) as (_ & Hb4096 & Hbceil & Hbapp & _ & _ & Hbm).
pose proof (req_size_pos bm ltac:(lia)) as [_ Hreq].
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.

(* the shadow entry of the mconf block (atom 33), [c, c + hi) for hi <= 9236 *)
Lemma mf_she_blk : forall v lyc Sc Wc regs1 memc mdc pos lowsh mcc cur np xs hi,
mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> 0 <= hi <= seg_spec.SEG_M_SIZE ->
shent_ok SEGS (SOff 32 0) (mfE regs1 v lyc pos cur np xs) (mrestrict (w_H Wc) memc) (mkSHE 33 0 hi).
Proof.
intros v lyc Sc Wc regs1 memc mdc pos lowsh mcc cur np xs hi CX CORE Hhi.
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _).
pose proof CORE as (_ & _ & _ & _ & _ & _ & _ & HADDR & _).
pose proof HADDR as (_ & _ & _ & HRA & _).
set (E := mfE regs1 v lyc pos cur np xs).
pose proof (mfE_extra regs1 v lyc pos cur np xs 1 ltac:(unfold A_TEXT; lia)) as E33.
cbn [Nat.add nth mf_extra map app] in E33. fold E in E33.
apply (shent_ok_of_range SEGS (w_H Wc) memc E (SOff 32 0) 33 (mv_c v) seg_spec.SEG_M_SIZE (mv_c v) 0 hi).
- exact HRA.
- apply mfE_U32.
- apply (U_atom E 33 (mv_c v) E33). lia.
- lia.
- lia.
- intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. apply (mf_blk_app v CX). lia.
Qed.

(* a read-only region of n bytes of the text left at atom r, which holds x (mf_seed_txt): its region_ok, its
   disjointness from the seed's six regions, and the fact the token engine asks of the cursor atom *)
Lemma mf_txt_region : forall v lyc Sc Wc regs1 memc mdc pos lowsh mcc cur np xs (r : nat) x n cs line p rest
  cells hnp slx hw lw lowcs shw,
mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> mf_regs_base v regs1 ->
mf_loop v Wc memc mcc cur line p rest ->
ew (mfE regs1 v lyc pos cur np xs) r = Z_to_bv 64 x -> p <= x -> 0 <= n -> x + n <= p + Z.of_nat (length rest) + 1 ->
Forall (YP09.chunk_ok SEGS (mfE regs1 v lyc pos cur np xs) (mrestrict (w_H Wc) memc) x) cs ->
region_ok SEGS (mfE regs1 v lyc pos cur np xs) (mrestrict (w_H Wc) memc) (YP09.mkRegion (Some r) 0 n 0 0 cs) /\
all_disjoint (mfE regs1 v lyc pos cur np xs) (YP09.mkRegion (Some r) 0 n 0 0 cs)
  (mf_regions cells hnp slx hw lw lowcs shw lowsh) /\
afact_ok (mfE regs1 v lyc pos cur np xs) r (mkAF 4096 (2 ^ 47 - 8) 0).
Proof.
intros v lyc Sc Wc regs1 memc mdc pos lowsh mcc cur np xs r x n cs line p rest cells hnp slx hw lw lowcs shw
  CX CORE RB LP Hr Hpx Hn Hxn FCS.
destruct (mf_txt_blk v Wc memc mcc cur line p rest CX LP) as (bb & bm & Hbin & Hb1 & Hb2).
pose proof CX as (HPRE & _). pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof CORE as (HJ & HPerm & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof RB as (R2 & R8 & R9 & R18).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in Hslo.
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb bm HAR0 Hbin) as (_ & Hb4096 & Hbceil & Hbapp & _ & _ & Hbm).
pose proof (req_size_pos bm ltac:(lia)) as [_ Hreq].
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
assert (Hbin2 : In (bb, bm) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HPerm)); exact Hbin).
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc bb bm 1 pos HAR Hbin2 Hfin) as Hsep.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HF4096 & HFceil & HFapp).
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
change (fs_frame_bytes 1) with 128 in *. unfold in_app in Hbapp, HFapp.
set (sp0 := mv_sp v) in *. set (F := frame_addr lyc 1 pos) in *.
unfold mv_sp in sp0. fold sp0 in Hstk, Hal16, Hslo, Hshi.
set (E := mfE regs1 v lyc pos cur np xs) in *.
assert (Hx64 : 0 <= x < 2 ^ 64) by lia.
assert (Br : base_val E (Some r) = x) by (cbn [base_val]; rewrite Hr; apply unsigned_lit_small; exact Hx64).
pose proof (mfE_extra regs1 v lyc pos cur np xs 2 ltac:(unfold A_TEXT; lia)) as E34.
pose proof (mfE_extra regs1 v lyc pos cur np xs 4 ltac:(unfold A_TEXT; lia)) as E36.
cbn [Nat.add nth mf_extra map app] in E34, E36. fold E F in E34, E36.
assert (HF8 : 512 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
assert (HSB : SHADOW_OFF = 0x7fff8000) by reflexivity.
assert (B2 : base_val E (Some 2%nat) = mf_s1 sp0).
{ cbn [base_val]. unfold E. rewrite (mfE_reg regs1 v lyc pos cur np xs 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small.
  unfold mf_s1. pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)). lia. }
assert (B8 : base_val E (Some 8%nat) = sp0).
{ cbn [base_val]. unfold E. rewrite (mfE_reg regs1 v lyc pos cur np xs 8 8%bv eq_refl), R8. unfold w64. apply unsigned_lit_small. lia. }
assert (B34 : base_val E (Some 34%nat) = F) by (cbn [base_val]; rewrite E34; apply unsigned_lit_small; lia).
assert (B36 : base_val E (Some 36%nat) = SHADOW_OFF + F / 8)
  by (cbn [base_val]; rewrite E36; apply unsigned_lit_small; rewrite HSB; lia).
assert (Hs1 : sp0 - 336 <= mf_s1 sp0 <= sp0 - 320).
{ unfold mf_s1. pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)).
  replace ((sp0 - 320) mod 32) with (sp0 mod 32)
    by (rewrite Zminus_mod; change (320 mod 32) with 0; rewrite Z.sub_0_r, Z.mod_mod by lia; reflexivity).
  pose proof (Z.div_mod sp0 32 ltac:(lia)). pose proof (Z.div_mod sp0 16 ltac:(lia)). pose proof (Z.mod_pos_bound sp0 32 ltac:(lia)).
  lia. }
split; [|split].
- unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite Br.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia | exact FCS].
- apply all_disjoint_of_extents. unfold mf_regions, mf_r_saved, mf_r_slots, mf_r_fh, mf_r_low, mf_r_ft, mf_r_fs,
    extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite Br, B2, B8, B34, B36.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. rewrite HSB.
  pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.mod_pos_bound F 8 ltac:(lia)).
  repeat split; lia.
- unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Hr, unsigned_lit_small by exact Hx64.
  rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.

(* the text's block is live at the current state *)
Lemma mf_txt_heap_now : forall v lyc Sc Wc memc mdc pos lowsh mcc,
mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
sa_heap B lyc Sc (mv_t v) (Z.of_nat (length (mv_s v)) + 1).
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc CX CORE.
pose proof CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMP & _).
pose proof HMP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htheap & _).
pose proof CORE as (_ & HPerm & _).
destruct Htheap as (bb & bm & Hbin & Hb1 & Hb2).
exists bb, bm. split; [apply (Permutation_in _ (Permutation_sym HPerm)); exact Hbin | lia].
Qed.
(* every byte of a live block lies below every callee window under s1 (callees run at sp = s1 and ask at most
   2 * ESTACK below it; m_file's STK is 8,592) *)
Lemma mf_heap_below_stack : forall v lyc Sc Wc memc mdc pos lowsh mcc q n,
mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> sa_heap B lyc Sc q n ->
forall a, q <= a < q + n -> a < mf_s1 (mv_sp v) - 2 * YG0d.ESTACK.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc q n CX CORE Hh a Ha.
pose proof CX as (HPRE & _). pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & _).
pose proof CORE as (HJ & _). pose proof HJ as (HAR & _).
destruct Hh as (bb & bm & Hbin & Hb1 & Hb2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb bm HAR Hbin) as (_ & Hb4096 & Hbceil & _ & _ & _ & Hbm).
pose proof (req_size_pos bm ltac:(lia)) as [_ Hreq].
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in Hslo.
unfold mf_s1. set (sp0 := mv_sp v) in *. unfold mv_sp in sp0. fold sp0 in Hslo, Hal16.
pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)). unfold YG0d.ESTACK.
(* a < b + |b| <= alloc_ceiling <= the entry layout's stack bottom <= sp0 - 8592 < s1 - 8192 *)
lia.
Qed.

(* ===================== what the strip and fold call sites need of the frame (image B) ===================== *)
(* every byte of the thread stack's band has shadow 0 at an AR state (ARm's am_zshadow, lib/B/YG0n.v:193-196) *)
Lemma mf_stk_sh0 : forall lyc Sc (Wc : world SEGS) memc mdc x, AR SEGS B lyc Sc Wc memc mdc ->
ly_stk_lo lyc <= x < ly_stk_hi lyc -> rdW Wc memc (SHADOW_OFF + x / 8) = Some 0.
Proof.
intros lyc Sc Wc memc mdc x HAR Hx.
destruct HAR as (HM & _).
pose proof HM as HZ. apply am_zshadow in HZ. pose proof HM as LO. apply am_layout in LO.
pose proof LO as LT. apply lo_top in LT. destruct LT as (_ & _ & _ & _ & Hplo & Hphi & _).
unfold zshadow_ok, zero_shadow_ranges in HZ. apply Forall_inv in HZ. cbn [fst snd] in HZ.
unfold page_aligned in Hplo, Hphi. unfold zero_shadow, shadow_of_addr in HZ.
set (lo := ly_stk_lo lyc) in *. set (hi := ly_stk_hi lyc) in *.
assert (Hlo8 : lo mod 8 = 0).
{ replace lo with ((lo / 4096) * 512 * 8) by (pose proof (Z.div_mod lo 4096 ltac:(lia)); lia). apply Z.mod_mul. lia. }
assert (Hhi8 : hi mod 8 = 0).
{ replace hi with ((hi / 4096) * 512 * 8) by (pose proof (Z.div_mod hi 4096 ltac:(lia)); lia). apply Z.mod_mul. lia. }
pose proof (Z.div_mod lo 8 ltac:(lia)). pose proof (Z.div_mod hi 8 ltac:(lia)).
pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + lo / 8 + (x / 8 - lo / 8)) by lia.
apply HZ.
replace (hi - lo) with ((hi / 8 - lo / 8) * 8) by lia. rewrite Z.div_mul by lia.
lia.
Qed.

(* an 8-byte frame cell off(s1), 16 <= off <= 208: addressable (strip_args' sa_addr of a cell), present and at or
   above s1, the sp every callee runs at (strip_slot); s1 is 32-aligned, so off mod 8 = 0 makes the cell 8-aligned *)
Lemma mf_slot_addr : forall v lyc Sc Wc memc mdc pos lowsh mcc off,
mf_cx B v -> mf_ls v lyc Sc -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> 16 <= off -> off + 8 <= 216 ->
sa_addr (rdW Wc memc) (mf_s1 (mv_sp v) + off) 8 /\
(forall i, 0 <= i < 8 -> apresent (w_H Wc) memc (mf_s1 (mv_sp v) + off + i)) /\
mf_s1 (mv_sp v) <= mf_s1 (mv_sp v) + off /\ (mf_s1 (mv_sp v)) mod 32 = 0.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc off CX LS CORE Hoff1 Hoff2.
pose proof CX as (HPRE & _). pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof CORE as (HJ & _). pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
destruct LS as (Hly & _). subst lyc.
pose proof HAR as (HM & _). pose proof HM as LO. apply am_layout in LO.
pose proof LO as LT. apply lo_top in LT. destruct LT as (_ & _ & _ & HhiE & _ & _ & HloB).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in Hslo, Hpres.
set (sp0 := mv_sp v) in *. unfold mv_sp in sp0. fold sp0 in Hslo, Hal16, Hshi.
assert (Hs1 : sp0 - 336 <= mf_s1 sp0 <= sp0 - 320 /\ (mf_s1 sp0) mod 32 = 0).
{ unfold mf_s1. pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)).
  replace ((sp0 - 320) mod 32) with (sp0 mod 32)
    by (rewrite Zminus_mod; change (320 mod 32) with 0; rewrite Z.sub_0_r, Z.mod_mod by lia; reflexivity).
  pose proof (Z.div_mod sp0 32 ltac:(lia)). pose proof (Z.div_mod sp0 16 ltac:(lia)). pose proof (Z.mod_pos_bound sp0 32 ltac:(lia)).
  split; [lia|].
  replace (sp0 - 320 - sp0 mod 32) with ((sp0 / 32 - 10) * 32) by lia. apply Z_mod_mult. }
destruct Hs1 as [Hs1 Hs1m].
unfold kHighMemBeg, kHighMemEnd in *.
split; [|split; [|split; [lia | exact Hs1m]]].
- unfold sa_addr. split; [lia|]. split; [lia|]. split.
  { unfold amem_range. right. unfold kHighMemBeg, kHighMemEnd. lia. }
  split.
  { intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
    apply (mf_stk_sh0 (mv_ly v) Sc Wc memc mdc x HAR). lia. }
  intros _ s Hs. unfold shadow_addr in Hs.
  assert (HSB : SHADOW_OFF = 8 * 268431360) by reflexivity.
  (* s is the shadow byte of the address 8 * (s - SHADOW_OFF), which lies in the band *)
  replace s with (SHADOW_OFF + (8 * (s - SHADOW_OFF)) / 8)
    by (rewrite (Z.mul_comm 8), Z.div_mul by lia; lia).
  rewrite (mf_stk_sh0 (mv_ly v) Sc Wc memc mdc (8 * (s - SHADOW_OFF)) HAR); [discriminate|].
  rewrite HSB in Hs |- *. clear - Hs Hslo Hshi Hs1 Hoff1 Hoff2.
  Z.div_mod_to_equations. lia.
- intros i Hi. apply Hpres. lia.
Qed.

(* low.i's first k <= 64 bytes, at FB + 32, when its shadow bytes are 0 (the K cuts): addressable and inside the
   live side-stack frame (1, pos), fold_pre's sa_fframe and fold_args' range_addressable of out *)
Lemma mf_low_addr : forall v lyc Sc Wc memc mdc pos mcc k,
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> 0 <= k <= 64 ->
range_addressable (rdW Wc memc) SHADOW_OFF (frame_addr lyc 1 pos + 32) k /\
sa_fframe lyc Sc (frame_addr lyc 1 pos + 32) k.
Proof.
intros v lyc Sc Wc memc mdc pos mcc k CORE Hk.
pose proof CORE as (HJ & _ & _ & VSH & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HFal & _ & _ & _).
set (F := frame_addr lyc 1 pos) in *. unfold MF_LOW_ON in VSH.
assert (HFm : F mod 32 = 0) by exact HFal.
split.
- intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
  replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + F / 8 + (x / 8 - F / 8)) by lia.
  apply (aview_of_val_mem1 SEGS); [|lia]. apply VSH.
  clear - Hx Hk HFm. Z.div_mod_to_equations. lia.
- exists 1, pos. split; [exact Hfin|]. split; [lia|]. change (fs_frame_bytes 1) with 128. lia.
Qed.
End e.
End f.
End d.
