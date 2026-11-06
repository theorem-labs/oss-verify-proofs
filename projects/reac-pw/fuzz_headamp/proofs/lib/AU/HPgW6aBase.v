(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aBase.v at 80bf14ccf11
   (its block-statement shape: one statement per block of the piece, each in the shape of a callee
   contract, so the blocks are proved independently and the piece is their chaining) for reac-pw/fuzz_headamp's
   image B: the rs_ prefix renamed to w6b_, every pc, register and real-frame cell measured on image B's own twin,
   the block context and post taken from lib/AU/HPgCaseB.v instead of restated, the frame object the dispatch fills
   is e62 at F+0x210 (image A's single e at F+0xf0), pod_write_ent is out of line so the piece ends at the join J
   before its call, and case 3's two even arms are brought to one exit pc. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded sections are byte-equal to the
   pin's except .note.gnu.build-id): the BLOCK STATEMENTS of the walk piece W6a of LLVMFuzzerTestOneInput (0x80c40) -- the pod loop's head C
   (0x81888) through ent_build's dispatch (pod.h:279-281), and ent_build's cases 2 and 3 (pod.h:298-324) to the
   join J (0x82618, where the out-of-line pod_write_ent call begins). Statement text only: proves no function
   (kind: segment lemma).

   WHY BLOCKS. The piece is cut where the code calls something (the __asan_memset of e62 at 0x818cc, the fuzz_u32
   read-ahead blocks hdu_u32_block2 / hdu_u32_block3 of lib/AU/HPgSteps.v, the jump-table block hdu_jt_block of the
   same file) and at the first store of the cases' common tail. Each block is stated over the machine state it
   starts from (its registers, the 8-byte real-frame cells it reads, the input bytes) in the shape of a callee
   contract, so that the blocks are proved independently and the piece lemmas of lib/AU/HPgSeg.v
   (hsu_piece_W6a_disp_stmt, hsu_piece_W6a_cases_stmt) are their chaining with SRr_bind:

     w6b_head   C 0x81888 .. 0x818cc + the memset call, back at 0x818d0: [R+0x158] := k (the pod index),
                e62's 13 shadow granules [66, 79) := 0, e62 := 0^104, a0 = F + 0x210.
     w6b_kind   0x818d0 .. the case entry: no input left goes to D0E 0x819c0; else the kind byte is read
                (its shadow check's slow block 0x82770), kind mod 10 is formed (0xcd multiply, 0x81904 .. 0x81918),
                case 9 is taken by `bltu a2,a1` 0x81924 to 0x82004, cases 0 .. 8 through hdu_jt_block 0x81928.
     w6b_c2     case 2's entry 0x81cbc: m = fuzz_u8; m odd stops at 0x82390 (hdu_u32_block2's entry, with its
                premises); m even (or no byte left) loads ints[(m >> 1) % 14] and stops at 0x82578.
     w6b_c3     case 3's entry 0x81d34: m odd stops at 0x823cc (hdu_u32_block3's entry); m = 0xfe gives the NaN
                literal and m = 0xfc the infinity literal (0x8249c / 0x81d80), else floats[(m >> 1) % 21]; every
                even arm stops at 0x825fc.
     w6b_tail2  0x82574 / 0x82578 .. J 0x82618: e62.type := 4, e62.size := 4, e62.body[0..4) := the value,
                t1 := what is left, a3 := the cursor, s2 := [R+0x138] = &pp->len.
     w6b_tail3  0x825f8 / 0x825fc .. J 0x82618: the same with e62.type := 6.

   THE REGISTERS AND CELLS (image B, measured; a port to another image-B unit rewrites exactly this list).
   s0 = x8 = S, s1 = x9 = R (the real frame's 32-aligned base), s3 = x19 = shadow_addr F, s11 = x27 = SHADOW_OFF,
   s5 = x21 = the input cursor at the pod loop's head, s10 = x26 = what is left there, s4 = x20 = &e62 at the head
   (reused for the kind byte's `left` and reloaded from [R+0x130] at each case entry), s7 = x23 = -8 at the head
   and the first block pp from [R+0x148] inside a case, s2 = x18 = the cursor after the kind byte, a7 = x17 = the
   kind byte's own address, t1 = x6 = what was left before the kind byte, t2 = x7 = 10, a6 = x16 = 1,
   a3 = x13 = the sign-extended kind byte, a2 = x12 = what is left after m, a1 = x11 = the value, a4 = x14 = 4.
   Real-frame cells: [R+0x130] = F + 0x210 (&e62), [R+0x138] = pp + Layout.OFF_LEN, [R+0x148] = pp,
   [R+0x150] = shadow_addr (pp + Layout.OFF_LEN), [R+0x158] = the pod index. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSteps HPgSeg HPgCaseB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================== the pcs ========================================
   Each is read from the image's code; the five that a cut of lib/AU/HPgSeg.v names are the fields of
   headamp_bld_B (w6b_pcs_of_bld below checks that they agree). *)
Definition W6B_C : Z := 0x81888.        (* `sd a1,0x158(s1)`: the pod loop's head (bi_C) *)
Definition W6B_MEMSET : Z := 0x52228.   (* __asan_memset, the `jal` target at 0x818cc *)
Definition W6B_RET : Z := 0x818d0.      (* `beqz s10`, after the memset of e62 *)
Definition W6B_D0E : Z := 0x819c0.      (* case 0 with no input left (`beqz s10` 0x818d0 taken; bi_D0E) *)
Definition W6B_D9 : Z := 0x82004.       (* case 9 (`bltu a2,a1` 0x81924 taken; bi_d9) *)
Definition W6B_D2 : Z := 0x81cbc.       (* case 2's switch entry (the table's entry 2) *)
Definition W6B_D3 : Z := 0x81d34.       (* case 3's switch entry (the table's entry 3) *)
Definition W6B_U2 : Z := 0x82390.       (* case 2's fuzz_u32 block (HPgSteps hdu_u32_block2) .. 0x82574 *)
Definition W6B_U2E : Z := 0x82574.
Definition W6B_U3 : Z := 0x823cc.       (* case 3's fuzz_u32 block (HPgSteps hdu_u32_block3) .. 0x825f8 *)
Definition W6B_U3E : Z := 0x825f8.
Definition W6B_T2 : Z := 0x82578.       (* case 2's tail: `sw a4,0(s4)`, e62.type := 4 *)
Definition W6B_T3 : Z := 0x825fc.       (* case 3's tail: `addi a0,zero,6`, then e62.type := 6 *)
Definition W6B_J : Z := 0x82618.        (* the join: the out-of-line pod_write_ent call begins (bi_J) *)
(* the two tables the cases read (registered globals of .rodata): ints[14] 56 bytes, floats[21] 84 bytes *)
Definition W6B_INTS : Z := 0x21040.
Definition W6B_FLOATS : Z := 0x210a0.

Lemma w6b_pcs_of_bld :
bi_C headamp_bld_B = W6B_C /\ bi_D0E headamp_bld_B = W6B_D0E /\ bi_d9 headamp_bld_B = W6B_D9 /\
bi_J headamp_bld_B = W6B_J /\ nth 2 (bi_dt headamp_bld_B) 0 = W6B_D2 /\ nth 3 (bi_dt headamp_bld_B) 0 = W6B_D3.
Proof. repeat split. Qed.
(* the globals of image B's record hold both tables, so hd_seg_pre gives their shadow bytes *)
Lemma w6b_tables_glob :
In (W6B_INTS, 56) (hi_globs headamp_himg_B) /\ In (W6B_FLOATS, 84) (hi_globs headamp_himg_B).
Proof. split; cbn [hi_globs headamp_himg_B headamp_B_globs In]; repeat (first [left; reflexivity | right]). Qed.

(* ======================================== the code table ========================================
   Every instruction word of [0x81888, 0x828d0): the pod loop's head, the dispatch, the ten cases' fast paths, the
   two fuzz_u32 sites and the slow blocks of the checks the piece steps (0x82770 .. 0x828c8). The `unimp` trap
   sites and the report calls past 0x83a10 are never stepped. Precomputed once, for every block file of the piece. *)
Definition W6B_TLO : Z := 0x81888.
Definition W6B_TN : nat := 1042.
Definition w6b_tbl : ctable := Eval vm_compute in build_table rsegs W6B_TLO W6B_TN TEmpty.
Lemma w6b_tbl_ok : table_ok rsegs w6b_tbl.
Proof.
pose proof (build_table_ok0 rsegs W6B_TN W6B_TLO ltac:(unfold W6B_TLO; lia)) as H.
assert (E : build_table rsegs W6B_TLO W6B_TN TEmpty = w6b_tbl) by (vm_compute; reflexivity).
rewrite E in H. exact H.
Qed.

(* ======================================== the model's values ========================================
   kind mod 10 as the code reaches it: case 9 by the bound test `bltu a2,a1` 0x81924, cases 0 .. 8 by the table at
   .rodata 0x20ecc (HPgSteps jt_tgt). *)
Definition w6b_case_pc (kd : Z) : Z := if kd mod 10 =? 9 then W6B_D9 else jt_tgt (kd mod 10).
Lemma w6b_case_pc_D : forall kd, w6b_case_pc kd = hsu_pc_D headamp_bld_B kd.
Proof.
intros kd. unfold w6b_case_pc, hsu_pc_D, W6B_D9.
pose proof (Z.mod_pos_bound kd 10 ltac:(lia)) as Hm.
destruct (kd mod 10 =? 9) eqn:E9; [reflexivity|].
apply Z.eqb_neq in E9.
assert (Hc : kd mod 10 = 0 \/ kd mod 10 = 1 \/ kd mod 10 = 2 \/ kd mod 10 = 3 \/ kd mod 10 = 4 \/
  kd mod 10 = 5 \/ kd mod 10 = 6 \/ kd mod 10 = 7 \/ kd mod 10 = 8) by lia.
clear E9 Hm.
repeat (destruct Hc as [Hc | Hc]; [rewrite Hc; vm_compute; reflexivity|]).
rewrite Hc; vm_compute; reflexivity.
Qed.
(* the registers the kind block writes, per outcome (case 9 is reached before a3 is formed) *)
Definition w6b_kind_clob : list (bv 5) := [6; 7; 10; 11; 12; 13; 16; 17; 18; 20]%bv.
(* case 2's int when m is even (ints[(m >> 1) % 14]; with no byte left m = 0 and ints[0]) *)
Definition w6b_int_even (m : Z) : Z := nth (Z.to_nat ((m / 2) mod 14)) Tables.ints 0.
(* case 3's bits when m is even: NaN (m = 0xfe), +/- infinity (m = 0xfc, 0xfd), else floats[(m >> 1) % 21];
   this is Model.ent_build's case 3 on an even m. *)
Definition w6b_float_even (m : Z) : Z :=
if m / 2 =? 127 then 0x7fc00000
else if m / 2 =? 126 then (if Z.testbit m 1 then 0xff800000 else 0x7f800000)
else nth (Z.to_nat ((m / 2) mod 21)) Tables.float_bits 0.
(* the value a case's even arm leaves in a1 *)
Definition w6b_even_val (c3 : bool) (m : Z) : Z := if c3 then w6b_float_even m else w6b_int_even m.
(* the bytes a turn of the pod loop consumes in its case: the kind byte is already read, m follows it, and on an
   odd m the four bytes of fuzz_u32 follow m. *)
Definition w6b_rest_of (r : list byte) : list byte :=
let '(m, r1) := Cursor.fuzz_u8 r in if Z.odd m then snd (Cursor.fuzz_u32 r1) else r1.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Local Notation u8s l := (map (fun x : byte => bv_unsigned x) l).

(* ===================== w6b_head: C 0x81888 .. the memset of e62, back at 0x818d0 =====================
     0x81888  sd a1,0x158(s1)                      [R+0x158] := kk (the pod index)
     0x8188c .. 0x818bc  13 x sb zero,o(s3)        shadow_addr F + 66 .. 78 := 0 (e62 in scope, pod.h:426)
     0x818c0  a2 := 0x68; 0x818c4 a0 := s4 (= F + 0x210); 0x818c8 a1 := 0
     0x818cc  jal __asan_memset (0x52228)          e62 := 104 zero bytes (pod.h:279), returns a0 = F + 0x210
   The call is the Section hypothesis AMEMSET (the kernel's contract of __asan_memset, lib/Reusable/YG0d.v
   aintrin_realizes OSet), applied through lib/AU/HPgCaseB.v's cb_memset_at. The destination e62 lies in the frame
   the harness owns and its shadow is the 13 zero bytes just stored. Wr: the callee's stack [R - ESTACK, R), the
   cell [R+0x158, R+0x160), the 13 shadow granules and e62 itself. *)
Definition w6b_head_wr (R F : Z) : Z -> Prop :=
fun a => (R - ESTACK <= a < R) \/ (R + 0x158 <= a < R + 0x160) \/
(shadow_addr F + 66 <= a < shadow_addr F + 79) \/ (F + 0x210 <= a < F + 0x278).
Definition w6b_head_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos kk : Z) (pat : list Z),
cb_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 2 = w64 R -> getr regs 9 = w64 R -> getr regs 19 = w64 (shadow_addr F) ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 11 = w64 kk -> getr regs 20 = w64 (F + 0x210) ->
hd_fsh rsegs (w_H W) memc F pat -> length pat = 116%nat ->
SRr rsegs W (cfg_at rsegs W6B_C regs memc mdc)
(hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6B_RET cb_caller_saved (w6b_head_wr R F)
(fun W2 regs2 mem2 =>
getr regs2 10 = w64 (F + 0x210) /\
val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x158) 8 (kk mod 2 ^ 64) /\
hd_fsh rsegs (w_H W2) mem2 F (hm_setn pat 66 13 0) /\
(forall i, 0 <= i < 104 -> aview rsegs (w_H W2) mem2 (F + 0x210 + i) = Some 0))).

(* the input bytes r at cursor cur, as headamp_build_contract gives them (garr8, range_addressable, 0 < cur,
   cur + |r| <= 2 ^ 63, amem_range) and outside the callees' stack below R and the real frame's cells
   [R, R + 0x198) (HPgImgB hi_w1's (XR, 0, 0x198); HPgSeg hsu_in) *)
Definition w6b_in (W : world rsegs) (memc : word -> option byte) (R cur : Z) (r : list byte) : Prop :=
garr8 rsegs (mrestrict (w_H W) memc) cur (u8s r) /\
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur (Z.of_nat (length r)) /\
0 < cur /\ cur + Z.of_nat (length r) <= 2 ^ 63 /\ amem_range cur (Z.of_nat (length r)) /\
(forall a, cur <= a < cur + Z.of_nat (length r) -> ~ (R - T_SEG_STK <= a < R + 0x198)).

(* ===================== w6b_kind: 0x818d0 .. the case entry (no store) =====================
     0x818d0  beqz s10 -> 0x819c0                   nothing left: kind = 0, case 0 with nothing read
     0x818d4 .. 0x818e0  s2 := s5 + 1; a6 := 1; t2 := 10; `bltu a6,s2` (the pointer test of fuzz.h:42)
     0x818e8  t1 := s10; a7 := s5; the shadow check of s5 (NE-SLOW, slow block 0x82770)
     0x81900  a0 := lbu(a7) = the kind byte
     0x81904 .. 0x81918  a1 := kind mod 10 (a1 = (kind * 0xcd) >> 11, a1 := (kind - 10 a1) & 0xff)
     0x8191c  s4 := t1 - 1 (what is left after the kind byte); 0x81920 a2 := 8
     0x81924  bltu a2,a1 -> 0x82004 (case 9)
     0x81928 .. 0x81948  hdu_jt_block (lib/AU/HPgSteps.v) to jt_tgt (kind mod 10), a3 := the sign-extended byte.
   The cursor is s5 = cur and what is left s10 = |rr|. *)
Definition w6b_kind_R (kd cur nl : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 17 = w64 cur /\ getr regs2 18 = w64 (cur + 1) /\ getr regs2 6 = w64 (nl + 1) /\
getr regs2 20 = w64 nl /\ getr regs2 7 = w64 10 /\ getr regs2 16 = w64 1 /\
(kd mod 10 = 9 \/ getr regs2 13 = w64 (sext8 kd)).
Definition w6b_kind_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos cur : Z)
(rr : list byte),
cb_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 2 = w64 R -> getr regs 9 = w64 R -> getr regs 27 = w64 SHADOW_OFF ->
getr regs 21 = w64 cur -> getr regs 26 = w64 (Z.of_nat (length rr)) ->
w6b_in W memc R cur rr ->
SRr rsegs W (cfg_at rsegs W6B_RET regs memc mdc)
(fun W2 c2 =>
 (rr = [] /\
  hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6B_D0E []%bv (fun _ => False)
  (fun _ _ _ => True) W2 c2) \/
 (exists b r, rr = b :: r /\
  hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc
  (w6b_case_pc (bv_unsigned b)) w6b_kind_clob (fun _ => False)
  (fun _ regs2 _ => w6b_kind_R (bv_unsigned b) cur (Z.of_nat (length r)) regs2) W2 c2)).

(* ===================== w6b_c2 / w6b_c3: a case's head (no store) =====================
   At the case entry (w6b_kind's post): a7 = c - 1 (the kind byte's address), s2 = c (the cursor after it),
   t1 = |r| + 1, s4 = |r|, t2 = 10, a6 = 1, a3 = the sign-extended kind byte; s5, s10 and s7 = -8 are the pod
   loop's and are not read again before J. m = fuzz_u8 r.
   case 2 (pod.h:298-303): 0x81cbc `beqz s4` -> 0x820a0 (no byte: m = 0, ints[0]); the pointer test of fuzz.h:42
     (`bltu a6,a0` 0x81cc4, with a0 = s2 + 1: its `unimp` arm needs 1 <u c + 1, which 0 < c gives); the shadow
     check of s2 (NE-SLOW, slow block 0x827f8); s7 := [R+0x148] = pp; a1 := lbu(s2) = m; a2 := t1 - 2;
     s2 := a7 + 2; m odd -> 0x8238c `ld s4,0x130(s1)` and stop at 0x82390 (hdu_u32_block2's entry, whose premises
     this post carries); m even -> 0x81cf4 .. 0x81d30 a1 := &ints[(m >> 1) % 14] (the `mulhu` by the cell at
     0x10318; the pointer-overflow test 0x81d24 passes because the byte offset is at most 52), then 0x820b0 .. 0x820cc
     the shadow check of that element (its slow block 0x827b4), s4 := [R+0x130] = &e62, a4 := 4,
     a1 := lw 0(a1), stop at 0x82578.
   case 3 (pod.h:304-324): 0x81d34, the same read with s4 := [R+0x130] taken before the branch (0x81d54);
     m odd -> 0x823cc (hdu_u32_block3's entry); m = 0xfe -> 0x8249c a1 := 0x7fc00000; m = 0xfc -> 0x81d80
     a1 := 0x7f800000; else 0x824a4 .. 0x824d8 a1 := &floats[(m >> 1) % 21] (`mulhu` by the cell at 0x10310, the
     index at most 80) and 0x824dc .. 0x824f4 its shadow check and load; every even arm stops at 0x825fc with
     a4 = 4 (0x825f8 `addi a4,zero,4` on the two literal arms, 0x824ec on the table arm).
   The value is given mod 2 ^ 32 (`lw` sign-extends; the tail stores its low four bytes). *)
Definition w6b_case_in (W : world rsegs) (memc : word -> option byte) (regs : bvmap 5 word) (R F pp c : Z)
(r : list byte) : Prop :=
getr regs 2 = w64 R /\ getr regs 9 = w64 R /\ getr regs 27 = w64 SHADOW_OFF /\
getr regs 17 = w64 (c - 1) /\ getr regs 18 = w64 c /\ getr regs 6 = w64 (Z.of_nat (length r) + 1) /\
getr regs 20 = w64 (Z.of_nat (length r)) /\ getr regs 16 = w64 1 /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 (F + 0x210) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x148) 8 pp /\
0 < c - 1 /\ w6b_in W memc R c r.
(* what the case's head leaves at the entry of its fuzz_u32 block: exactly hdu_u32_stmt's premises for the bytes
   after m, with &e62 in s4 and pp in s7 for the tail *)
Definition w6b_case_odd_R (F pp c : Z) (r1 : list byte) (regs2 : bvmap 5 word) : Prop :=
getr regs2 12 = w64 (Z.of_nat (length r1)) /\ getr regs2 18 = w64 (c + 1) /\
getr regs2 20 = w64 (F + 0x210) /\ getr regs2 23 = w64 pp.
(* and at the tail's entry: the value in a1, what is left in a2, the cursor in s2, 4 in a4 *)
Definition w6b_case_even_R (c3 : bool) (F pp c : Z) (r : list byte) (regs2 : bvmap 5 word) : Prop :=
(exists v, getr regs2 11 = w64 v /\
 v mod 2 ^ 32 = w6b_even_val c3 (fst (Cursor.fuzz_u8 r)) mod 2 ^ 32) /\
getr regs2 12 = w64 (Z.of_nat (length (snd (Cursor.fuzz_u8 r)))) /\
getr regs2 14 = w64 4 /\
getr regs2 18 = w64 (c + Z.of_nat (length r - length (snd (Cursor.fuzz_u8 r)))) /\
getr regs2 20 = w64 (F + 0x210) /\ getr regs2 23 = w64 pp.
Definition w6b_case_clob : list (bv 5) := [10; 11; 12; 13; 14; 15; 18; 20; 23]%bv.
Definition w6b_case_stmt (c3 : bool) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos pp c : Z)
(r : list byte),
cb_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
w6b_case_in W memc regs R F pp c r ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (if c3 then W6B_FLOATS else W6B_INTS)
  (if c3 then 84 else 56) ->
SRr rsegs W (cfg_at rsegs (if c3 then W6B_D3 else W6B_D2) regs memc mdc)
(fun W2 c2 =>
 if Z.odd (fst (Cursor.fuzz_u8 r)) then
  hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (if c3 then W6B_U3 else W6B_U2)
  w6b_case_clob (fun _ => False)
  (fun _ regs2 _ => w6b_case_odd_R F pp c (snd (Cursor.fuzz_u8 r)) regs2) W2 c2
 else
  hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (if c3 then W6B_T3 else W6B_T2)
  w6b_case_clob (fun _ => False)
  (fun _ regs2 _ => w6b_case_even_R c3 F pp c r regs2) W2 c2).
Definition w6b_c2_stmt : Prop := w6b_case_stmt false.
Definition w6b_c3_stmt : Prop := w6b_case_stmt true.

(* ===================== w6b_tail2 / w6b_tail3: the cases' common tail .. J 0x82618 =====================
     0x82574  a4 := 4                                               (case 2's fuzz_u32 exit only)
     0x82578  sw a4,0(s4)        e62.type := 4 (POD_INT); j 0x82604 (case 2)
     0x825f8  a4 := 4                                               (case 3's fuzz_u32 and literal exits only)
     0x825fc  a0 := 6; 0x82600 sw a0,0(s4)   e62.type := 6 (POD_FLOAT)                              (case 3)
     0x82604  sw a4,4(s4)        e62.size := 4
     0x82608  sw a1,8(s4)        e62.body[0..4) := the value
     0x8260c  t1 := a2 (what is left); 0x82610 a3 := s2 (the cursor); 0x82614 s2 := [R+0x138] = &pp->len
                                                                                              -> J 0x82618
   e62 = F + 0x210 lies in the frame (4, pos) the harness owns; the three stores carry no instrumented check (the
   memset of pod.h:279 made the object's shadow 0 just before). Wr: e62's first twelve bytes. *)
Definition w6b_tail_wr (F : Z) : Z -> Prop := fun a => F + 0x210 <= a < F + 0x21c.
Definition w6b_tail_stmt (c3 : bool) (pc0 : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos pp n' v c' : Z),
cb_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 2 = w64 R -> getr regs 9 = w64 R -> getr regs 20 = w64 (F + 0x210) ->
getr regs 11 = w64 v -> getr regs 12 = w64 n' -> getr regs 18 = w64 c' ->
(pc0 = W6B_T2 \/ pc0 = W6B_T3 -> getr regs 14 = w64 4) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 (pp + Layout.OFF_LEN) ->
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
(hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6B_J [6; 10; 13; 14; 18]%bv
(w6b_tail_wr F)
(fun W2 regs2 mem2 =>
getr regs2 6 = w64 n' /\ getr regs2 13 = w64 c' /\ getr regs2 18 = w64 (pp + Layout.OFF_LEN) /\
val_mem rsegs (mrestrict (w_H W2) mem2) (F + 0x210) 4 (if c3 then 6 else 4) /\
val_mem rsegs (mrestrict (w_H W2) mem2) (F + 0x214) 4 4 /\
val_mem rsegs (mrestrict (w_H W2) mem2) (F + 0x218) 4 (v mod 2 ^ 32))).
(* the four entries: case 2 from its fuzz_u32 exit and from its even arm, case 3 likewise *)
Definition w6b_tail2u_stmt : Prop := w6b_tail_stmt false W6B_U2E.
Definition w6b_tail2_stmt : Prop := w6b_tail_stmt false W6B_T2.
Definition w6b_tail3u_stmt : Prop := w6b_tail_stmt true W6B_U3E.
Definition w6b_tail3_stmt : Prop := w6b_tail_stmt true W6B_T3.

End d.
End b.

(* ======================================== what the model says of cases 2 and 3 ========================================
   Model.ent_build's cases 2 and 3 on a kind byte b with b mod 10 = 2 / 3: the pod is Ent POD_INT / POD_FLOAT of
   size 4 whose body is the four little-endian bytes of the value, and the input left is what follows m (and, on an
   odd m, the four bytes of fuzz_u32 after it). *)
Lemma w6b_ent_build : forall (c3 : bool) (b : byte) (r : list byte),
bv_unsigned b mod 10 = (if c3 then 3 else 2) ->
Model.ent_build (b :: r) =
(Model.Ent (if c3 then Model.POD_FLOAT else Model.POD_INT) 4
  (Cursor.le32 (if Z.odd (fst (Cursor.fuzz_u8 r)) then fst (Cursor.fuzz_u32 (snd (Cursor.fuzz_u8 r)))
                else w6b_even_val c3 (fst (Cursor.fuzz_u8 r)))),
 w6b_rest_of r).
Proof.
intros c3 b r Hb. unfold Model.ent_build, w6b_rest_of, w6b_even_val, w6b_int_even, w6b_float_even.
cbn [Cursor.fuzz_u8 fst snd].
destruct (Cursor.fuzz_u8 (b :: r)) as [kd r0] eqn:Ek.
assert (Ekd : kd = bv_unsigned b /\ r0 = r).
{ unfold Cursor.fuzz_u8 in Ek. injection Ek as <- <-. split; reflexivity. }
destruct Ekd as [-> ->]. rewrite Hb.
destruct c3; cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add].
- destruct (Cursor.fuzz_u8 r) as [m r1] eqn:Em. cbn [fst snd].
  destruct (Z.odd m); [destruct (Cursor.fuzz_u32 r1) as [v r2] eqn:Ev; cbn [fst snd]; reflexivity|].
  destruct (Z.eqb_spec (m / 2) 127) as [E127|_]; [reflexivity|].
  destruct (Z.eqb_spec (m / 2) 126) as [E126|_]; [destruct (Z.testbit m 1); reflexivity | reflexivity].
- destruct (Cursor.fuzz_u8 r) as [m r1] eqn:Em. cbn [fst snd].
  destruct (Z.odd m); [destruct (Cursor.fuzz_u32 r1) as [v r2] eqn:Ev; cbn [fst snd]; reflexivity | reflexivity].
Qed.

(* the bytes of the pod the tail writes: type, size 4 and the four value bytes, then e62's 92 zero bytes *)
Lemma w6b_ent_mem : forall ty v,
Layout.ent_mem (Model.Ent ty 4 (Cursor.le32 v)) =
Cursor.le32 ty ++ Cursor.le32 4 ++ Cursor.le32 v ++ Cursor.zeros 92.
Proof. intros ty v. unfold Layout.ent_mem. cbn [Model.e_type Model.e_size Model.e_body]. reflexivity. Qed.
