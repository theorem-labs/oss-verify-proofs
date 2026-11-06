(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, as pa_i_region_nth over a restricted state and pa_i_field) and proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v at a0d3fb0309b (aj_intrin_at, as pa_i_memset_at: at OSet on rsegs, its post adds same_io from the contract's same_but_materialized); the rest of the file is new: the block lemma pa_int7 of LLVMFuzzerTestOneInput's shape-7 Int pod block and its helpers. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v, with its module paths and module names changed; 1062 of its 1144 lines of code are new or changed and 417 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgSteps.v at 6bdf633122fe for reac-pw/fuzz_rate's
   image A: module paths changed; the image is fuzz_rate.asan (images.Asan) instead of a lib/A/Img0 module; the jump
   table's site, table and targets and the fuzz_u32 sites are rate's (their registers: the cursor in s9, the shadow
   offset in s2, the original byte count in a5 / a7, no frame cell); the prefix rl_ becomes rts_; the image facts
   wx_segs_nowrap / segs-low and same_io_wvb are stated here instead of taken from a cfg walk file; the block-chaining
   lemmas and helpers (from proofs/reac-pw/fuzz_role/lib/A/RPgW6aBase.v and RPgW6aHead.v at ef33766f272a), the
   intrinsic call adapter (RPgW6aHead.v w6h_intrin, for both OSet and OCpy), the generic ecall adapter, the class-3
   frame arithmetic and the frame write rights are added. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgSteps.v, with its module paths changed; 146 of its 241 lines of code are new or changed and 1049 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aBase.v at 876d0cb3d0d; for reac-pw/fuzz_headamp image A: module paths and the rl_ prefix renamed to hd_, every pc moved by the code's uniform shift +0xd20 over [0x80a80, 0x81af0) (the memset call to 0x521a8), the real-frame cells by the plan's slot map (0xb0>0xd0, 0xd8>0xf8, 0xf0>0x110, 0xf8>0x118), the frame for locals of class 4 (80 shadow bytes), the real frame of 0x1e0 bytes and hi_w1's cells [R, R+0x160). *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): the BLOCK STATEMENTS of the
   walk piece "ent_build A" of LLVMFuzzerTestOneInput (0x80bc0): the pod loop's head C (0x817a0) to the dispatch of
   ent_build's `switch (kind % 10)` (pod.h:279-281), and the cases 2 and 3 (pod.h:298-324) to the join J (0x8237c).
   Statement text only: no function is proved here (kind: segment lemma).

   WHY BLOCKS. The piece is cut at the points where the code calls something (the __asan_memset of e at 0x817e4,
   the fuzz_u32 read-ahead block of lib/A/HPgSteps.v, the jump table block hd_jt_block of the same file) and at
   the first store of each case's common tail. Each block is stated over the machine state it starts from (its
   registers, the 8-byte frame cells it reads, the input bytes) in the shape of a callee contract, so that the blocks
   are proved independently and the piece is their chaining with SRr_bind:
     w6_head  C 0x817a0 .. 0x817e4 + the memset call: k into [R+0xf8], e's 13 shadow granules := 0, e := 0^104;
              returns at 0x817e8.
     w6_kind  0x817e8 .. the case entry: in.n = 0 goes to 0x818cc; else the kind byte, kind % 10 (0xcd multiply,
              0x81810 .. 0x81828), case 9 to 0x81ea4 by `bltu` 0x81838, cases 0 .. 8 through hd_jt_block.
     w6_c2h   case 2's head 0x81bd4: m = fuzz_u8; m odd stops at 0x81c04 (the fuzz_u32 block's start), m even (or
              no byte) loads ints[(m >> 1) % 14] and stops at 0x82308.
     w6_c3h   case 3's head 0x81c3c: m odd stops at 0x82174; else NaN (m = 0xfe), inf (m = 0xfc) or
              floats[(m >> 1) % 21], stopping at 0x8235c.
     w6_tail  0x82308 (case 2, type 4) / 0x8235c (case 3, type 6) .. J 0x8237c: e.type, e.size = 4, e.body[0..4)
              := the value, [R+0x118] := in.n, s9 := the cursor.
   THE REGISTERS (the plan's section 2.2, checked against the code): s1 = R (x9) the real frame's base, s3 = shadow_addr F (x19),
   s7 = SHADOW_OFF (x23); in the pod loop the cursor in.p is s9 (x25) and in.n is the cell [R+0x118]; after the kind
   read the cursor is s8 (x24), s9 = in.n - 1, a4 (x14) = the kind byte's address, and [R+0x118] still holds the
   in.n of the kind read (the read-ahead compares it with 3, 4, 5). [R+0x110] = F + 0xf0 (the address of e), [R+0xd0]
   the shadow address the cases reload into s4 (x20). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================== the pcs ======================================== *)
Definition W6_C : Z := 0x817a0.        (* `sd a1,0xf8(s1)`: the pod loop's head *)
Definition W6_MEMSET : Z := 0x521a8.   (* __asan_memset, the `jal` target at 0x817e4 *)
Definition W6_RET : Z := 0x817e8.      (* after the memset of e *)
Definition W6_D0E : Z := 0x818cc.      (* case 0 with no input left (`beqz a0` 0x817ec taken) *)
Definition W6_D9 : Z := 0x81ea4.       (* case 9 (`bltu a2,a1` 0x81838 taken) *)
Definition W6_JT : Z := 0x8183c.       (* hd_jt_block's start *)
Definition W6_D2 : Z := 0x81bd4.
Definition W6_D3 : Z := 0x81c3c.
Definition W6_U2 : Z := 0x81c04.       (* case 2's fuzz_u32 block (HPgSteps hd_u32_block2) .. 0x82308 *)
Definition W6_U3 : Z := 0x82174.       (* case 3's fuzz_u32 block (HPgSteps hd_u32_block3) .. 0x8235c *)
Definition W6_T2 : Z := 0x82308.       (* case 2's tail: e.type := 4 *)
Definition W6_T3 : Z := 0x8235c.       (* case 3's tail: e.type := 6 *)
Definition W6_J : Z := 0x8237c.        (* the join: the inlined pod_write_ent begins *)
(* the tables the cases read (registered globals, .rodata): ints[14] at 0x21000, floats[21] at 0x21060 *)
Definition W6_INTS : Z := 0x21000.
Definition W6_FLOATS : Z := 0x21060.

(* ======================================== the code table ========================================
   Every instruction word of [0x817a0, 0x82810): the dispatch, the ten cases' fast paths and the slow blocks of
   their checks (0x82664 .. 0x82808). The report calls past 0x83848 are never stepped. Precomputed once. *)
Definition W6_TLO : Z := 0x817a0.
Definition W6_TN : nat := 1052.
Definition w6_tbl : ctable := Eval vm_compute in build_table rsegs W6_TLO W6_TN TEmpty.
Lemma w6_tbl_ok : table_ok rsegs w6_tbl.
Proof.
pose proof (build_table_ok0 rsegs W6_TN W6_TLO ltac:(unfold W6_TLO; lia)) as H.
assert (E : build_table rsegs W6_TLO W6_TN TEmpty = w6_tbl) by (vm_compute; reflexivity).
rewrite E in H. exact H.
Qed.

(* ======================================== the model's values ======================================== *)
(* kind % 10 as the code computes it (case 9 by the branch, cases 0 .. 8 by the table) *)
Definition w6_case_pc (kd : Z) : Z := if kd mod 10 =? 9 then W6_D9 else jt_tgt (kd mod 10).
(* the registers the kind block writes, per outcome *)
Definition w6_kind_clob (kd : Z) : list (bv 5) :=
if kd mod 10 =? 9 then [10; 11; 12; 14; 17; 24; 25]%bv else [10; 11; 12; 14; 17; 20; 24; 25]%bv.
(* case 2's int when m is even (ints[(m >> 1) % 14]; with no byte left m = 0 and ints[0]) *)
Definition w6_int_even (m : Z) : Z := nth (Z.to_nat ((m / 2) mod 14)) Tables.ints 0.
(* case 3's bits when m is even: NaN, inf, or floats[(m >> 1) % 21] (Model.ent_build's case 3) *)
Definition w6_float_even (m : Z) : Z :=
if m / 2 =? 127 then 0x7fc00000
else if m / 2 =? 126 then (if Z.testbit m 1 then 0xff800000 else 0x7f800000)
else nth (Z.to_nat ((m / 2) mod 21)) Tables.float_bits 0.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Local Notation u8s l := (map (fun x : byte => bv_unsigned x) l).

(* ===================== the context every block runs in =====================
   The harness's journal from the segment's start (hd_seg_pre's first conjunct), the real frame [R, R + 0x1e0)
   inside the journal's stack window with the callees' stack below it, the frame for locals F = the side-stack frame
   (4, pos) the harness holds, and the read-only segments as in the image (hd_seg_pre's rom_view). *)
Definition w6_ctx (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z)
(lyc : alayout) (Sc : astate) (W : world rsegs) (memc : word -> option byte) (mdc : Model) (R F pos : Z) : Prop :=
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
R mod 16 = 0 /\ R + 0x1e0 <= sp0 /\ sp0 - STK <= R - T_SEG_STK /\
In (4, pos) own /\ F = frame_addr lyc 4 pos /\
rom_view rsegs W memc.

(* The post of a block that writes memory: hd_blk_post (lib/A/HPgSteps.v) with every byte outside Wr kept instead of
   every byte, and R reading the world and memory too. *)
Definition w6_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z) (regs : bvmap 5 word)
(lyc : alayout) (Sc : astate) (W : world rsegs) (memc : word -> option byte) (mdc : Model) (pc : Z)
(clob : list (bv 5)) (Wr : Z -> Prop) (R : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop)
: world rsegs -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (w64 pc) mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs2 r = getr regs r) /\
frames S2 = frames Sc /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ same_io mdc md2 /\ mo_le MT Sc S2 0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W) memc a) /\
R W2 regs2 mem2.

(* the registers a call may change (everything but YG0d.acallee_saved and x0) *)
Definition w6_caller_saved : list (bv 5) :=
[1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.

(* ===================== w6_head: C 0x817a0 .. the memset of e, back at 0x817e8 =====================
     0x817a0  sd a1,0xf8(s1)                       [R+0xf8] := k (the pod index)
     0x817a4 .. 0x817d4  13 x sb zero,o(s3)        shadow_addr F + 0x1e .. 0x2a := 0 (e in scope, pod.h:426)
     0x817d8  a2 := 0x68; 0x817dc ld a0,0x110(s1) (= F + 0xf0); 0x817e0 a1 := 0
     0x817e4  jal __asan_memset (0x521a8)          e := 104 zero bytes (pod.h:279), returns a0 = F + 0xf0
   The memset is the kernel's aintrin_realizes OSet (lib/Reusable/YG0d.v), a hypothesis of the proof. Wr: the
   callee's stack [R - ESTACK, R), the cell [R+0xf8, R+0x100), the 13 granules and e. *)
Definition w6_head_wr (R F : Z) : Z -> Prop :=
fun a => (R - ESTACK <= a < R) \/ (R + 0xf8 <= a < R + 0x100) \/
(shadow_addr F + 0x1e <= a < shadow_addr F + 0x2b) \/ (F + 0xf0 <= a < F + 0x158).
Definition w6_head_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos kk : Z) (pat : list Z),
w6_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 2 = w64 R -> getr regs 9 = w64 R -> getr regs 19 = w64 (shadow_addr F) ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 11 = w64 kk ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x110) 8 (F + 0xf0) ->
hd_fsh rsegs (w_H W) memc F pat -> length pat = 80%nat ->
SRr rsegs W (cfg_at rsegs W6_C regs memc mdc)
(w6_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6_RET w6_caller_saved (w6_head_wr R F)
(fun W2 regs2 mem2 =>
getr regs2 10 = w64 (F + 0xf0) /\
val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0xf8) 8 (kk mod 2 ^ 64) /\
(forall i, 0 <= i < 13 -> aview rsegs (w_H W2) mem2 (shadow_addr F + 0x1e + i) = Some 0) /\
(forall i, 0 <= i < 104 -> aview rsegs (w_H W2) mem2 (F + 0xf0 + i) = Some 0))).

(* the input bytes r at cursor cur, as headamp_build_contract gives them (garr8, range_addressable, 0 < src,
   src + left <= 2 ^ 63, amem_range) and outside the callees' stack below R and the real frame's cells
   [R, R + 0x160) (HPgImgA hi_w1's (XR, 0, 0x160); HPgSeg hs_in) *)
Definition w6_in (W : world rsegs) (memc : word -> option byte) (R cur : Z) (r : list byte) : Prop :=
garr8 rsegs (mrestrict (w_H W) memc) cur (u8s r) /\
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur (Z.of_nat (length r)) /\
0 < cur /\ cur + Z.of_nat (length r) <= 2 ^ 63 /\ amem_range cur (Z.of_nat (length r)) /\
(forall a, cur <= a < cur + Z.of_nat (length r) -> ~ (R - T_SEG_STK <= a < R + 0x160)).

(* ===================== w6_kind: 0x817e8 .. the case entry (no store) =====================
     0x817e8  ld a0,0x118(s1); beqz a0 -> 0x818cc     in.n = 0: kind = 0, case 0 with nothing read
     0x817f0 .. 0x817fc  the shadow check of s9 (NE-SLOW, slow block 0x82664)
     0x81800  lbu a0,0(s9); s8 := s9; s9 := [R+0x118] - 1
     0x81810 .. 0x81828  a1 := kind % 10 (a1 = (kind * 0xcd) >> 11, a1 := (kind - 10 a1) & 0xff), a7 := 10
     0x8182c  a4 := s8 (the kind's address); s8 += 1; a2 := 8; 0x81838 bltu a2,a1 -> 0x81ea4 (case 9)
     0x8183c .. 0x8185c  hd_jt_block (lib/A/HPgSteps.v) to jt_tgt (kind % 10).
   The cursor is s9 = cur and the input left is r ([R+0x118] = |r|). *)
Definition w6_kind_R (kd cur nl' : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 14 = w64 cur /\ getr regs2 24 = w64 (cur + 1) /\ getr regs2 25 = w64 nl' /\ getr regs2 17 = w64 10 /\
(if kd mod 10 =? 9 then getr regs2 10 = w64 kd /\ getr regs2 11 = w64 9 /\ getr regs2 12 = w64 8
 else bv_unsigned (getr regs2 10) = (kd mod 256) * 2 ^ 56 /\ getr regs2 11 = w64 (jt_tgt (kd mod 10)) /\
      getr regs2 12 = w64 JT_A /\ getr regs2 20 = w64 (sext8 kd)).
Definition w6_kind_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos cur : Z) (r : list byte),
w6_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 9 = w64 R -> getr regs 23 = w64 SHADOW_OFF -> getr regs 25 = w64 cur ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 (Z.of_nat (length r)) ->
w6_in W memc R cur r ->
SRr rsegs W (cfg_at rsegs W6_RET regs memc mdc)
(fun W2 c2 =>
 (r = [] /\
  hd_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6_D0E [10]%bv
  (fun regs2 => getr regs2 10 = w64 0) W2 c2) \/
 (exists b r', r = b :: r' /\
  hd_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (w6_case_pc (bv_unsigned b))
  (w6_kind_clob (bv_unsigned b)) (w6_kind_R (bv_unsigned b) cur (Z.of_nat (length r'))) W2 c2)).

(* ===================== w6_c2h / w6_c3h: a case's head (no store) =====================
   At the case entry (w6_kind's post): s8 = c (the cursor after kind), s9 = |r| (in.n after kind), a4 = c - 1,
   [R+0x118] = |r| + 1 (in.n of the kind read), [R+0xd0] = vb. m = fuzz_u8 r.
   case 2 (pod.h:298-303): 0x81bd4 beqz s9 -> 0x81f10 (m = 0); the check of s8 (NE-SLOW, 0x82704); lbu a2 = m;
     s4 := [R+0xd0]; a1 := [R+0x118] - 2; s8 := a4 + 2; m odd: stop at 0x81c04 (the u32 block: a1 = |r'|,
     s8 = c + 1, a4 = c - 1, [R+0x118] = |r'| + 2, exactly hd_u32_block2's premises); m even: 0x81f1c .. 0x81f5c
     a2 := ints[(m >> 1) % 14] (mulhu by the constant at 0x10318; the check of the int, NE-SLOW 0x826c0), stop at
     0x82308.
   case 3 (pod.h:304-324): 0x81c3c, the same read; m odd: stop at 0x82174; m = 0xfe: a2 := 0x7fc00000 (0x82278);
     m = 0xfc: a2 := 0x7f800000 (0x81c7c); else a2 := floats[(m >> 1) % 21] (0x82280 .. 0x822bc, mulhu by the
     constant at 0x10310, the check NE-SLOW 0x82774, its slow path reached at floats[20]); stop at 0x8235c.
   The value is given mod 2 ^ 32 (`lw` sign-extends; the tail stores its low 4 bytes). *)
Definition w6_head_in (W : world rsegs) (memc : word -> option byte) (regs : bvmap 5 word) (R c vb : Z)
(r : list byte) : Prop :=
getr regs 9 = w64 R /\ getr regs 23 = w64 SHADOW_OFF /\ getr regs 24 = w64 c /\
getr regs 25 = w64 (Z.of_nat (length r)) /\ getr regs 14 = w64 (c - 1) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 (Z.of_nat (length r) + 1) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xd0) 8 vb /\ 0 <= vb < 2 ^ 64 /\
0 < c - 1 /\ w6_in W memc R c r.
Definition w6_case_head_stmt (c3 : bool) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos c vb : Z) (r : list byte),
w6_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
w6_head_in W memc regs R c vb r ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (if c3 then W6_FLOATS else W6_INTS) (if c3 then 84 else 56) ->
SRr rsegs W (cfg_at rsegs (if c3 then W6_D3 else W6_D2) regs memc mdc)
(fun W2 c2 =>
 let mv := fst (Cursor.fuzz_u8 r) in let r1 := snd (Cursor.fuzz_u8 r) in
 if Z.odd mv then
  hd_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (if c3 then W6_U3 else W6_U2)
  [10; 11; 12; 13; 20; 24]%bv
  (fun regs2 => getr regs2 11 = w64 (Z.of_nat (length r1)) /\ getr regs2 12 = w64 mv /\
     getr regs2 24 = w64 (c + 1) /\ getr regs2 20 = w64 vb) W2 c2
 else
  hd_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (if c3 then W6_T3 else W6_T2)
  [10; 11; 12; 13; 20; 24]%bv
  (fun regs2 => (exists v, getr regs2 12 = w64 v /\
       v mod 2 ^ 32 = (if c3 then w6_float_even mv else w6_int_even mv) mod 2 ^ 32) /\
     getr regs2 11 = w64 (Z.of_nat (length r1)) /\
     getr regs2 24 = w64 (c + Z.of_nat (length r - length r1)) /\ getr regs2 20 = w64 vb) W2 c2).
Definition w6_c2h_stmt : Prop := w6_case_head_stmt false.
Definition w6_c3h_stmt : Prop := w6_case_head_stmt true.

(* ===================== w6_tail: 0x82308 / 0x8235c .. J 0x8237c =====================
     0x82308  ld a0,0x110(s1); a3 := 4; sw a3,0(a0) (e.type = POD_INT); j 0x8236c        (case 2)
     0x8235c  ld a0,0x110(s1); a3 := 6; sw a3,0(a0) (e.type = POD_FLOAT); a3 := 4        (case 3)
     0x8236c  sw a3,4(a0) (e.size = 4); sw a2,8(a0) (e.body[0..4) = the value); sd a1,0x118(s1) (in.n)
     0x82378  mv s9,s8 (the cursor)                                                        -> J 0x8237c
   e = F + 0xf0 lies in the frame (4, pos) the harness owns; [R+0x118] in the real frame. *)
Definition w6_tail_wr (R F : Z) : Z -> Prop :=
fun a => (F + 0xf0 <= a < F + 0xfc) \/ (R + 0x118 <= a < R + 0x120).
Definition w6_tail_stmt (c3 : bool) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos n' v c' : Z),
w6_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 9 = w64 R -> val_mem rsegs (mrestrict (w_H W) memc) (R + 0x110) 8 (F + 0xf0) ->
getr regs 11 = w64 n' -> getr regs 12 = w64 v -> getr regs 24 = w64 c' ->
SRr rsegs W (cfg_at rsegs (if c3 then W6_T3 else W6_T2) regs memc mdc)
(w6_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6_J [10; 13; 25]%bv (w6_tail_wr R F)
(fun W2 regs2 mem2 =>
getr regs2 10 = w64 (F + 0xf0) /\ getr regs2 13 = w64 4 /\ getr regs2 25 = w64 c' /\
val_mem rsegs (mrestrict (w_H W2) mem2) (F + 0xf0) 4 (if c3 then 6 else 4) /\
val_mem rsegs (mrestrict (w_H W2) mem2) (F + 0xf4) 4 4 /\
val_mem rsegs (mrestrict (w_H W2) mem2) (F + 0xf8) 4 (v mod 2 ^ 32) /\
val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x118) 8 (n' mod 2 ^ 64))).
Definition w6_tail2_stmt : Prop := w6_tail_stmt false.
Definition w6_tail3_stmt : Prop := w6_tail_stmt true.

(* ===================== chaining the blocks =====================
   A pure-read block (hd_blk_post) is a w6_post with any write set; two w6_post blocks chain into one, with the
   union of the clobbered registers and of the write sets, and the second block's R. *)
Section seq.
Hypothesis MTL : ameter_laws MT.
Lemma w6_post_of_blk : forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob
(Rr : bvmap 5 word -> Prop) (Wr : Z -> Prop) W2 c2,
hd_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob Rr W2 c2 ->
w6_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob Wr (fun _ regs2 _ => Rr regs2) W2 c2.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob Rr Wr W2 c2
(ly2 & S2 & regs2 & mem2 & md2 & Ec & HJ & Hr & Hf & Hp & Hio & Hmo & Hm & HR).
exists ly2, S2, regs2, mem2, md2. repeat (split; [eassumption|]).
split; [intros a _ _; apply Hm|]. exact HR.
Qed.
Lemma w6_post_seq : forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc0 pc1 pc2 clob1 clob2
(Wr1 Wr2 : Z -> Prop) (R1 R2 : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop),
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
(w6_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc1 clob1 Wr1 R1) ->
(forall W1 ly1 S1 regs1 mem1 md1, wle W W1 ->
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k ->
 (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob1 -> getr regs1 r = getr regs r) ->
 frames S1 = frames Sc -> Permutation (ablocks B ly1 S1) (ablocks B lyc Sc) -> same_io mdc md1 -> mo_le MT Sc S1 0 ->
 (forall a, 0 <= a < 2 ^ 64 -> ~ Wr1 a -> aview rsegs (w_H W1) mem1 a = aview rsegs (w_H W) memc a) ->
 R1 W1 regs1 mem1 ->
 SRr rsegs W1 (cfg_at rsegs pc1 regs1 mem1 md1)
 (w6_post STK sp0 FP ly S W0 mem0 md0 own k regs1 ly1 S1 W1 mem1 md1 pc2 clob2 Wr2 R2)) ->
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
(w6_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc2 (clob1 ++ clob2) (fun a => Wr1 a \/ Wr2 a) R2).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc0 pc1 pc2 clob1 clob2 Wr1 Wr2 R1 R2 H1 H2.
eapply SRr_bind; [exact H1|].
intros W1 c1 Hw1 (ly1 & S1 & regs1 & mem1 & md1 & -> & HJ1 & Hr1 & Hf1 & Hp1 & Hio1 & Hmo1 & Hm1 & HR1).
eapply SRr_mono; [exact (H2 W1 ly1 S1 regs1 mem1 md1 Hw1 HJ1 Hr1 Hf1 Hp1 Hio1 Hmo1 Hm1 HR1)|].
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & Hr2 & Hf2 & Hp2 & Hio2 & Hmo2 & Hm2 & HR2).
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|].
split; [intros r Hr0 Hn; rewrite (Hr2 r Hr0 ltac:(intros X; apply Hn; apply in_or_app; right; exact X));
  apply Hr1; [exact Hr0 | intros X; apply Hn; apply in_or_app; left; exact X]|].
split; [rewrite Hf2; exact Hf1|].
split; [eapply Permutation_trans; [exact Hp2 | exact Hp1]|].
split; [eapply same_io_trans; [exact Hio1 | exact Hio2]|].
split; [exact (mle_station MT Sc S1 S2 0 0 MTL Hmo1 Hmo2)|].
split; [intros a Ha Hn; rewrite (Hm2 a Ha ltac:(intros X; apply Hn; right; exact X));
  exact (Hm1 a Ha ltac:(intros X; apply Hn; left; exact X))|].
exact HR2.
Qed.
Lemma w6_blk_seq : forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc0 pc1 pc2 clob1 clob2
(R1 R2 : bvmap 5 word -> Prop),
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
(hd_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc1 clob1 R1) ->
(forall W1 ly1 S1 regs1 mem1 md1, wle W W1 ->
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k ->
 (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob1 -> getr regs1 r = getr regs r) ->
 frames S1 = frames Sc -> Permutation (ablocks B ly1 S1) (ablocks B lyc Sc) -> same_io mdc md1 -> mo_le MT Sc S1 0 ->
 (forall a, aview rsegs (w_H W1) mem1 a = aview rsegs (w_H W) memc a) ->
 R1 regs1 ->
 SRr rsegs W1 (cfg_at rsegs pc1 regs1 mem1 md1)
 (hd_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs1 ly1 S1 W1 mem1 md1 pc2 clob2 R2)) ->
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
(hd_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc2 (clob1 ++ clob2) R2).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc0 pc1 pc2 clob1 clob2 R1 R2 H1 H2.
eapply SRr_bind; [exact H1|].
intros W1 c1 Hw1 (ly1 & S1 & regs1 & mem1 & md1 & -> & HJ1 & Hr1 & Hf1 & Hp1 & Hio1 & Hmo1 & Hm1 & HR1).
eapply SRr_mono; [exact (H2 W1 ly1 S1 regs1 mem1 md1 Hw1 HJ1 Hr1 Hf1 Hp1 Hio1 Hmo1 Hm1 HR1)|].
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & Hr2 & Hf2 & Hp2 & Hio2 & Hmo2 & Hm2 & HR2).
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|].
split; [intros r Hr0 Hn; rewrite (Hr2 r Hr0 ltac:(intros X; apply Hn; apply in_or_app; right; exact X));
  apply Hr1; [exact Hr0 | intros X; apply Hn; apply in_or_app; left; exact X]|].
split; [rewrite Hf2; exact Hf1|].
split; [eapply Permutation_trans; [exact Hp2 | exact Hp1]|].
split; [eapply same_io_trans; [exact Hio1 | exact Hio2]|].
split; [exact (mle_station MT Sc S1 S2 0 0 MTL Hmo1 Hmo2)|].
split; [intros a; rewrite (Hm2 a); exact (Hm1 a)|].
exact HR2.
Qed.
End seq.

End d.
End b.
