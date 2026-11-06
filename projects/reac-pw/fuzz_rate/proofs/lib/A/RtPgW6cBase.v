(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at at 28fdc66416e (the call of
   __asan_memcpy in the journal) restated as hd_memcpy with the wrapper's same_but_materialized kept in the post as
   same_io, and proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v at 9e73ed57244 (m2_img_zone, m2_cstr_kept, the .rodata
   zone of m2_szone) restated as hd_img_zone / hd_cstr_kept / hd_szone for the .rodata range only; the rest of the
   file is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v, with its module paths and module names changed; 428 of its 517 lines of code are new or changed and 925 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgW6cTail.v, with its module paths, module names, addresses and numbers changed; 138 of its 192 lines of code are new or changed and 463 lines of the source are left out. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): the BLOCK STATEMENTS of the
   walk piece "ent_build C" of LLVMFuzzerTestOneInput (0x80714): ent_build's cases 6, 7 and 8 (pod.h:340-366), from
   their switch entries D6 0x81880 / D7 0x81754 / D8 0x818d0 to the join J 0x81e00 (the inlined pod_write_ent).
   Statement text only: no function is proved here (kind: segment lemma).

   WHY BLOCKS. Each case calls one intrinsic (__asan_memcpy for cases 6 and 7, __asan_memset for case 8), so a case
   is a HEAD (one engine run from the case entry to the intrinsic's entry, with the `jal`'s return address in ra) and
   a TAIL (the intrinsic, the kernel's aintrin_realizes, then the jump to J). The heads are stated here over the
   machine state at the case entry (registers, the 8-byte cells of the real frame they read, the input bytes) in the
   shape of a callee contract, the tails over the state at the intrinsic's entry, so that each is proved alone; the
   piece (lib/A/RtPgW6c.v) chains them from RtPgSeg's cut D to its cut J.

   THE CODE (listing of image A; s1 = R the real frame's base, s2 = SHADOW_OFF, s9 = c the cursor after the kind
   byte, s8 = |r| what is left after it, a4 = c - 1 the kind byte's address, a5 = |r| + 1; [R+0x138] = F + 0xf0 the
   address of e, [R+0x108] = F + 0xf8 the address of e.body, [R+0xe8] = vb the shadow address of &pp->len,
   [R+0x10] = 0x15555556 the `% 12u` multiplier):
   case 6 (pod.h:340-348) 0x81880  beqz s8 -> 0x81b24 (no byte: a0 := 5, a2 := 8, a1 := 0, s6 := [R+0xe8],
                                   -> 0x81cb0); the check of s9 (NE-SLOW, slow block 0x821b8), s6 := [R+0xe8];
                                   lbu a2 (= t); a0 := t[t & 3] (.rodata 0x211c0, the check NE-SLOW 0x821c4);
                                   t & 3 = 2: a3 := 4 (0x81c90), else a3 := 8; 0x81c94 a1 := a5 - 2, s9 := a4 + 2,
                                   lw a0 (the type), a2 := (t & 3 = 3) ? 0 : a3 (the size); 0x81cb0 e.type, e.size
                                   := a0, a2; a2 := min(a2, a1); 0x81cc4 a3 := s9 + a2, s8 := a1 - a2,
                                   a0 := [R+0x108], a1 := s9, s9 := a3; 0x81cd8 jal __asan_memcpy (0x51860);
                                   0x81cdc j J.
   case 7 (pod.h:350-357) 0x81754  beqz s8 -> 0x81a1c (no byte: a1 := 0, a2 := 0, s6 := [R+0xe8], -> 0x81c7c);
                                   the check of s9 (NE-SLOW, 0x82194); lbu a1 (= t); s9 := a4 + 2; a1 := t mod 21
                                   (the multiply by 0x87, 0x81770 .. 0x817a0); e.type := a1; s6 := [R+0xe8];
                                   a5 = 2 (one byte left): a1 := 0, a2 := 0 -> 0x81c7c; else 0x81c44 the check of
                                   s9 (NE-SLOW, 0x82208), lbu a2 (= s), a1 := a5 - 3, s9 := a4 + 3, a2 := s mod 12
                                   (the multiply by [R+0x10]); 0x81c7c e.size := a2; a2 := min(a2, a1); 0x81cc4 as
                                   case 6.
   case 8 (pod.h:359-366) 0x818d0  beqz s8 -> 0x81bd4 (no byte: s6 := 0, a2 := 0, e.type := 4, a3 := [R+0x108],
                                   -> 0x81bec); the check of s9 (NE-SLOW, 0x82154); lbu a1 (= t); a0 := &t.9[t & 3]
                                   (.rodata 0x211e0, the check NE-SLOW 0x82160); lw a0; s6 := a5 - 2;
                                   s9 := a4 + 2; e.type := a0; a3 := [R+0x108]; t & 3 = 3 (POD_STRING) or s6 = 0:
                                   a2 := 0 (0x8198c); else the check of s9 (NE-SLOW, 0x82214), lbu a2 (= s),
                                   s6 := a5 - 3, s9 := a4 + 3, a2 := s & 3; 0x81bec e.size := a2, a0 := a3,
                                   a1 := 0, 0x81bfc jal __asan_memset (0x51cfc); 0x81c00 s8 := s6;
                                   0x81c04 s6 := [R+0xe8]; j J.
   e = F + 0xf0 lies in the frame for locals (the side-stack frame (3, pos)); its bytes are 104 zeros at the case
   entry (the dispatch's memset). The cells the heads read, R + 0x10, 0xe8 .. 0x110 and 0x138, lie in the build's
   write ranges (RtPgImgA hi_w1), which the input avoids (rate_build_contract), so the input byte, the cells, e and
   the tables are disjoint regions of one engine state. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Tables.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgMem RtPgSteps RtPgSeg.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* image A's loaded segments *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ======================================== the pcs ======================================== *)
Definition W6C_D6 : Z := 0x81880.     (* case 6's entry, `beqz s8` *)
Definition W6C_D7 : Z := 0x81754.     (* case 7's entry, `beqz s8` *)
Definition W6C_D8 : Z := 0x818d0.     (* case 8's entry, `beqz s8` *)
Definition W6C_J : Z := 0x81e00.      (* the join: the inlined pod_write_ent begins (RtPgSeg RS_J) *)
Definition W6C_CPY : Z := 0x51860.    (* __asan_memcpy, the `jal` target at 0x81cd8 *)
Definition W6C_SET : Z := 0x51cfc.    (* __asan_memset, the `jal` target at 0x81bfc *)
Definition W6C_RCPY : Z := 0x81cdc.   (* after the memcpy: `j J` *)
Definition W6C_RSET : Z := 0x81c00.   (* after the memset: `mv s8,s6`; `ld s6,0xe8(s1)`; `j J` *)
(* the two tables the cases read (registered globals, .rodata, 16 bytes each): case 6's t[] = {LONG, DOUBLE, ID,
   NONE} and case 8's t[] = {INT, FLOAT, BOOL, STRING} (Pod/Tables.v t6, t8) *)
Definition W6C_T6 : Z := 0x211c0.
Definition W6C_T8 : Z := 0x211e0.

Lemma w6c_pcs_seg : RS_D6 = W6C_D6 /\ RS_D7 = W6C_D7 /\ RS_D8 = W6C_D8 /\ RS_J = W6C_J.
Proof. repeat split; reflexivity. Qed.

(* ======================================== the code table ========================================
   Every instruction word of [0x81754, 0x81ce4) (the three cases' fast paths and the two tails, with the other cases'
   words between them) and of [0x82154, 0x82220) (the slow blocks of the cases' seven checks). The report calls past
   0x833dc are never stepped. Precomputed once. *)
Definition W6C_TLO : Z := 0x81754.
Definition W6C_TN : nat := 356.
Definition W6C_SLO : Z := 0x82154.
Definition W6C_SN : nat := 51.
Definition w6c_tbl : ctable := Eval vm_compute in build_table rsegs W6C_TLO W6C_TN (build_table rsegs W6C_SLO W6C_SN TEmpty).
Lemma w6c_tbl_ok : table_ok rsegs w6c_tbl.
Proof.
assert (H : table_ok rsegs (build_table rsegs W6C_TLO W6C_TN (build_table rsegs W6C_SLO W6C_SN TEmpty))).
{ apply build_table_ok; [unfold W6C_TLO; lia|]. apply build_table_ok0. unfold W6C_SLO; lia. }
assert (E : build_table rsegs W6C_TLO W6C_TN (build_table rsegs W6C_SLO W6C_SN TEmpty) = w6c_tbl) by (vm_compute; reflexivity).
rewrite E in H. exact H.
Qed.

(* ======================================== the model's values ======================================== *)
(* case 6: the type t6[t mod 4] and its size (Model.ent_build) *)
Definition w6c_ty6 (t : Z) : Z := nth (Z.to_nat (t mod 4)) Tables.t6 0.
Definition w6c_sz6 (ty : Z) : Z := if ty =? POD_NONE then 0 else if ty =? POD_ID then 4 else 8.
(* case 8: the type t8[t mod 4]; a String has size 0 and reads no second byte *)
Definition w6c_ty8 (t : Z) : Z := nth (Z.to_nat (t mod 4)) Tables.t8 0.
(* case 8's size and what is left after it, from what is left after the type byte *)
Definition w6c_sz8 (ty : Z) (r1 : list byte) : Z * list byte :=
if ty =? POD_STRING then (0, r1) else (fst (fuzz_u8 r1) mod 4, snd (fuzz_u8 r1)).

(* the registers a case writes before its intrinsic (cases 6 and 7: a0 .. a3, s6, s8, s9 and ra; case 8: a0 .. a3, s6,
   s9 and ra) *)
Definition w6c_clob67 : list (bv 5) := [1; 10; 11; 12; 13; 22; 24; 25]%bv.
Definition w6c_clob8 : list (bv 5) := [1; 10; 11; 12; 13; 22; 25]%bv.
(* the registers RtPgSeg's cut J keeps from the case entry (rs_Rc0: s0 s1 s2 s3 s4 s5 s7; s10; s11) and sp, gp, tp *)
Definition w6c_keep : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 26; 27]%bv.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.

(* ===================== the context every block runs in =====================
   The harness's journal from the segment's start; the real frame [R, R + 0x1e0) 16-aligned inside the journal's
   stack window with the callees' stack below it and above the high-memory boundary; the frame for locals F = the
   side-stack frame (3, pos) the harness holds, 32-aligned in the application's memory; the read-only segments as in
   the image. *)
Definition w6c_geo (STK sp0 : Z) (own : list (Z * Z)) (lyc : alayout) (R F pos : Z) : Prop :=
R mod 16 = 0 /\ sp0 - STK <= R - T_SEG_STK /\ R + 0x1e0 <= sp0 /\ kHighMemBeg <= R - T_SEG_STK /\
In (3, pos) own /\ F = frame_addr lyc 3 pos /\ in_app F 512 /\ F mod 32 = 0.
Definition w6c_ctx (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z)
(lyc : alayout) (Sc : astate) (W : world rsegs) (memc : word -> option byte) (mdc : Model) (R F pos : Z) : Prop :=
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
w6c_geo STK sp0 own lyc R F pos /\ rom_view rsegs W memc.

(* the registers at a case entry (RtPgSeg rs_L_D): sp = s1 = R, gp, tp, s2 = SHADOW_OFF, s9 = c, s8 = n = |r|,
   a4 = c - 1, a5 = n + 1 *)
Definition w6c_regs (regs : bvmap 5 word) (R c n : Z) : Prop :=
getr regs 2 = w64 R /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\ getr regs 9 = w64 R /\
getr regs 18 = w64 SHADOW_OFF /\ getr regs 25 = w64 c /\ getr regs 24 = w64 n /\
getr regs 14 = w64 (c - 1) /\ getr regs 15 = w64 (n + 1).

(* the real frame's cells the cases read (RtPgSeg rs_Kc) *)
Definition w6c_cells (W : world rsegs) (memc : word -> option byte) (R F vb : Z) : Prop :=
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 (F + 0xf0) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 (F + 0xf8) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe8) 8 vb /\ 0 <= vb < 2 ^ 64 /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x10) 8 0x15555556.

(* the input bytes r at the cursor c, as rate_build_contract gives them (bytes, shadow, hull, amem_range, bounds),
   outside the callees' stack, the build's write ranges in the real frame (RtPgImgA hi_w1) and e *)
Definition w6c_in (W : world rsegs) (memc : word -> option byte) (R F c : Z) (r : list byte) : Prop :=
rtm_bytes rsegs (w_H W) memc c r /\
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF c (Z.of_nat (length r)) /\
(0 < Z.of_nat (length r) -> shadow_hull_vis (aview rsegs (w_H W) memc) c (Z.of_nat (length r))) /\
0 < c - 1 /\ c + Z.of_nat (length r) <= 2 ^ 63 /\ amem_range c (Z.of_nat (length r)) /\
(forall a, c <= a < c + Z.of_nat (length r) ->
 ~ (R - T_SEG_STK <= a < R) /\ ~ (R + 0x10 <= a < R + 0x38) /\ ~ (R + 0x60 <= a < R + 0x120) /\
 ~ (R + 0x128 <= a < R + 0x140) /\ ~ (F + 0x20 <= a < F + 0x158)).

(* e's header bytes, the only bytes a head writes *)
Definition w6c_hdr_wr (F : Z) : Z -> Prop := fun a => F + 0xf0 <= a < F + 0xf8.

(* The post of a head: the intrinsic's entry pc with ra set, the world, layout and state as at the start, the
   journal at the run's memory, the I/O state, every register outside clob and every byte outside Wr kept, and Q. *)
Definition w6c_hpost (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z)
(lyc : alayout) (Sc : astate) (W : world rsegs) (memc : word -> option byte) (mdc : Model) (regs : bvmap 5 word)
(pc : Z) (clob : list (bv 5)) (Wr : Z -> Prop) (Q : bvmap 5 word -> (word -> option byte) -> Prop)
: world rsegs -> config -> Prop :=
fun W2 c2 => exists regs2 mem2 md2,
W2 = W /\ c2 = cfg_at rsegs pc regs2 mem2 md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\ same_io mdc md2 /\
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs2 r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a) /\
Q regs2 mem2.

(* ===================== the three heads ===================== *)
(* case 6: t = the first byte of r (0 if none) and r1 the rest, the type t6[t mod 4] and its size sz; the memcpy
   copies n = min(sz, |r1|) bytes from the cursor after t. At the memcpy's entry: ra = 0x81cdc, a0 = &e.body,
   a1 = the source, a2 = n, s6 = vb, s8 = |r1| - n and s9 = the source + n (both as after the call); e.type and
   e.size written. *)
Definition w6c_h6_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos c vb : Z) (r : list byte),
w6c_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
w6c_regs regs R c (Z.of_nat (length r)) -> w6c_cells W memc R F vb -> w6c_in W memc R F c r ->
rtm_bytes rsegs (w_H W) memc (F + 0xf0) (zeros 104) ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF W6C_T6 16 ->
SRr rsegs W (cfg_at rsegs W6C_D6 regs memc mdc)
(w6c_hpost STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs W6C_CPY w6c_clob67 (w6c_hdr_wr F)
(fun regs2 mem2 =>
 let t := fst (fuzz_u8 r) in let r1 := snd (fuzz_u8 r) in
 let ty := w6c_ty6 t in let sz := w6c_sz6 ty in
 let n := Z.min sz (Z.of_nat (length r1)) in
 let src := c + Z.of_nat (length r) - Z.of_nat (length r1) in
 getr regs2 1 = w64 W6C_RCPY /\ getr regs2 10 = w64 (F + 0xf8) /\ getr regs2 11 = w64 src /\
 getr regs2 12 = w64 n /\ getr regs2 22 = w64 vb /\ getr regs2 24 = w64 (Z.of_nat (length r1) - n) /\
 getr regs2 25 = w64 (src + n) /\
 val_mem rsegs (mrestrict (w_H W) mem2) (F + 0xf0) 4 ty /\
 val_mem rsegs (mrestrict (w_H W) mem2) (F + 0xf4) 4 sz)).

(* case 7: t and s the next two bytes (0 if none), r2 what is left after them; the type t mod 21 (written only when a
   byte is left; e's zeros give it otherwise) and the size s mod 12; the memcpy copies n = min(s mod 12, |r2|). *)
Definition w6c_h7_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos c vb : Z) (r : list byte),
w6c_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
w6c_regs regs R c (Z.of_nat (length r)) -> w6c_cells W memc R F vb -> w6c_in W memc R F c r ->
rtm_bytes rsegs (w_H W) memc (F + 0xf0) (zeros 104) ->
SRr rsegs W (cfg_at rsegs W6C_D7 regs memc mdc)
(w6c_hpost STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs W6C_CPY w6c_clob67 (w6c_hdr_wr F)
(fun regs2 mem2 =>
 let t := fst (fuzz_u8 r) in let r1 := snd (fuzz_u8 r) in
 let s := fst (fuzz_u8 r1) in let r2 := snd (fuzz_u8 r1) in
 let n := Z.min (s mod 12) (Z.of_nat (length r2)) in
 let src := c + Z.of_nat (length r) - Z.of_nat (length r2) in
 getr regs2 1 = w64 W6C_RCPY /\ getr regs2 10 = w64 (F + 0xf8) /\ getr regs2 11 = w64 src /\
 getr regs2 12 = w64 n /\ getr regs2 22 = w64 vb /\ getr regs2 24 = w64 (Z.of_nat (length r2) - n) /\
 getr regs2 25 = w64 (src + n) /\
 val_mem rsegs (mrestrict (w_H W) mem2) (F + 0xf0) 4 (t mod 21) /\
 val_mem rsegs (mrestrict (w_H W) mem2) (F + 0xf4) 4 (s mod 12))).

(* case 8: t the first byte, the type t8[t mod 4]; a String has size 0, any other type the size s mod 4 of the next
   byte s; r' what is left. At the memset's entry: ra = 0x81c00, a0 = &e.body, a1 = 0, a2 = the size, s6 = |r'| and
   s9 = the cursor after the reads (s8 is set after the call); e.type and e.size written. *)
Definition w6c_h8_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos c vb : Z) (r : list byte),
w6c_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
w6c_regs regs R c (Z.of_nat (length r)) -> w6c_cells W memc R F vb -> w6c_in W memc R F c r ->
rtm_bytes rsegs (w_H W) memc (F + 0xf0) (zeros 104) ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF W6C_T8 16 ->
SRr rsegs W (cfg_at rsegs W6C_D8 regs memc mdc)
(w6c_hpost STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs W6C_SET w6c_clob8 (w6c_hdr_wr F)
(fun regs2 mem2 =>
 let t := fst (fuzz_u8 r) in let r1 := snd (fuzz_u8 r) in
 let ty := w6c_ty8 t in let sz := fst (w6c_sz8 ty r1) in let r' := snd (w6c_sz8 ty r1) in
 getr regs2 1 = w64 W6C_RSET /\ getr regs2 10 = w64 (F + 0xf8) /\ getr regs2 11 = w64 0 /\
 getr regs2 12 = w64 sz /\ getr regs2 22 = w64 (Z.of_nat (length r')) /\
 getr regs2 25 = w64 (c + Z.of_nat (length r) - Z.of_nat (length r')) /\
 val_mem rsegs (mrestrict (w_H W) mem2) (F + 0xf0) 4 ty /\
 val_mem rsegs (mrestrict (w_H W) mem2) (F + 0xf4) 4 sz)).

(* ===================== the join's state, and the two tails ===================== *)
(* At J: the journal (no event), the I/O state, the registers RtPgSeg's cut J keeps, s6 = vb, s8 = what is left,
   s9 = the cursor, every byte outside the callee's stack [R - ESTACK, R) and e (F + 0xf0, 104 bytes) kept, and e's
   bytes. *)
Definition w6c_jpost (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z)
(lyc : alayout) (Sc : astate) (W : world rsegs) (memc : word -> option byte) (mdc : Model) (regs : bvmap 5 word)
(R F : Z) (ed : ent) (cur' nl' vb : Z) : world rsegs -> config -> Prop :=
fun W2 c2 => exists regs2 mem2 md2,
W2 = W /\ c2 = cfg_at rsegs W6C_J regs2 mem2 md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\ same_io mdc md2 /\
(forall r, In r w6c_keep -> getr regs2 r = getr regs r) /\
getr regs2 22 = w64 vb /\ getr regs2 24 = w64 nl' /\ getr regs2 25 = w64 cur' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (R - ESTACK <= a < R) -> ~ (F + 0xf0 <= a < F + 0x158) ->
 aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a) /\
rtm_bytes rsegs (w_H W) mem2 (F + 0xf0) (ent_mem ed).

(* cases 6 and 7 from the memcpy's entry: memcpy(e.body, src, |bs|), then `j J` (0x81cdc) *)
Definition w6c_tail_cpy_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos ty sz src : Z)
(bs : list byte) (cur' nl' vb : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
w6c_geo STK sp0 own lyc R F pos ->
getr regs 1 = w64 W6C_RCPY -> getr regs 2 = w64 R -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 (F + 0xf8) -> getr regs 11 = w64 src -> getr regs 12 = w64 (Z.of_nat (length bs)) ->
getr regs 22 = w64 vb -> getr regs 24 = w64 nl' -> getr regs 25 = w64 cur' ->
(length bs <= Z.to_nat sz)%nat -> 0 <= sz <= 96 ->
rtm_bytes rsegs (w_H W) memc (F + 0xf0) (le32 ty ++ le32 sz ++ zeros 96) ->
rtm_bytes rsegs (w_H W) memc src bs ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF src (Z.of_nat (length bs)) ->
(0 < Z.of_nat (length bs) -> shadow_hull_vis (aview rsegs (w_H W) memc) src (Z.of_nat (length bs))) ->
amem_range src (Z.of_nat (length bs)) -> 0 <= src -> src + Z.of_nat (length bs) <= 2 ^ 63 ->
(forall a, src <= a < src + Z.of_nat (length bs) -> ~ (R - ESTACK <= a < R) /\ ~ (F + 0xf0 <= a < F + 0x158)) ->
rt_fsh rsegs (w_H W) memc F rs_PJ ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 W6C_CPY) memc (seg_rom rsegs)) mdc)
(w6c_jpost STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F
 (Ent ty sz (bs ++ zeros (Z.to_nat sz - length bs))) cur' nl' vb).

(* case 8 from the memset's entry: memset(e.body, 0, sz), then s8 := s6, s6 := [R+0xe8], `j J` (0x81c00 .. 0x81c08) *)
Definition w6c_tail_set_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos ty sz cur' nl' vb : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
w6c_geo STK sp0 own lyc R F pos ->
getr regs 1 = w64 W6C_RSET -> getr regs 2 = w64 R -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 9 = w64 R -> getr regs 10 = w64 (F + 0xf8) -> getr regs 11 = w64 0 -> getr regs 12 = w64 sz ->
getr regs 22 = w64 nl' -> getr regs 25 = w64 cur' ->
0 <= sz <= 96 -> 0 <= vb < 2 ^ 64 ->
rtm_bytes rsegs (w_H W) memc (F + 0xf0) (le32 ty ++ le32 sz ++ zeros 96) ->
rt_fsh rsegs (w_H W) memc F rs_PJ ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe8) 8 vb ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 W6C_SET) memc (seg_rom rsegs)) mdc)
(w6c_jpost STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F (Ent ty sz (zeros (Z.to_nat sz))) cur' nl' vb).

End d.
End b.
