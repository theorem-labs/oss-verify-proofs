(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at at 28fdc66416e (the call of
   __asan_memcpy in the journal) restated as hd_memcpy with the wrapper's same_but_materialized kept in the post as
   same_io, and proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v at 9e73ed57244 (m2_img_zone, m2_cstr_kept, the .rodata
   zone of m2_szone) restated as hd_img_zone / hd_cstr_kept / hd_szone for the .rodata range only; the rest of the
   file is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v, with its module paths and module names changed; 428 of its 517 lines of code are new or changed and 925 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgW6cTail.v, with its module paths, module names, addresses and numbers changed; 138 of its 192 lines of code are new or changed and 463 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgW6cBase.v, with its module names, addresses and numbers changed; 107 of its 198 lines of code are new or changed and 101 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW6cBase.v at cb9cdc023f20 for the same
   unit's image B (fuzz_rate.asan-ubsan): image B's pcs, code table, registers and real-frame cells; the pod is e62
   (F + 0x210) instead of e (F + 0xf0); the intrinsics are image B's __asan_memcpy 0x518b8 and __asan_memset 0x51d54;
   the frame for locals is class 4 (1024 bytes) and the real frame 0x220 bytes; the join's state names t1, s2, s6 and
   s10 and the tails read s2 back from the cell R + 0x158; the input avoids image B's first write ranges. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): the BLOCK STATEMENTS of the
   walk piece "ent_build C" of LLVMFuzzerTestOneInput (0x8076c): ent_build's cases 6, 7 and 8 (pod.h:340-366), from
   their switch entries D6 0x819a0 / D7 0x81888 / D8 0x819f0 to the join J 0x820dc (the capacity guard before the call
   pod_write_ent(pp, e62)). Statement text only: no function is proved here (kind: segment lemma).

   WHY BLOCKS. Each case calls one intrinsic (__asan_memcpy for cases 6 and 7, __asan_memset for case 8), so a case
   is a HEAD (one engine run from the case entry to the intrinsic's entry, with the `jal`'s return address in ra) and
   a TAIL (the intrinsic, the kernel's aintrin_realizes, then the jump to J). The heads are stated here over the
   machine state at the case entry (registers, the 8-byte cells of the real frame they read, the input bytes) in the
   shape of a callee contract, the tails over the state at the intrinsic's entry, so that each is proved alone; the
   piece (lib/AU/RtPgW6cB.v) chains them from RtPgSegB's cut D to its cut J.

   THE CODE (listing of image B; s1 = R the real frame's base, s4 = SHADOW_OFF, s2 = c the cursor after the kind
   byte, s6 = |r| what is left after it, s10 = c - 1 the kind byte's address, t1 = |r| + 1, a6 = 1 the left side of
   the pointer-overflow tests; [R+0x150] = F + 0x210 the address of e62, [R+0x130] = F + 0x218 the address of
   e62.body, [R+0x158] = pp + 0x4000 = &pp->len, [R+0x0] = 0x15555556 the `% 12u` multiplier; every `j 0x83098` is
   a UBSan trap branch to the `unimp`):
   case 6 (pod.h:340-348) 0x819a0  beqz s6 -> 0x81cf0 (no byte: a1 := 0, a2 := 0, a0 := 0x211c0, -> 0x81d00);
                                   trap s2 + 1 (0x819a8); the check of s2 (NE-SLOW, slow block 0x822e0); lbu a2
                                   (= t); a0 := 0x211c0; a2 := t & 3; a3 := 4 (t & 3); trap ~a0 >= a3 (0x819d8);
                                   a1 := t1 - 2 (= |r1|), s2 := s10 + 2, a0 := a0 + a3; 0x81d00 the check of a0, 4
                                   bytes (NE-SLOW, 0x82250), s6 := [R+0x150]; lw a0 (the type); e62.type := a0;
                                   a0 := (t & 3 = 2) ? 4 : 8; a2 := (t & 3 = 3) ? 0 : a0 (the size); e62.size := a2;
                                   a2 := min(a2, a1); trap ~s2 >= a2 (0x81d50); -> 0x81f2c.
   case 7 (pod.h:350-357) 0x81888  beqz s6 -> 0x81b64 (no byte: a1 := 0, a2 := 0, s6 := [R+0x150], -> 0x81f14);
                                   trap s2 + 1 (0x81890); the check of s2 (NE-SLOW, 0x822bc), s6 := [R+0x150]; lbu
                                   a1 (= t); s2 := s10 + 2; a1 := t mod 21 (the multiply by 0x87, 0x818b4 ..
                                   0x818e4); e62.type := a1; t1 = 2 (one byte left): a1 := 0, a2 := 0 -> 0x81f14;
                                   else 0x81ed0 trap s2 + 1, the check of s2 (NE-SLOW, 0x82320), lbu a2 (= s),
                                   a1 := t1 - 3, s2 := s10 + 3, a2 := s mod 12 (the multiply by [R+0x0]); 0x81f14
                                   e62.size := a2; a2 := min(a2, a1); trap ~s2 >= a2 (0x81f24).
   cases 6, 7: 0x81f2c  s10 := s2 + a2; s8 := a1 - a2; a0 := [R+0x130]; a1 := s2; 0x81f3c jal __asan_memcpy
                        (0x518b8); 0x81f40 t1 := s8; j 0x820d8; 0x820d8 s2 := [R+0x158]; J.
   case 8 (pod.h:359-366) 0x819f0  beqz s6 -> 0x81d60 (no byte: a2 := 0, e62.type := 4, -> 0x81d70); trap s2 + 1
                                   (0x819f8); the check of s2 (NE-SLOW, 0x8227c); lbu a1 (= t); a0 := 0x211e0;
                                   a1 := t & 3; a2 := 4 (t & 3); trap ~a0 >= a2 (0x81a28); a0 := a0 + a2; the
                                   check of a0, 4 bytes (NE-SLOW, 0x82288); lw a0 (the type); s6 := t1 - 2;
                                   s2 := s10 + 2; e62.type := a0; t & 3 = 3 (POD_STRING) or s6 = 0: a2 := 0
                                   (0x81afc); else trap s2 + 1 (0x81a68), the check of s2 (NE-SLOW, 0x8232c), lbu a2
                                   (= s), s6 := t1 - 3, s2 := s10 + 3, a2 := s & 3; 0x81d70 s10 := [R+0x150];
                                   e62.size := a2; a0 := [R+0x130]; a1 := 0; 0x81d80 jal __asan_memset (0x51d54);
                                   0x81d84 t1 := s6; s6 := s10; j 0x820d4; 0x820d4 s10 := s2; s2 := [R+0x158]; J.
   e62 = F + 0x210 lies in the frame for locals (the side-stack frame (4, pos)); its bytes are 104 zeros at the case
   entry (the dispatch's memset). The cells the heads read, R + 0x0, 0x130 and 0x150, lie in the build's write ranges
   (RtPgImgB hi_w1), which the input avoids (rate_build_contract), so the input bytes, the cells, e62 and the tables
   are disjoint regions of one engine state. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgMemB RtPgStepsB RtPgSegB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* image B's loaded segments *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ======================================== the pcs ======================================== *)
Definition W6CB_D6 : Z := 0x819a0.     (* case 6's entry, `beqz s6` *)
Definition W6CB_D7 : Z := 0x81888.     (* case 7's entry, `beqz s6` *)
Definition W6CB_D8 : Z := 0x819f0.     (* case 8's entry, `beqz s6` *)
Definition W6CB_J : Z := 0x820dc.      (* the join: `ld a0,0x170(s1)`, the capacity guard (RtPgSegB RSB_J) *)
Definition W6CB_CPY : Z := 0x518b8.    (* __asan_memcpy, the `jal` target at 0x81f3c *)
Definition W6CB_SET : Z := 0x51d54.    (* __asan_memset, the `jal` target at 0x81d80 *)
Definition W6CB_RCPY : Z := 0x81f40.   (* after the memcpy: `mv t1,s8`; `j 0x820d8`; `ld s2,0x158(s1)` *)
Definition W6CB_RSET : Z := 0x81d84.   (* after the memset: `mv t1,s6`; `mv s6,s10`; `j 0x820d4`; `mv s10,s2`;
                                          `ld s2,0x158(s1)` *)
(* the two tables the cases read (registered globals, .rodata, 16 bytes each): case 6's t[] = {LONG, DOUBLE, ID,
   NONE} and case 8's t[] = {INT, FLOAT, BOOL, STRING} (Pod/Tables.v t6, t8) *)
Definition W6CB_T6 : Z := 0x211c0.
Definition W6CB_T8 : Z := 0x211e0.

Lemma w6cb_pcs_seg : RSB_D6 = W6CB_D6 /\ RSB_D7 = W6CB_D7 /\ RSB_D8 = W6CB_D8 /\ RSB_J = W6CB_J.
Proof. repeat split; reflexivity. Qed.

(* ======================================== the code table ========================================
   Every instruction word of [0x81888, 0x820dc) (the three cases' fast paths, their trap tests and the two tails, with
   the other cases' words between them) and of [0x82250, 0x82338) (the slow blocks of the cases' seven checks). The
   trap target 0x83098 and the report calls past it are never stepped. Precomputed once. *)
Definition W6CB_TLO : Z := 0x81888.
Definition W6CB_TN : nat := 533.
Definition W6CB_SLO : Z := 0x82250.
Definition W6CB_SN : nat := 58.
Definition w6cb_tbl : ctable := Eval vm_compute in build_table rsegs W6CB_TLO W6CB_TN (build_table rsegs W6CB_SLO W6CB_SN TEmpty).
Lemma w6cb_tbl_ok : table_ok rsegs w6cb_tbl.
Proof.
assert (H : table_ok rsegs (build_table rsegs W6CB_TLO W6CB_TN (build_table rsegs W6CB_SLO W6CB_SN TEmpty))).
{ apply build_table_ok; [unfold W6CB_TLO; lia|]. apply build_table_ok0. unfold W6CB_SLO; lia. }
assert (E : build_table rsegs W6CB_TLO W6CB_TN (build_table rsegs W6CB_SLO W6CB_SN TEmpty) = w6cb_tbl) by (vm_compute; reflexivity).
rewrite E in H. exact H.
Qed.

(* ======================================== the model's values ======================================== *)
(* case 6: the type t6[t mod 4] and its size (Model.ent_build) *)
Definition w6cb_ty6 (t : Z) : Z := nth (Z.to_nat (t mod 4)) Tables.t6 0.
Definition w6cb_sz6 (ty : Z) : Z := if ty =? POD_NONE then 0 else if ty =? POD_ID then 4 else 8.
(* case 8: the type t8[t mod 4]; a String has size 0 and reads no second byte *)
Definition w6cb_ty8 (t : Z) : Z := nth (Z.to_nat (t mod 4)) Tables.t8 0.
(* case 8's size and what is left after it, from what is left after the type byte *)
Definition w6cb_sz8 (ty : Z) (r1 : list byte) : Z * list byte :=
if ty =? POD_STRING then (0, r1) else (fst (fuzz_u8 r1) mod 4, snd (fuzz_u8 r1)).

(* the registers a case writes before its intrinsic (cases 6 and 7: ra, a0 .. a3, s2, s6, s8 and s10; case 8: ra,
   a0 .. a3, s2, s6 and s10) *)
Definition w6cb_clob67 : list (bv 5) := [1; 10; 11; 12; 13; 18; 22; 24; 26]%bv.
Definition w6cb_clob8 : list (bv 5) := [1; 10; 11; 12; 13; 18; 22; 26]%bv.
(* the registers RtPgSegB's cut J keeps from the case entry (rsb_Rc0: s0 s1 s3 s4 s5 s7 s11) and sp, gp, tp *)
Definition w6cb_keep : list (bv 5) := [2; 3; 4; 8; 9; 19; 20; 21; 23; 27]%bv.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.

(* ===================== the context every block runs in =====================
   The harness's journal from the segment's start; the real frame [R, R + 0x220) 16-aligned inside the journal's
   stack window with the callees' stack below it and above the high-memory boundary; the frame for locals F = the
   side-stack frame (4, pos) the harness holds, 32-aligned in the application's memory; the read-only segments as in
   the image. *)
Definition w6cb_geo (STK sp0 : Z) (own : list (Z * Z)) (lyc : alayout) (R F pos : Z) : Prop :=
R mod 16 = 0 /\ sp0 - STK <= R - T_SEG_STK /\ R + 0x220 <= sp0 /\ kHighMemBeg <= R - T_SEG_STK /\
In (4, pos) own /\ F = frame_addr lyc 4 pos /\ in_app F 1024 /\ F mod 32 = 0.
Definition w6cb_ctx (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z)
(lyc : alayout) (Sc : astate) (W : world rsegs) (memc : word -> option byte) (mdc : Model) (R F pos : Z) : Prop :=
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
w6cb_geo STK sp0 own lyc R F pos /\ rom_view rsegs W memc.

(* the registers at a case entry (RtPgSegB rsb_L_D): sp = s1 = R, gp, tp, s4 = SHADOW_OFF, s2 = c, s6 = n = |r|,
   s10 = c - 1, t1 = n + 1, a6 = 1 *)
Definition w6cb_regs (regs : bvmap 5 word) (R c n : Z) : Prop :=
getr regs 2 = w64 R /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\ getr regs 9 = w64 R /\
getr regs 20 = w64 SHADOW_OFF /\ getr regs 18 = w64 c /\ getr regs 22 = w64 n /\
getr regs 26 = w64 (c - 1) /\ getr regs 6 = w64 (n + 1) /\ getr regs 16 = w64 1.

(* the real frame's cells the cases read (RtPgSegB rsb_Kc) *)
Definition w6cb_cells (W : world rsegs) (memc : word -> option byte) (R F : Z) : Prop :=
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x150) 8 (F + 0x210) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 (F + 0x218) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x0) 8 0x15555556.

(* the input bytes r at the cursor c, as rate_build_contract gives them (bytes, shadow, hull, amem_range, bounds),
   outside the callees' stack and the build's write ranges in the real frame and the frame for locals (RtPgImgB
   hi_w1) *)
Definition w6cb_in (W : world rsegs) (memc : word -> option byte) (R F c : Z) (r : list byte) : Prop :=
rtmb_bytes rsegs (w_H W) memc c r /\
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF c (Z.of_nat (length r)) /\
(0 < Z.of_nat (length r) -> shadow_hull_vis (aview rsegs (w_H W) memc) c (Z.of_nat (length r))) /\
0 < c - 1 /\ c + Z.of_nat (length r) <= 2 ^ 63 /\ amem_range c (Z.of_nat (length r)) /\
(forall a, c <= a < c + Z.of_nat (length r) ->
 ~ (R - T_SEG_STK <= a < R) /\ ~ (R + 0x0 <= a < R + 0x30) /\ ~ (R + 0x58 <= a < R + 0x148) /\
 ~ (R + 0x150 <= a < R + 0x180) /\ ~ (R + 0x198 <= a < R + 0x1b8) /\ ~ (F + 0x20 <= a < F + 0x278)).

(* e62's header bytes, the only bytes a head writes *)
Definition w6cb_hdr_wr (F : Z) : Z -> Prop := fun a => F + 0x210 <= a < F + 0x218.

(* The post of a head: the intrinsic's entry pc with ra set, the world, layout and state as at the start, the
   journal at the run's memory, the I/O state, every register outside clob and every byte outside Wr kept, and Q. *)
Definition w6cb_hpost (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
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
   copies n = min(sz, |r1|) bytes from the cursor after t. At the memcpy's entry: ra = 0x81f40, a0 = &e62.body,
   a1 = the source, a2 = n, s6 = &e62, s8 = |r1| - n and s10 = the source + n (both as after the call); e62.type and
   e62.size written. *)
Definition w6cb_h6_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos c : Z) (r : list byte),
w6cb_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
w6cb_regs regs R c (Z.of_nat (length r)) -> w6cb_cells W memc R F -> w6cb_in W memc R F c r ->
rtmb_bytes rsegs (w_H W) memc (F + 0x210) (zeros 104) ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF W6CB_T6 16 ->
SRr rsegs W (cfg_at rsegs W6CB_D6 regs memc mdc)
(w6cb_hpost STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs W6CB_CPY w6cb_clob67 (w6cb_hdr_wr F)
(fun regs2 mem2 =>
 let t := fst (fuzz_u8 r) in let r1 := snd (fuzz_u8 r) in
 let ty := w6cb_ty6 t in let sz := w6cb_sz6 ty in
 let n := Z.min sz (Z.of_nat (length r1)) in
 let src := c + Z.of_nat (length r) - Z.of_nat (length r1) in
 getr regs2 1 = w64 W6CB_RCPY /\ getr regs2 10 = w64 (F + 0x218) /\ getr regs2 11 = w64 src /\
 getr regs2 12 = w64 n /\ getr regs2 22 = w64 (F + 0x210) /\ getr regs2 24 = w64 (Z.of_nat (length r1) - n) /\
 getr regs2 26 = w64 (src + n) /\
 val_mem rsegs (mrestrict (w_H W) mem2) (F + 0x210) 4 ty /\
 val_mem rsegs (mrestrict (w_H W) mem2) (F + 0x214) 4 sz)).

(* case 7: t and s the next two bytes (0 if none), r2 what is left after them; the type t mod 21 (written only when a
   byte is left; e62's zeros give it otherwise) and the size s mod 12; the memcpy copies n = min(s mod 12, |r2|). *)
Definition w6cb_h7_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos c : Z) (r : list byte),
w6cb_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
w6cb_regs regs R c (Z.of_nat (length r)) -> w6cb_cells W memc R F -> w6cb_in W memc R F c r ->
rtmb_bytes rsegs (w_H W) memc (F + 0x210) (zeros 104) ->
SRr rsegs W (cfg_at rsegs W6CB_D7 regs memc mdc)
(w6cb_hpost STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs W6CB_CPY w6cb_clob67 (w6cb_hdr_wr F)
(fun regs2 mem2 =>
 let t := fst (fuzz_u8 r) in let r1 := snd (fuzz_u8 r) in
 let s := fst (fuzz_u8 r1) in let r2 := snd (fuzz_u8 r1) in
 let n := Z.min (s mod 12) (Z.of_nat (length r2)) in
 let src := c + Z.of_nat (length r) - Z.of_nat (length r2) in
 getr regs2 1 = w64 W6CB_RCPY /\ getr regs2 10 = w64 (F + 0x218) /\ getr regs2 11 = w64 src /\
 getr regs2 12 = w64 n /\ getr regs2 22 = w64 (F + 0x210) /\ getr regs2 24 = w64 (Z.of_nat (length r2) - n) /\
 getr regs2 26 = w64 (src + n) /\
 val_mem rsegs (mrestrict (w_H W) mem2) (F + 0x210) 4 (t mod 21) /\
 val_mem rsegs (mrestrict (w_H W) mem2) (F + 0x214) 4 (s mod 12))).

(* case 8: t the first byte, the type t8[t mod 4]; a String has size 0, any other type the size s mod 4 of the next
   byte s; r' what is left. At the memset's entry: ra = 0x81d84, a0 = &e62.body, a1 = 0, a2 = the size,
   s2 = the cursor after the reads, s6 = |r'| and s10 = &e62; e62.type and e62.size written. *)
Definition w6cb_h8_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos c : Z) (r : list byte),
w6cb_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
w6cb_regs regs R c (Z.of_nat (length r)) -> w6cb_cells W memc R F -> w6cb_in W memc R F c r ->
rtmb_bytes rsegs (w_H W) memc (F + 0x210) (zeros 104) ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF W6CB_T8 16 ->
SRr rsegs W (cfg_at rsegs W6CB_D8 regs memc mdc)
(w6cb_hpost STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs W6CB_SET w6cb_clob8 (w6cb_hdr_wr F)
(fun regs2 mem2 =>
 let t := fst (fuzz_u8 r) in let r1 := snd (fuzz_u8 r) in
 let ty := w6cb_ty8 t in let sz := fst (w6cb_sz8 ty r1) in let r' := snd (w6cb_sz8 ty r1) in
 getr regs2 1 = w64 W6CB_RSET /\ getr regs2 10 = w64 (F + 0x218) /\ getr regs2 11 = w64 0 /\
 getr regs2 12 = w64 sz /\ getr regs2 18 = w64 (c + Z.of_nat (length r) - Z.of_nat (length r')) /\
 getr regs2 22 = w64 (Z.of_nat (length r')) /\ getr regs2 26 = w64 (F + 0x210) /\
 val_mem rsegs (mrestrict (w_H W) mem2) (F + 0x210) 4 ty /\
 val_mem rsegs (mrestrict (w_H W) mem2) (F + 0x214) 4 sz)).

(* ===================== the join's state, and the two tails ===================== *)
(* At J: the journal (no event), the I/O state, the registers RtPgSegB's cut J keeps, t1 = what is left,
   s2 = vp (&pp->len, read back from R + 0x158), s6 = &e62, s10 = the cursor, every byte outside the callee's stack
   [R - ESTACK, R) and e62 (F + 0x210, 104 bytes) kept, and e62's bytes. *)
Definition w6cb_jpost (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z)
(lyc : alayout) (Sc : astate) (W : world rsegs) (memc : word -> option byte) (mdc : Model) (regs : bvmap 5 word)
(R F : Z) (ed : ent) (cur' nl' vp : Z) : world rsegs -> config -> Prop :=
fun W2 c2 => exists regs2 mem2 md2,
W2 = W /\ c2 = cfg_at rsegs W6CB_J regs2 mem2 md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\ same_io mdc md2 /\
(forall r, In r w6cb_keep -> getr regs2 r = getr regs r) /\
getr regs2 6 = w64 nl' /\ getr regs2 18 = w64 vp /\ getr regs2 22 = w64 (F + 0x210) /\ getr regs2 26 = w64 cur' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (R - ESTACK <= a < R) -> ~ (F + 0x210 <= a < F + 0x278) ->
 aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a) /\
rtmb_bytes rsegs (w_H W) mem2 (F + 0x210) (ent_mem ed).

(* cases 6 and 7 from the memcpy's entry: memcpy(e62.body, src, |bs|), then t1 := s8, `j 0x820d8`,
   s2 := [R+0x158] *)
Definition w6cb_tail_cpy_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos ty sz src : Z)
(bs : list byte) (cur' nl' vp : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
w6cb_geo STK sp0 own lyc R F pos ->
getr regs 1 = w64 W6CB_RCPY -> getr regs 2 = w64 R -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 9 = w64 R -> getr regs 10 = w64 (F + 0x218) -> getr regs 11 = w64 src ->
getr regs 12 = w64 (Z.of_nat (length bs)) ->
getr regs 22 = w64 (F + 0x210) -> getr regs 24 = w64 nl' -> getr regs 26 = w64 cur' ->
(length bs <= Z.to_nat sz)%nat -> 0 <= sz <= 96 ->
rtmb_bytes rsegs (w_H W) memc (F + 0x210) (le32 ty ++ le32 sz ++ zeros 96) ->
rtmb_bytes rsegs (w_H W) memc src bs ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF src (Z.of_nat (length bs)) ->
(0 < Z.of_nat (length bs) -> shadow_hull_vis (aview rsegs (w_H W) memc) src (Z.of_nat (length bs))) ->
amem_range src (Z.of_nat (length bs)) -> 0 <= src -> src + Z.of_nat (length bs) <= 2 ^ 63 ->
(forall a, src <= a < src + Z.of_nat (length bs) -> ~ (R - ESTACK <= a < R) /\ ~ (F + 0x210 <= a < F + 0x278)) ->
rt_fsh rsegs (w_H W) memc F rsb_PJ ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x158) 8 vp -> 0 <= vp < 2 ^ 64 ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 W6CB_CPY) memc (seg_rom rsegs)) mdc)
(w6cb_jpost STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F
 (Ent ty sz (bs ++ zeros (Z.to_nat sz - length bs))) cur' nl' vp).

(* case 8 from the memset's entry: memset(e62.body, 0, sz), then t1 := s6, s6 := s10, `j 0x820d4`, s10 := s2,
   s2 := [R+0x158] (0x81d84 .. 0x820d8) *)
Definition w6cb_tail_set_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos ty sz cur' nl' vp : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
w6cb_geo STK sp0 own lyc R F pos ->
getr regs 1 = w64 W6CB_RSET -> getr regs 2 = w64 R -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 9 = w64 R -> getr regs 10 = w64 (F + 0x218) -> getr regs 11 = w64 0 -> getr regs 12 = w64 sz ->
getr regs 18 = w64 cur' -> getr regs 22 = w64 nl' -> getr regs 26 = w64 (F + 0x210) ->
0 <= sz <= 96 ->
rtmb_bytes rsegs (w_H W) memc (F + 0x210) (le32 ty ++ le32 sz ++ zeros 96) ->
rt_fsh rsegs (w_H W) memc F rsb_PJ ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x158) 8 vp -> 0 <= vp < 2 ^ 64 ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 W6CB_SET) memc (seg_rom rsegs)) mdc)
(w6cb_jpost STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F (Ent ty sz (zeros (Z.to_nat sz))) cur' nl' vp).

End d.
End b.
