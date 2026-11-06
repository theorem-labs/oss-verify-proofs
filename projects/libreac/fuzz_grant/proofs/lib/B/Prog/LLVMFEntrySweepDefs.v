(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySweepDefs), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACeg.v. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/Prog/GrantEntrySweepDefs.v. *)
(* The SWEEP phase of fuzz_grant's entry function on IMAGE B (fuzz_grant.asan-ubsan):
   listing slots 0x954 .. 0xde0 (addresses 0x81390 .. 0x8181c), fuzz_grant.c:285-361 —
   the sweep an admitted box builds, which the harness checks row by row, and its free.

   LLVMFEntryDefs.v fixes the two ends: `GI_sweep` at 0x81390 and `GI_raw` at 0x8181c.
   This file states the invariant at every cut inside the phase; the segments between
   the cuts are proved in LLVMFEntrySweepS1 .. S4.v, and LLVMFEntrySweep.v composes them.

   Adapted from lib/A/Prog/GrantEntrySweepDefs.v (a working branch afd75724b5b, blob
   f14e00ba6, 207 lines), which carries no licence header of its own.
   Every pc, register, spill slot and loop bound is
   read from image B; image B calls `want_of` where image A inlines it, keeps the sweep
   buffer in s11 instead of a spill slot, overwrites slot 88 with the one's complement of
   that buffer for its UBSan pointer-overflow guards, and builds group B from
   reac_ctrl_identity_poll_block and three bcmp calls instead of image A's GROUPB table. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaRun.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantPa GrantPaLib GrantRo GrantFrame GrantBContracts LLVMFEntryDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel GrantModel GrantSweepModel BuildSweepModel SweepRowCheck GrantSlotPlan.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require SlotNeeds_c.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* With zify's euclidean-division flag false, `lia` does not turn `mod` and `/` into equations and fails on goals that need them (`0 <= x mod 4 < 4`), so this file sets it
   to true itself, whatever its Require closure leaves; `Local` keeps the setting here. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ---- the cuts inside the phase, as listing offsets (address - 0x80a3c) ---- *)
Definition GPS_mal   : Z := 0x9a0.   (* 0x813dc  the sweep buffer is allocated, a0 and s11 hold it *)
Definition GPS_rowhd : Z := 0xa14.   (* 0x81450  head of the inlined check_row loop         *)
Definition GPS_rowex : Z := 0xb94.   (* 0x815d0  the row loop is done                       *)
Definition GPS_ga0   : Z := 0xbdc.   (* 0x81618  group A, the channel a.base                *)
Definition GPS_ga1   : Z := 0xc48.   (* 0x81684  group A, the channels 1 .. w-1             *)
Definition GPS_gbhd  : Z := 0xd00.   (* 0x8173c  head of the group-B loop                   *)
Definition GPS_free1 : Z := 0xdc8.   (* 0x81804  the first sweep buffer is freed            *)
Definition GPS_raw   : Z := 0xde0.   (* 0x8181c  the hand-built allocation                  *)

(* The two dead ends of image B's entry function, as listing offsets: the UBSan trap
   `unimp` 0x81f48 and the abort block `jal __asan_handle_no_return` 0x81d98. Every
   branch into either one is refuted inside the segment that reaches it. *)
Definition GPS_trap  : Z := 0x150c.  (* 0x81f48 *)
Definition GPS_abort : Z := 0x135c.  (* 0x81d98 *)

(* ---- the input this phase reads, through fuzz_grant's own plain model ---- *)
Definition sw_rows (pl : list byte) : Z := h_rows (header pl).
Definition sw_base (pl : list byte) : Z := h_base (header pl).
Definition sw_in (pl : list byte) : Z := h_in (header pl).
(* malloc((rows > 0 ? rows : 1) * 34), the call at 0x813d0 *)
Definition sw_mbytes (pl : list byte) : Z := 34 * (if 0 <? sw_rows pl then sw_rows pl else 1).
Definition sw_want (pl : list byte) : Z := 8 + 3 * sw_in pl.
Definition sw_n (pl : list byte) : Z := if sw_want pl <=? sw_rows pl then sw_want pl else -1.
Definition sw_vals (pl : list byte) (t : Z) : list byte :=
  sweep_vals (T_end pl) t (sw_base pl) (Z.to_nat (sw_in pl)).
Definition sw_bytes (pl : list byte) (t : Z) : list byte :=
  SWEEP (sw_base pl) (Z.to_nat (sw_in pl)) (sw_vals pl t).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
Section c.
Variable B : asyms.
Variable MT : ameter_ops.

(* ---- the spill slots this phase carries ----
   Image B's body reads these back after every call; the offsets are image B's own
   (the block 0x81224 .. 0x81270 wrote them). Slot 88 is NOT here: this phase
   overwrites it at 0x81418 with the one's complement of the sweep buffer, so each cut
   names its own value. Slots 0, 24 and 32 are read for the last time before GPS_mal
   (0x813dc; slot 0's last read is at 0x813c4) and are not carried; slot 104 is read at 0x81818, the last slot of the
   phase, so it is. *)
Definition gsw_slots (cx : ecx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) (t : Z) : Prop :=
  gslot cx W3 ms3 8 (gF cx fp) /\
  gslot cx W3 ms3 16 (gF cx fp + GO_RAW) /\
  gslot cx W3 ms3 40 (gF cx fp + GO_UNSET) /\
  gslot cx W3 ms3 48 (c_p cx + Z.of_nat (pos_end (c_pl cx))) /\
  gslot cx W3 ms3 56 (gF cx fp + GO_LIT) /\
  gslot cx W3 ms3 64 (gF cx fp + GO_CH) /\
  gslot cx W3 ms3 72 (gF cx fp) /\
  gslot cx W3 ms3 80 (gF cx fp + GO_POLL) /\
  gslot cx W3 ms3 96 (gF cx fp + GO_VAL) /\
  gslot cx W3 ms3 104 (c_n cx - Z.of_nat (pos_end (c_pl cx))) /\
  gslot cx W3 ms3 112 (gF cx fp + GO_PAR) /\
  gslot cx W3 ms3 120 (gF cx fp + GO_A) /\
  gslot cx W3 ms3 128 (gF cx fp + GO_SET) /\
  gslot cx W3 ms3 136 (gF cx fp + GO_WAS) /\
  gslot cx W3 ms3 144 SHADOW_OFF /\
  gslot cx W3 ms3 152 t.

(* ---- what every cut between the malloc and the free keeps ---- *)
(* The table block and the first sweep block, the frame's two arrays, the spill slots,
   and the two bytes of `a`. Every cut inside this phase is on the admitted path
   (0x81394 took the branch), so `ok` is true and `a` holds the box the input asked
   for; image A's cut carried the refused case too, because image A's `GI_sweep` and
   this one split at the same instruction but image A kept one shape for both. *)
Definition gsw_blk (cx : ecx) (fp : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (t s : Z) : Prop :=
  ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ++ [(t, 460); (s, sw_mbytes (c_pl cx))] /\
  In (s, sw_mbytes (c_pl cx)) (ablocks B ly3 S3) /\
  gtab B cx ly3 S3 W3 ms3 t (T_end (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_WAS (ws_end (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_SET (st_end (c_pl cx)) /\
  Hrel (T_end (c_pl cx)) (ws_end (c_pl cx)) (st_end (c_pl cx)) /\
  SlotNeeds_c.I1 (T_end (c_pl cx)) /\
  gsw_slots cx fp W3 ms3 t /\
  c_n cx < 2 ^ 26 /\ 0 < t /\ 0 < s /\
  ok (c_pl cx) = true /\
  gfb cx fp W3 ms3 GO_A (sw_base (c_pl cx)) /\
  gfb cx fp W3 ms3 (GO_A + 1) (sw_in (c_pl cx)).

(* The bytes reac_grant_build_sweep wrote: only when it accepted the allocation. *)
Definition gsw_rows (cx : ecx) (W3 : world SEGS) (ms3 : machine_state) (t s : Z) : Prop :=
  sw_want (c_pl cx) <= sw_rows (c_pl cx) /\
  garr8 SEGS (mrestrict (w_H W3) (ms_mem ms3)) s
        (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)).

(* ---- the invariant at each inner cut ---- *)

(* 0x813dc: the box is admitted, the sweep buffer is allocated, `mv s11,a0` has run and
   a0 and s11 both hold it; reac_grant_build_sweep follows. s4 is the row count the
   header names, s8 the address of `a`, s2 the table, s3 the frame's shadow base. The
   cut is one instruction past the null test 0x813d4, which the segment before refutes. *)
Definition GIS_mal (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t s : Z,
  ge_body cx fp GPS_mal W3 ms3 GSH_a /\ k <= 2 /\ acc <= GE_A2 MT - mo_free MT /\
  gsw_blk cx fp ly3 S3 W3 ms3 t s /\
  gslot cx W3 ms3 88 (h_base (header (c_pl cx)) mod 2 ^ 64) /\
  getr (ms_regs ms3) 10 = w64 s /\ getr (ms_regs ms3) 27 = w64 s /\
  getr (ms_regs ms3) 20 = w64 (sw_rows (c_pl cx)) /\
  getr (ms_regs ms3) 24 = w64 (gF cx fp + GO_A) /\
  getr (ms_regs ms3) 18 = w64 t /\
  getr (ms_regs ms3) 19 = w64 (gSH cx fp).

(* 0x81450, the head of the row loop: j rows have passed check_row. The twelve
   constants the loop hoisted (0x81420 .. 0x81444) are part of the cut, as image A's
   seven are. s8 walks the row, s5 and a4 the row's body, s11 holds the buffer, and
   slot 88 holds its one's complement for the UBSan guard at 0x81458. *)
Definition GIS_rowhd (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (t s : Z) (j : nat),
  ge_body cx fp GPS_rowhd W3 ms3 GSH_a /\ k <= 2 /\ acc <= GE_A2 MT - mo_free MT /\
  gsw_blk cx fp ly3 S3 W3 ms3 t s /\ gsw_rows cx W3 ms3 t s /\
  gslot cx W3 ms3 88 (2 ^ 64 - 1 - s) /\
  Z.of_nat j < sw_n (c_pl cx) /\
  getr (ms_regs ms3) 13 = w64 (Z.of_nat j) /\
  getr (ms_regs ms3) 10 = w64 (sw_n (c_pl cx)) /\
  getr (ms_regs ms3) 14 = w64 (s + 34 * Z.of_nat j + 2) /\
  getr (ms_regs ms3) 21 = w64 (s + 34 * Z.of_nat j + 2) /\
  getr (ms_regs ms3) 24 = w64 (s + 34 * Z.of_nat j) /\
  getr (ms_regs ms3) 27 = w64 s /\ getr (ms_regs ms3) 19 = w64 (gSH cx fp) /\
  getr (ms_regs ms3) 15 = w64 (-2) /\ getr (ms_regs ms3) 16 = w64 34 /\
  getr (ms_regs ms3) 17 = w64 32 /\ getr (ms_regs ms3) 5 = w64 205 /\
  getr (ms_regs ms3) 6 = w64 (-1) /\ getr (ms_regs ms3) 7 = w64 234 /\
  getr (ms_regs ms3) 28 = w64 (-3) /\ getr (ms_regs ms3) 29 = w64 4 /\
  getr (ms_regs ms3) 30 = w64 (-4) /\ getr (ms_regs ms3) 31 = w64 3.

(* 0x815d0: every row is a cd ea link-4 SINGLE whose block sums to zero. *)
Definition GIS_rowex (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t s : Z,
  ge_body cx fp GPS_rowex W3 ms3 GSH_a /\ k <= 2 /\ acc <= GE_A2 MT - mo_free MT /\
  gsw_blk cx fp ly3 S3 W3 ms3 t s /\ gsw_rows cx W3 ms3 t s /\
  gslot cx W3 ms3 88 (2 ^ 64 - 1 - s) /\
  getr (ms_regs ms3) 27 = w64 s /\ getr (ms_regs ms3) 19 = w64 (gSH cx fp).

(* 0x81618, group A for the channel a.base: p of its three records are checked.
   s10 is p, s9 the row, s2 the byte offset the UBSan guard at 0x8161c compares with
   the one's complement in slot 88, s4 the bound 3. *)
Definition GIS_ga0 (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (t s : Z) (p : nat),
  ge_body cx fp GPS_ga0 W3 ms3 GSH_a /\ k <= 2 /\ acc <= GE_A2 MT - mo_free MT /\
  gsw_blk cx fp ly3 S3 W3 ms3 t s /\ gsw_rows cx W3 ms3 t s /\
  gslot cx W3 ms3 88 (2 ^ 64 - 1 - s) /\
  (p < 3)%nat /\
  getr (ms_regs ms3) 26 = w64 (Z.of_nat p) /\
  getr (ms_regs ms3) 25 = w64 (s + 34 + 34 * Z.of_nat p) /\
  getr (ms_regs ms3) 18 = w64 (34 + 34 * Z.of_nat p) /\
  getr (ms_regs ms3) 20 = w64 3 /\
  getr (ms_regs ms3) 27 = w64 s /\ getr (ms_regs ms3) 19 = w64 (gSH cx fp).

(* 0x81684, group A for the channels 1 .. w-1: c channels are checked. The inner
   parameter loop (head 0x81694) is a local cut of the segment, as image A's is. *)
Definition GIS_ga1 (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (t s : Z) (c : nat),
  ge_body cx fp GPS_ga1 W3 ms3 GSH_a /\ k <= 2 /\ acc <= GE_A2 MT - mo_free MT /\
  gsw_blk cx fp ly3 S3 W3 ms3 t s /\ gsw_rows cx W3 ms3 t s /\
  gslot cx W3 ms3 88 (2 ^ 64 - 1 - s) /\
  (1 <= c)%nat /\ Z.of_nat c < sw_in (c_pl cx) /\
  getr (ms_regs ms3) 18 = w64 (Z.of_nat c) /\
  getr (ms_regs ms3) 21 = w64 34 /\ getr (ms_regs ms3) 22 = w64 3 /\
  getr (ms_regs ms3) 27 = w64 s /\ getr (ms_regs ms3) 19 = w64 (gSH cx fp).

(* 0x8173c, the group-B loop: i of the six identity polls are checked. Image B builds
   each poll row with reac_ctrl_identity_poll_block into the frame's `poll` object and
   compares it with the sweep's row, then the row's bytes 16..19 with the compound
   literal it writes into the frame, then the row's bytes 20..22 with POLL (object 6);
   image A compares the sweep against the GROUPB table (object 19) instead. *)
Definition GIS_gbhd (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (t s : Z) (i : nat),
  ge_body cx fp GPS_gbhd W3 ms3 GSH_a /\ k <= 2 /\ acc <= GE_A2 MT - mo_free MT /\
  gsw_blk cx fp ly3 S3 W3 ms3 t s /\ gsw_rows cx W3 ms3 t s /\
  gslot cx W3 ms3 88 (2 ^ 64 - 1 - s) /\
  (i <= 5)%nat /\
  getr (ms_regs ms3) 18 = w64 (Z.of_nat i) /\
  getr (ms_regs ms3) 24 = w64 (34 * Z.of_nat i) /\
  getr (ms_regs ms3) 20 = w64 (s + 170) /\
  getr (ms_regs ms3) 22 = w64 (s + 190) /\
  getr (ms_regs ms3) 23 = w64 (s + 186) /\
  getr (ms_regs ms3) 21 = w64 (-8) /\
  getr (ms_regs ms3) 25 = w64 (VAL (A_OBJ 6) + 3 * Z.of_nat i) /\
  getr (ms_regs ms3) 27 = w64 s /\ getr (ms_regs ms3) 19 = w64 (gSH cx fp).

(* 0x81804: the checks are done; the first sweep buffer is freed. Two slots reach it,
   the row-count test 0x8140c (no row was checked) and the end of the group-B loop, and
   they disagree on slot 88, so this cut does not name it. *)
Definition GIS_free1 (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t s : Z,
  ge_body cx fp GPS_free1 W3 ms3 GSH_a /\ k <= 2 /\ acc <= GE_A2 MT - mo_free MT /\
  gsw_blk cx fp ly3 S3 W3 ms3 t s /\
  getr (ms_regs ms3) 27 = w64 s /\ getr (ms_regs ms3) 19 = w64 (gSH cx fp).

(* ---- the runtime the phase uses ---- *)
(* Taken as one premise by every segment, so that a segment's signature does not
   change when its proof starts to use one of them. Each conjunct is one conjunct of
   `GrantBContracts.hyps_LLVMFuzzerTestOneInput`, except the two meter laws and the two
   meter rules, which the top of the chain builds from RT_MALLOC / RT_FREE at the
   trivial meter (lib/Reusable/YCbp.v amalloc04_rule_triv / afree04_rule_triv). *)
Definition GSW_RT : Prop :=
  AR_laws SEGS B /\ PALib B /\ PALibF B /\ model_laws (as_universe B) /\
  ameter_laws MT /\ ameter_fs_laws MT /\
  amalloc04_rule SEGS B MT /\ afree04_rule SEGS B MT /\
  abcmp_realizes SEGS B (SIGMA GS___interceptor_trampoline_bcmp) /\
  img_shadow_vis SEGS B /\ globs_marked SEGS B GRANT_GLOBS_B /\
  ro_below_ofl SEGS pa_relro_lo pa_relro_hi.

(* ---- the four read-only tables of image B this phase reads ----
   HEAD_ACK (object 4, 0x20f00, 34 bytes; the bcmp at 0x815e0), HEAD_MARK (object 5,
   0x20f60, 34; 0x81604), POLL (object 6, 0x20ec0, 18; 0x817d4) and GRANT_GROUPB
   (object 19, 0x21080, 204; reac_ctrl_identity_poll_block's own premise). PI and B are
   abstract, so no walk can compute these; image A's `ge_sweep` took the same facts as
   Hypotheses (GrantEntrySweep.v:46-72) and its image instance discharged them. On image
   B they are `GrantBContracts.IMG_LLVMF_SWEEP`, a conjunct of
   `hyps_LLVMFuzzerTestOneInput`, whose byte lists `b_llvmf_sweep_check` and
   `b_groupb_check` check against image B by computation. *)
Definition GSW_IMG : Prop := IMG_LLVMF_SWEEP B.

(* ---- the statement of each segment ---- *)
#[local] Notation GF := (fun GI => ge_from B MT (ge_post B MT) GI).
Definition SEG_sweep : Prop := GSW_RT -> GF GIS_mal -> GF (GI_raw B MT) -> GF (GI_sweep B MT).
Definition SEG_mal : Prop := GSW_RT -> GF GIS_rowhd -> GF GIS_free1 -> GF GIS_mal.
Definition SEG_free1 : Prop := GSW_RT -> GF (GI_raw B MT) -> GF GIS_free1.
Definition SEG_rows : Prop := GSW_RT -> GF GIS_rowex -> GF GIS_rowhd.
Definition SEG_heads : Prop := GSW_RT -> GSW_IMG -> GF GIS_ga0 -> GF GIS_rowex.
Definition SEG_ga0 : Prop := GSW_RT -> GF GIS_ga1 -> GF GIS_gbhd -> GF GIS_ga0.
Definition SEG_ga1 : Prop := GSW_RT -> GF GIS_gbhd -> GF GIS_ga1.
Definition SEG_gb : Prop := GSW_RT -> GSW_IMG -> GF GIS_free1 -> GF GIS_gbhd.

End c.
End b.
End a.
