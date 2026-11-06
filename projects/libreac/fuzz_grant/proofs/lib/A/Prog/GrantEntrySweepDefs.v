(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySweepDefs), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACeg.v. *)
(* The SWEEP phase of fuzz_grant's entry function on the ASan build: listing slots
   0x7a8 .. 0xbfc (addresses 0x80e58 .. 0x812ac), fuzz_grant.c:285-361 — the sweep
   an admitted box builds, which the harness checks row by row, and its free.

   GrantEntryDefs.v fixes the two ends: `GI_sweep` at 0x80e58 and `GI_raw` at
   0x812ac. This file states the invariant at every cut inside the phase; the
   segments between the cuts are proved in GrantEntrySweepS1 .. S4.v, and
   GrantEntrySweep.v composes them. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YC5d YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaJournal GrantSyms GrantList GrantPa GrantPaLib GrantBase GrantRo GrantFrame GrantEntryDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel GrantModel GrantSweepModel BuildSweepModel SweepRowCheck GrantSlotPlan.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require SlotNeeds_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ---- the cuts inside the phase, as listing offsets (address - 0x806b0) ---- *)
Definition GPS_mal   : Z := 0x7e8.   (* 0x80e98  the sweep buffer is allocated and stored *)
Definition GPS_rowhd : Z := 0x844.   (* 0x80ef4  head of the inlined check_row loop  *)
Definition GPS_rowex : Z := 0x950.   (* 0x81000  the row loop is done                *)
Definition GPS_ga0   : Z := 0x98c.   (* 0x8103c  group A, the channel a.base         *)
Definition GPS_ga1   : Z := 0xa54.   (* 0x81104  group A, the channels 1 .. w-1      *)
Definition GPS_gbhd  : Z := 0xb48.   (* 0x811f8  head of the group-B loop            *)
Definition GPS_free1 : Z := 0xbe8.   (* 0x81298  the first sweep buffer is freed     *)
Definition GPS_raw   : Z := 0xbfc.   (* 0x812ac  the hand-built allocation           *)

(* ---- the input this phase reads, through fuzz_grant's own plain model ---- *)
Definition sw_rows (pl : list byte) : Z := h_rows (header pl).
Definition sw_base (pl : list byte) : Z := h_base (header pl).
Definition sw_in (pl : list byte) : Z := h_in (header pl).
(* malloc((rows > 0 ? rows : 1) * 34) *)
Definition sw_mbytes (pl : list byte) : Z := 34 * (if 0 <? sw_rows pl then sw_rows pl else 1).
Definition sw_want (pl : list byte) : Z := 8 + 3 * sw_in pl.
Definition sw_n (pl : list byte) : Z := if sw_want pl <=? sw_rows pl then sw_want pl else -1.
Definition sw_vals (pl : list byte) (t : Z) : list byte :=
  sweep_vals (T_end pl) t (sw_base pl) (Z.to_nat (sw_in pl)).
Definition sw_bytes (pl : list byte) (t : Z) : list byte :=
  SWEEP (sw_base pl) (Z.to_nat (sw_in pl)) (sw_vals pl t).
(* the hand-built allocation of fuzz_grant.c:365-387 *)
Definition rw_base (pl : list byte) : Z := fst (fst (raw_rd pl)).
Definition rw_width (pl : list byte) : Z := snd (fst (raw_rd pl)).
Definition GE_SW2 : Z := 4352.       (* malloc(REAC_GRANT_SWEEP_MAX * 34) *)

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

(* ---- what every cut between the two mallocs keeps ---- *)
(* The table block and the first sweep block, the frame's two arrays, and the input
   cursor, which this part of the phase does not move. *)
Definition gsw_blk (cx : ecx) (fp : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (t s : Z) : Prop :=
  ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ++ [(t, 460); (s, sw_mbytes (c_pl cx))] /\
  In (s, sw_mbytes (c_pl cx)) (ablocks B ly3 S3) /\
  gtab B cx ly3 S3 W3 ms3 t (T_end (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_WAS (ws_end (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_SET (st_end (c_pl cx)) /\
  Hrel (T_end (c_pl cx)) (ws_end (c_pl cx)) (st_end (c_pl cx)) /\
  SlotNeeds_c.I1 (T_end (c_pl cx)) /\
  gslots_late cx fp W3 ms3 /\
  gslot cx W3 ms3 88 (c_p cx + Z.of_nat (pos_end (c_pl cx))) /\
  gslot cx W3 ms3 120 (c_n cx - Z.of_nat (pos_end (c_pl cx))) /\
  gslot cx W3 ms3 96 (gF cx fp + GO_LIT) /\
  gslot cx W3 ms3 64 s /\
  getr (ms_regs ms3) 20 = w64 t /\
  c_n cx < 2 ^ 26 /\ 0 < t /\ 0 < s /\
  (if ok (c_pl cx)
   then gfb cx fp W3 ms3 GO_A (sw_base (c_pl cx)) /\ gfb cx fp W3 ms3 (GO_A + 1) (sw_in (c_pl cx))
   else gfb cx fp W3 ms3 GO_A 0 /\ gfb cx fp W3 ms3 (GO_A + 1) 0).

(* The bytes reac_grant_build_sweep wrote: only when it accepted the allocation. *)
Definition gsw_rows (cx : ecx) (W3 : world SEGS) (ms3 : machine_state) (t s : Z) : Prop :=
  ok (c_pl cx) = true /\ sw_want (c_pl cx) <= sw_rows (c_pl cx) /\
  garr8 SEGS (mrestrict (w_H W3) (ms_mem ms3)) s
        (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)).

(* ---- the invariant at each inner cut ---- *)

(* 0x80e98: the box is admitted; the sweep buffer is allocated and its address
   stored in slot 64 (`sd a0,64(s1)` at 0x80e94); reac_grant_build_sweep follows. *)
Definition GIS_mal (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t s : Z,
  ge_body cx fp GPS_mal W3 ms3 GSH_a /\ k <= 2 /\ acc <= GE_A2 MT - mo_free MT /\
  gsw_blk cx fp ly3 S3 W3 ms3 t s /\ ok (c_pl cx) = true /\
  getr (ms_regs ms3) 10 = w64 s /\ getr (ms_regs ms3) 19 = w64 (sw_rows (c_pl cx)) /\
  getr (ms_regs ms3) 18 = w64 (gF cx fp + GO_A) /\ getr (ms_regs ms3) 22 = w64 (gSH cx fp).

(* 0x80ef4, the head of the row loop: j rows have passed check_row. *)
Definition GIS_rowhd (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (t s : Z) (j : nat),
  ge_body cx fp GPS_rowhd W3 ms3 GSH_a /\ k <= 2 /\ acc <= GE_A2 MT - mo_free MT /\
  gsw_blk cx fp ly3 S3 W3 ms3 t s /\ gsw_rows cx W3 ms3 t s /\
  Z.of_nat j < sw_n (c_pl cx) /\
  getr (ms_regs ms3) 13 = w64 (Z.of_nat j) /\ getr (ms_regs ms3) 10 = w64 (sw_n (c_pl cx)) /\
  getr (ms_regs ms3) 14 = w64 (s + 34 * Z.of_nat j + 2) /\
  getr (ms_regs ms3) 7 = w64 (s + 34 * Z.of_nat j + 2) /\
  getr (ms_regs ms3) 21 = w64 s /\ getr (ms_regs ms3) 23 = w64 SHADOW_OFF /\
  getr (ms_regs ms3) 22 = w64 (gSH cx fp) /\ getr (ms_regs ms3) 18 = w64 (gF cx fp + GO_A) /\
  getr (ms_regs ms3) 15 = w64 34 /\ getr (ms_regs ms3) 16 = w64 205 /\
  getr (ms_regs ms3) 17 = w64 234 /\ getr (ms_regs ms3) 5 = w64 4 /\ getr (ms_regs ms3) 6 = w64 3.

(* 0x81000: every row is a cd ea link-4 SINGLE whose block sums to zero. *)
Definition GIS_rowex (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t s : Z,
  ge_body cx fp GPS_rowex W3 ms3 GSH_a /\ k <= 2 /\ acc <= GE_A2 MT - mo_free MT /\
  gsw_blk cx fp ly3 S3 W3 ms3 t s /\ gsw_rows cx W3 ms3 t s /\
  getr (ms_regs ms3) 21 = w64 s /\ getr (ms_regs ms3) 23 = w64 SHADOW_OFF /\
  getr (ms_regs ms3) 22 = w64 (gSH cx fp) /\ getr (ms_regs ms3) 18 = w64 (gF cx fp + GO_A).

(* 0x8103c, group A for the channel a.base: p of its three records are checked. *)
Definition GIS_ga0 (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (t s : Z) (p : nat),
  ge_body cx fp GPS_ga0 W3 ms3 GSH_a /\ k <= 2 /\ acc <= GE_A2 MT - mo_free MT /\
  gsw_blk cx fp ly3 S3 W3 ms3 t s /\ gsw_rows cx W3 ms3 t s /\
  (p < 3)%nat /\
  getr (ms_regs ms3) 26 = w64 (Z.of_nat p) /\
  getr (ms_regs ms3) 27 = w64 (s + 34 + 34 * Z.of_nat p) /\
  getr (ms_regs ms3) 21 = w64 3 /\ getr (ms_regs ms3) 18 = w64 (gF cx fp + GO_A) /\
  getr (ms_regs ms3) 22 = w64 (gSH cx fp) /\ getr (ms_regs ms3) 23 = w64 SHADOW_OFF.

(* 0x81104, group A for the channels 1 .. w-1: c channels are checked. *)
Definition GIS_ga1 (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (t s : Z) (c : nat),
  ge_body cx fp GPS_ga1 W3 ms3 GSH_a /\ k <= 2 /\ acc <= GE_A2 MT - mo_free MT /\
  gsw_blk cx fp ly3 S3 W3 ms3 t s /\ gsw_rows cx W3 ms3 t s /\
  (1 <= c)%nat /\ Z.of_nat c < sw_in (c_pl cx) /\
  getr (ms_regs ms3) 21 = w64 (Z.of_nat c) /\ getr (ms_regs ms3) 24 = w64 (Z.of_nat c) /\
  getr (ms_regs ms3) 25 = w64 (s + 374 + 102 * (Z.of_nat c - 1)) /\
  getr (ms_regs ms3) 18 = w64 (gF cx fp + GO_A) /\ getr (ms_regs ms3) 23 = w64 3 /\
  getr (ms_regs ms3) 19 = w64 (gSH cx fp).

(* 0x811f8, the group-B loop: i of the six identity polls are checked. *)
Definition GIS_gbhd (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (t s : Z) (i : nat),
  ge_body cx fp GPS_gbhd W3 ms3 GSH_a /\ k <= 2 /\ acc <= GE_A2 MT - mo_free MT /\
  gsw_blk cx fp ly3 S3 W3 ms3 t s /\ gsw_rows cx W3 ms3 t s /\
  (i <= 5)%nat /\
  getr (ms_regs ms3) 18 = w64 (Z.of_nat i) /\
  getr (ms_regs ms3) 27 = w64 (s + 190 + 34 * Z.of_nat i) /\
  getr (ms_regs ms3) 26 = w64 (VAL (A_OBJ 6) + 3 * Z.of_nat i) /\
  getr (ms_regs ms3) 21 = w64 (6 - Z.of_nat i) /\
  getr (ms_regs ms3) 19 = w64 (gF cx fp + GO_POLL) /\
  getr (ms_regs ms3) 24 = w64 17 /\ getr (ms_regs ms3) 25 = w64 5 /\
  getr (ms_regs ms3) 23 = w64 (-8) /\ getr (ms_regs ms3) 22 = w64 (gSH cx fp).

(* 0x81298: the checks are done; the first sweep buffer is freed. *)
Definition GIS_free1 (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t s : Z,
  ge_body cx fp GPS_free1 W3 ms3 GSH_a /\ k <= 2 /\ acc <= GE_A2 MT - mo_free MT /\
  gsw_blk cx fp ly3 S3 W3 ms3 t s /\ getr (ms_regs ms3) 22 = w64 (gSH cx fp).

(* ---- the runtime the phase uses ---- *)
(* Taken as one premise by every segment, so that a segment's signature does not
   change when its proof starts to use one of them. *)
Definition GSW_RT : Prop :=
  AR_laws SEGS B /\ PALib B /\ ameter_laws MT /\ ameter_fs_laws MT /\
  amalloc04_rule SEGS B MT /\ afree04_rule SEGS B MT /\ afree_null04_rule SEGS B MT /\
  abcmp_realizes SEGS B (SIGMA GS___interceptor_trampoline_bcmp) /\
  img_shadow_vis SEGS B /\ model_laws (as_universe B) /\ PALibF B.


(* ---- the statement of each segment ---- *)
#[local] Notation GF := (fun GI => ge_from B MT (ge_post B MT) GI).
Definition SEG_sweep : Prop := GSW_RT -> GF GIS_mal -> GF (GI_raw B MT) -> GF (GI_sweep B MT).
Definition SEG_mal : Prop := GSW_RT -> GF GIS_rowhd -> GF GIS_free1 -> GF GIS_mal.
Definition SEG_free1 : Prop := GSW_RT -> GF (GI_raw B MT) -> GF GIS_free1.
Definition SEG_rows : Prop := GSW_RT -> GF GIS_rowex -> GF GIS_rowhd.
Definition SEG_heads : Prop := GSW_RT -> GF GIS_ga0 -> GF GIS_rowex.
Definition SEG_ga0 : Prop := GSW_RT -> GF GIS_ga1 -> GF GIS_gbhd -> GF GIS_ga0.
Definition SEG_ga1 : Prop := GSW_RT -> GF GIS_gbhd -> GF GIS_ga1.
Definition SEG_gb : Prop := GSW_RT -> GF GIS_free1 -> GF GIS_gbhd.

End c.
End b.
End a.
