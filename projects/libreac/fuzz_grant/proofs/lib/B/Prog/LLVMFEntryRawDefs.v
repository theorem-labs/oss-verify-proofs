(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryRawDefs), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACeg.v. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/Prog/GrantEntryRawDefs.v. *)
(* Ported from lib/A/Prog/GrantEntryRawDefs.v of a working branch 7c8c67da870 (blob 6a37011e675). *)
(* The cuts of the hand-built allocation phase of LLVMFuzzerTestOneInput on image B
   (fuzz_grant.c:363-387; slots 0xde0 .. 0xf08 of the listing, 0x8181c .. 0x81944).

   The phase marks `raw` usable (shadow byte 70 of the frame := 2), reads raw.base and
   raw.width from the input (each read preceded by the UBSan check that the cursor does not
   wrap and by the check of its shadow byte), allocates the 4352-byte sweep buffer, calls
   reac_grant_build_sweep on the hand-built allocation, checks its answer against
   reac_grant_alloc_fits, makes the two calls that must be refused (a null sweep, a null
   allocation) and frees the buffer. No branch to the error path is taken: 0x81d98 (abort),
   0x81f48 (the UBSan trap) and 0x81f90 / 0x81fcc (the slow paths of the input checks).

   Image B keeps the frame's shadow base in s3, the table in s4, the input cursor in s5 (until
   0x81850, then the address of `raw`, loaded from slot 16), the address of `ch` in s6 and the
   bytes of input left in s7; it loads the shadow offset from slot 144 at each check and keeps
   the input cursor in slot 48. The answer of the first sweep is in s8, and s4 is -1 from
   0x81920 on.

   The phase is cut before each call it makes:
     GP_raw  0xde0 (0x8181c)  GI_raw (LLVMFEntryDefs.v)
     GR_hd   0xde8 (0x81824)  beqz s7, the split on the bytes of input left
     GR_mal  0xe78 (0x818b4)  jal malloc, a0 = 4352
     GR_bs1  0xe90 (0x818cc)  jal reac_grant_build_sweep (s, 128, &raw, t)
     GR_fit  0xea4 (0x818e0)  jal reac_grant_alloc_fits (raw.base, raw.width)
     GR_bs2  0xedc (0x81918)  jal reac_grant_build_sweep (NULL, 1, &raw, t)
     GR_bs3  0xef8 (0x81934)  jal reac_grant_build_sweep (s, 128, NULL, t)
     GR_free 0xf04 (0x81940)  jal free (s)
     GP_sched0 0xf08 (0x81944) GI_sched0 (LLVMFEntryDefs.v)
   Each segment lemma has the shape `ge_from POST G_next -> ge_from POST G_self`. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaRun PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantPa GrantPaLib.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import LLVMFEntryDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel GrantModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require GrantSlotPlan SlotNeeds_c.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the pcs of the cuts, as offsets in the listing (address - 0x80a3c) ---- *)
Definition GR_hd : Z := 0xde8.    (* 0x81824, the `beqz s7` *)
Definition GR_mal : Z := 0xe78.   (* 0x818b4 *)
Definition GR_bs1 : Z := 0xe90.   (* 0x818cc *)
Definition GR_fit : Z := 0xea4.   (* 0x818e0 *)
Definition GR_bs2 : Z := 0xedc.   (* 0x81918 *)
Definition GR_bs3 : Z := 0xef8.   (* 0x81934 *)
Definition GR_free : Z := 0xf04.  (* 0x81940 *)

(* The sweep buffer the harness allocates: 34 rows of 128 bytes (`li a0,17; slli a0,a0,8`
   at 0x818ac). *)
Definition RAW_SW : Z := 4352.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.

(* ---- the two bytes of `raw` the input gives (fuzz_grant.c:367-368) ---- *)
Definition raw_b (cx : ecx) : Z := fst (fst (GrantSlotPlan.raw_rd (c_pl cx))).
Definition raw_w (cx : ecx) : Z := snd (fst (GrantSlotPlan.raw_rd (c_pl cx))).
(* The answer reac_grant_build_sweep gives on the hand-built allocation. *)
Definition raw_ans (cx : ecx) : Z := if fits (raw_b cx) (raw_w cx) then 8 + 3 * raw_w cx else -1.

(* The blocks after the sweep buffer `s` was allocated. *)
Definition gblk2 (cx : ecx) (ly3 : alayout) (S3 : astate) (t s : Z) : Prop :=
  ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ++ [(t, 460); (s, RAW_SW)].

(* The spill slots every cut of the phase keeps and GI_sched0 hands on: the frame (8, 72),
   the addresses of unset_sent, ch, value, param, set_to and was_set, the shadow offset and
   the table. *)
Definition rslots (cx : ecx) (fp t : Z) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  gslot cx W3 ms3 8 (gF cx fp) /\ gslot cx W3 ms3 40 (gF cx fp + GO_UNSET) /\
  gslot cx W3 ms3 64 (gF cx fp + GO_CH) /\ gslot cx W3 ms3 72 (gF cx fp) /\
  gslot cx W3 ms3 96 (gF cx fp + GO_VAL) /\ gslot cx W3 ms3 112 (gF cx fp + GO_PAR) /\
  gslot cx W3 ms3 128 (gF cx fp + GO_SET) /\ gslot cx W3 ms3 136 (gF cx fp + GO_WAS) /\
  gslot cx W3 ms3 144 SHADOW_OFF /\ gslot cx W3 ms3 152 t.

(* What every cut of the phase after the head holds: the machine part at pc, the frame's
   shadow with `raw` usable, the registers the phase keeps (s3 the frame's shadow base, s5
   the address of raw, s6 the address of ch, s7 the bytes of input left), the input
   position in slot 48, the other spill slots, the two bytes of raw, the two arrays of the
   frame and the facts about the tables that the scheduler needs. *)
Definition rcore (cx : ecx) (fp pc t : Z) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  ge_body cx fp pc W3 ms3 GSH_raw /\ c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 19 = w64 (gSH cx fp) /\
  getr (ms_regs ms3) 21 = w64 (gF cx fp + GO_RAW) /\
  getr (ms_regs ms3) 22 = w64 (gF cx fp + GO_CH) /\
  getr (ms_regs ms3) 23 = w64 (c_n cx - Z.of_nat (GrantSlotPlan.pos_raw (c_pl cx))) /\
  gslot cx W3 ms3 48 (c_p cx + Z.of_nat (GrantSlotPlan.pos_raw (c_pl cx))) /\
  rslots cx fp t W3 ms3 /\
  gfb cx fp W3 ms3 GO_RAW (raw_b cx) /\ gfb cx fp W3 ms3 (GO_RAW + 1) (raw_w cx) /\
  gfarr cx fp W3 ms3 GO_WAS (GrantSlotPlan.ws_end (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_SET (GrantSlotPlan.st_end (c_pl cx)) /\
  GrantSlotPlan.Hrel (GrantSlotPlan.T_end (c_pl cx)) (GrantSlotPlan.ws_end (c_pl cx))
    (GrantSlotPlan.st_end (c_pl cx)) /\ SlotNeeds_c.I1 (GrantSlotPlan.T_end (c_pl cx)).

(* 0x81824, inside the head: raw is marked usable (shadow byte 70 = 2) and `beqz s7` splits
   on the bytes of input left. The head is cut here so that each case is its own lemma. *)
Definition GR_hdI (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t : Z,
  ge_body cx fp GR_hd W3 ms3 GSH_raw /\ k <= 3 /\ acc <= GE_A2 MT /\
  gblk1 B cx ly3 S3 t /\ c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 19 = w64 (gSH cx fp) /\ getr (ms_regs ms3) 20 = w64 t /\
  getr (ms_regs ms3) 21 = w64 (c_p cx + Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  getr (ms_regs ms3) 22 = w64 (gF cx fp + GO_CH) /\
  getr (ms_regs ms3) 23 = w64 (c_n cx - Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  gslot cx W3 ms3 16 (gF cx fp + GO_RAW) /\
  gslot cx W3 ms3 48 (c_p cx + Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  rslots cx fp t W3 ms3 /\
  gtab B cx ly3 S3 W3 ms3 t (GrantSlotPlan.T_end (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_WAS (GrantSlotPlan.ws_end (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_SET (GrantSlotPlan.st_end (c_pl cx)) /\
  GrantSlotPlan.Hrel (GrantSlotPlan.T_end (c_pl cx)) (GrantSlotPlan.ws_end (c_pl cx))
    (GrantSlotPlan.st_end (c_pl cx)) /\ SlotNeeds_c.I1 (GrantSlotPlan.T_end (c_pl cx)).
(* The three cases: no byte of input left, one byte left, two or more bytes left. *)
Definition GR_hd0I (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  GR_hdI cx fp k acc ly3 S3 W3 ms3 md3 /\ GrantSlotPlan.pos_end (c_pl cx) = length (c_pl cx).
Definition GR_hd1I (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  GR_hdI cx fp k acc ly3 S3 W3 ms3 md3 /\ S (GrantSlotPlan.pos_end (c_pl cx)) = length (c_pl cx).
Definition GR_hd2I (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  GR_hdI cx fp k acc ly3 S3 W3 ms3 md3 /\ (S (S (GrantSlotPlan.pos_end (c_pl cx))) <= length (c_pl cx))%nat.

(* 0x818b4: raw holds the input's two bytes; malloc(4352) is called next. *)
Definition GR_malI (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t : Z,
  rcore cx fp GR_mal t W3 ms3 /\ k <= 3 /\ acc <= GE_A2 MT /\
  gblk1 B cx ly3 S3 t /\ gtab B cx ly3 S3 W3 ms3 t (GrantSlotPlan.T_end (c_pl cx)) /\
  getr (ms_regs ms3) 20 = w64 t /\ getr (ms_regs ms3) 10 = w64 RAW_SW.

(* 0x818cc: the sweep buffer s is allocated (s2); reac_grant_build_sweep (s, 128, &raw, t)
   is called next. *)
Definition GR_bs1I (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t s : Z,
  rcore cx fp GR_bs1 t W3 ms3 /\ k <= 4 /\ acc <= GE_A2 MT + mo_malloc MT RAW_SW /\
  gblk2 cx ly3 S3 t s /\ gtab B cx ly3 S3 W3 ms3 t (GrantSlotPlan.T_end (c_pl cx)) /\
  4096 <= s /\ getr (ms_regs ms3) 20 = w64 t /\ getr (ms_regs ms3) 18 = w64 s /\
  getr (ms_regs ms3) 10 = w64 s /\ getr (ms_regs ms3) 11 = w64 128 /\
  getr (ms_regs ms3) 12 = w64 (gF cx fp + GO_RAW) /\ getr (ms_regs ms3) 13 = w64 t.

(* 0x818e0: reac_grant_build_sweep gave its answer (s8); reac_grant_alloc_fits (raw.base,
   raw.width) is called next. *)
Definition GR_fitI (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t s : Z,
  rcore cx fp GR_fit t W3 ms3 /\ k <= 4 /\ acc <= GE_A2 MT + mo_malloc MT RAW_SW /\
  gblk2 cx ly3 S3 t s /\ gtab B cx ly3 S3 W3 ms3 t (GrantSlotPlan.T_end (c_pl cx)) /\
  4096 <= s /\ getr (ms_regs ms3) 20 = w64 t /\ getr (ms_regs ms3) 18 = w64 s /\
  getr (ms_regs ms3) 24 = w64 (raw_ans cx) /\
  getr (ms_regs ms3) 10 = w64 (raw_b cx) /\ getr (ms_regs ms3) 11 = w64 (raw_w cx).

(* 0x81918: the answer agreed with reac_grant_alloc_fits; reac_grant_build_sweep (NULL, 1,
   &raw, t) is called next. *)
Definition GR_bs2I (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t s : Z,
  rcore cx fp GR_bs2 t W3 ms3 /\ k <= 4 /\ acc <= GE_A2 MT + mo_malloc MT RAW_SW /\
  gblk2 cx ly3 S3 t s /\ gtab B cx ly3 S3 W3 ms3 t (GrantSlotPlan.T_end (c_pl cx)) /\
  4096 <= s /\ getr (ms_regs ms3) 20 = w64 t /\ getr (ms_regs ms3) 18 = w64 s /\
  getr (ms_regs ms3) 10 = w64 0 /\ getr (ms_regs ms3) 11 = w64 1 /\
  getr (ms_regs ms3) 12 = w64 (gF cx fp + GO_RAW) /\ getr (ms_regs ms3) 13 = w64 t.

(* 0x81934: the null sweep was refused (s4 = -1, `li s4,-1` at 0x81920, after a3 := t);
   reac_grant_build_sweep (s, 128, NULL, t) is called next. *)
Definition GR_bs3I (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t s : Z,
  rcore cx fp GR_bs3 t W3 ms3 /\ k <= 4 /\ acc <= GE_A2 MT + mo_malloc MT RAW_SW /\
  gblk2 cx ly3 S3 t s /\ gtab B cx ly3 S3 W3 ms3 t (GrantSlotPlan.T_end (c_pl cx)) /\
  4096 <= s /\ getr (ms_regs ms3) 18 = w64 s /\ getr (ms_regs ms3) 20 = w64 (-1) /\
  getr (ms_regs ms3) 10 = w64 s /\ getr (ms_regs ms3) 11 = w64 128 /\
  getr (ms_regs ms3) 12 = w64 0 /\ getr (ms_regs ms3) 13 = w64 t.

(* 0x81940: the null allocation was refused; free (s) is called next. *)
Definition GR_freeI (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t s : Z,
  rcore cx fp GR_free t W3 ms3 /\ k <= 4 /\ acc <= GE_A2 MT + mo_malloc MT RAW_SW /\
  gblk2 cx ly3 S3 t s /\ gtab B cx ly3 S3 W3 ms3 t (GrantSlotPlan.T_end (c_pl cx)) /\
  4096 <= s /\ getr (ms_regs ms3) 18 = w64 s /\ getr (ms_regs ms3) 10 = w64 s.

End c.
End b.
End a.
