(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryRawDefs), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACeg.v. *)
(* The cuts of the hand-built allocation phase of LLVMFuzzerTestOneInput on the ASan build
   (fuzz_grant.c:363-387; slots 0xbfc .. 0xd08 of the listing, 0x812ac .. 0x813b8).

   The phase marks `raw` usable (shadow byte 70 of the frame := 2), reads raw.base and
   raw.width from the input (each read preceded by the check of its shadow byte), allocates
   the 4352-byte sweep buffer, calls reac_grant_build_sweep on the hand-built allocation,
   checks its answer against reac_grant_alloc_fits, makes the two calls that must be refused
   (a null sweep, a null allocation) and frees the buffer. Every branch to the error path
   (0x81a0c, abort; 0x81a3c / 0x81a70, the slow paths of the input checks) is not taken.

   The phase is cut before each call it makes:
     GP_raw  0xbfc (0x812ac)  GI_raw (GrantEntryDefs.v)
     GR_mal  0xc78 (0x81328)  jal malloc, a0 = 4352
     GR_bs1  0xc90 (0x81340)  jal reac_grant_build_sweep (s, 128, &raw, t)
     GR_fit  0xca4 (0x81354)  jal reac_grant_alloc_fits (raw.base, raw.width)
     GR_bs2  0xcdc (0x8138c)  jal reac_grant_build_sweep (NULL, 1, &raw, t)
     GR_bs3  0xcf8 (0x813a8)  jal reac_grant_build_sweep (s, 128, NULL, t)
     GR_free 0xd04 (0x813b4)  jal free (s)
     GP_sched0 0xd08 (0x813b8) GI_sched0 (GrantEntryDefs.v)
   Each segment lemma has the shape `ge_from POST G_next -> ge_from POST G_self`. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal GrantSyms GrantList GrantPa GrantPaLib GrantBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import GrantEntryDefs HeadampTxEffective GrantBuildSweep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel GrantModel GrantSweepModel BuildSweepModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require GrantSlotPlan SlotNeeds_c.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the pcs of the cuts, as offsets in the listing (address - 0x806b0) ---- *)
Definition GR_hd : Z := 0xc04.    (* 0x812b4, inside the head *)
Definition GR_mal : Z := 0xc78.   (* 0x81328 *)
Definition GR_bs1 : Z := 0xc90.   (* 0x81340 *)
Definition GR_fit : Z := 0xca4.   (* 0x81354 *)
Definition GR_bs2 : Z := 0xcdc.   (* 0x8138c *)
Definition GR_bs3 : Z := 0xcf8.   (* 0x813a8 *)
Definition GR_free : Z := 0xd04.  (* 0x813b4 *)

(* The sweep buffer the harness allocates: 34 rows of 128 bytes. *)
Definition RAW_SW : Z := 4352.

(* ---- reac_grant_build_sweep's contract, as a Theorem Labs lane stated it (2026-10-28) ---- *)
(* The stack it needs. *)
Definition RB_TBGS_STK : Z := 1632 + (128 + (160 + ESTACK)).
Definition RB_TBSW_STK : Z := 208 + Z.max TEFF_STK RB_TBGS_STK.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.

(* The statement of `treac_grant_build_sweep_spec` (a Theorem Labs lane, lib/A/Prog/GrantBuildSweep.v),
   restated so that the segments were proved before that file landed; `traw_bsw_of` below
   derives it from a Theorem Labs lane's Definition. *)
Definition traw_bsw_spec : Prop := forall ly S W (regs : bvmap 5 word) mem md ch0 (s mx al tx base w : Z) (T : list byte),
 afn_pre SEGS B RB_TBSW_STK ly S W regs mem md ch0 -> Z.of_nat (length (frames S)) <= 7 -> spZ regs + 32 <= ly_top ly ->
 arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
 getr regs 10 = w64 s -> getr regs 11 = w64 mx -> getr regs 12 = w64 al -> getr regs 13 = w64 tx ->
 0 <= s < 2 ^ 63 -> -2 ^ 31 <= mx < 2 ^ 31 -> 0 <= al < 2 ^ 64 ->
 (al <> 0 -> afobj SEGS B ly S W mem al 2 /\ garr8 SEGS (mrestrict (w_H W) mem) al [base; w]) ->
 In (tx, TX_SIZE) (ablocks B ly S) -> length T = 460%nat -> obj_at SEGS (mrestrict (w_H W) mem) tx LAY_TX (tx_vals T) ->
 tx_set01 T -> tx_legal T ->
 (bsw_ok s al mx base w = true -> exists sb sn, In (sb, sn) (ablocks B ly S) /\ sb <= s /\ s + 34 * (8 + 3 * w) <= sb + sn) ->
 SRr SEGS W (cfg_at SEGS (BASE + AF_reac_grant_build_sweep) regs mem md)
  (apost_base SEGS B RB_TBSW_STK (if bsw_ok s al mx base w then [(s, s + 34 * (8 + 3 * w))] else []) regs ly S W mem md 0
   (fun ly' S' W' regs' mem' md' => frames S' = frames S /\ ablocks B ly' S' = ablocks B ly S /\ (exists f, S' = set_fs f S) /\
     getr regs' 10 = w64 (if bsw_ok s al mx base w then 8 + 3 * w else -1) /\
     (bsw_ok s al mx base w = true -> garr8 SEGS (mrestrict (w_H W') mem') s
        (map bv_unsigned (SWEEP base (Z.to_nat w) (sweep_vals T tx base (Z.to_nat w))))))).

(* a Theorem Labs lane's contract (lib/A/Prog/GrantBuildSweep.v) is this statement: its TBSW_STK is
   2128 + ESTACK = RB_TBSW_STK, and its bsw_FP unfolds to the footprint above. *)
Lemma traw_bsw_of : treac_grant_build_sweep_spec B -> traw_bsw_spec.
Proof. intro H. exact H. Qed.

(* ---- the two bytes of `raw` the input gives (fuzz_grant.c:367-368) ---- *)
Definition raw_b (cx : ecx) : Z := fst (fst (GrantSlotPlan.raw_rd (c_pl cx))).
Definition raw_w (cx : ecx) : Z := snd (fst (GrantSlotPlan.raw_rd (c_pl cx))).
(* The answer reac_grant_build_sweep gives on the hand-built allocation. *)
Definition raw_ans (cx : ecx) : Z := if fits (raw_b cx) (raw_w cx) then 8 + 3 * raw_w cx else -1.

(* The blocks after the sweep buffer `s` was allocated. *)
Definition gblk2 (cx : ecx) (ly3 : alayout) (S3 : astate) (t s : Z) : Prop :=
  ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ++ [(t, 460); (s, RAW_SW)].

(* What every cut of the phase after the head holds: the machine part at pc, the frame's
   shadow with `raw` usable, the registers the phase keeps (s4 the table, s5 the shadow
   offset, s6 the frame's shadow base, s8 the bytes of input left, s9 the address of raw),
   the input position in slot 88, the late spill slots, the two bytes of raw, the two
   arrays of the frame and the facts about the tables that the scheduler needs. *)
Definition rcore (cx : ecx) (fp pc t : Z) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  ge_body cx fp pc W3 ms3 GSH_raw /\ c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 20 = w64 t /\ getr (ms_regs ms3) 21 = w64 SHADOW_OFF /\
  getr (ms_regs ms3) 22 = w64 (gSH cx fp) /\
  getr (ms_regs ms3) 24 = w64 (c_n cx - Z.of_nat (GrantSlotPlan.pos_raw (c_pl cx))) /\
  getr (ms_regs ms3) 25 = w64 (gF cx fp + GO_RAW) /\
  gslot cx W3 ms3 88 (c_p cx + Z.of_nat (GrantSlotPlan.pos_raw (c_pl cx))) /\
  gslots_late cx fp W3 ms3 /\
  gfb cx fp W3 ms3 GO_RAW (raw_b cx) /\ gfb cx fp W3 ms3 (GO_RAW + 1) (raw_w cx) /\
  gfarr cx fp W3 ms3 GO_WAS (GrantSlotPlan.ws_end (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_SET (GrantSlotPlan.st_end (c_pl cx)) /\
  GrantSlotPlan.Hrel (GrantSlotPlan.T_end (c_pl cx)) (GrantSlotPlan.ws_end (c_pl cx))
    (GrantSlotPlan.st_end (c_pl cx)) /\ SlotNeeds_c.I1 (GrantSlotPlan.T_end (c_pl cx)).

(* 0x812b4, inside the head: raw is marked usable (shadow byte 70 = 2) and `beqz s8` splits
   on the bytes of input left. The head is cut here so that each case is its own lemma. *)
Definition GR_hdI (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t : Z,
  ge_body cx fp GR_hd W3 ms3 GSH_raw /\ k <= 3 /\ acc <= GE_A2 MT /\
  gblk1 B cx ly3 S3 t /\ c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 20 = w64 t /\ getr (ms_regs ms3) 21 = w64 SHADOW_OFF /\
  getr (ms_regs ms3) 22 = w64 (gSH cx fp) /\
  getr (ms_regs ms3) 24 = w64 (c_n cx - Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  getr (ms_regs ms3) 25 = w64 (gF cx fp + GO_RAW) /\
  gslot cx W3 ms3 88 (c_p cx + Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  gslots_late cx fp W3 ms3 /\
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

(* 0x81328: raw holds the input's two bytes; malloc(4352) is called next. *)
Definition GR_malI (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t : Z,
  rcore cx fp GR_mal t W3 ms3 /\ k <= 3 /\ acc <= GE_A2 MT /\
  gblk1 B cx ly3 S3 t /\ gtab B cx ly3 S3 W3 ms3 t (GrantSlotPlan.T_end (c_pl cx)) /\
  getr (ms_regs ms3) 10 = w64 RAW_SW.

(* 0x81340: the sweep buffer s is allocated (s2); reac_grant_build_sweep (s, 128, &raw, t)
   is called next. *)
Definition GR_bs1I (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t s : Z,
  rcore cx fp GR_bs1 t W3 ms3 /\ k <= 4 /\ acc <= GE_A2 MT + mo_malloc MT RAW_SW /\
  gblk2 cx ly3 S3 t s /\ gtab B cx ly3 S3 W3 ms3 t (GrantSlotPlan.T_end (c_pl cx)) /\
  4096 <= s /\ getr (ms_regs ms3) 18 = w64 s /\
  getr (ms_regs ms3) 10 = w64 s /\ getr (ms_regs ms3) 11 = w64 128 /\
  getr (ms_regs ms3) 12 = w64 (gF cx fp + GO_RAW) /\ getr (ms_regs ms3) 13 = w64 t.

(* 0x81354: reac_grant_build_sweep gave its answer (s7); reac_grant_alloc_fits (raw.base,
   raw.width) is called next. *)
Definition GR_fitI (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t s : Z,
  rcore cx fp GR_fit t W3 ms3 /\ k <= 4 /\ acc <= GE_A2 MT + mo_malloc MT RAW_SW /\
  gblk2 cx ly3 S3 t s /\ gtab B cx ly3 S3 W3 ms3 t (GrantSlotPlan.T_end (c_pl cx)) /\
  4096 <= s /\ getr (ms_regs ms3) 18 = w64 s /\
  getr (ms_regs ms3) 23 = w64 (raw_ans cx) /\
  getr (ms_regs ms3) 10 = w64 (raw_b cx) /\ getr (ms_regs ms3) 11 = w64 (raw_w cx).

(* 0x8138c: the answer agreed with reac_grant_alloc_fits; reac_grant_build_sweep (NULL, 1,
   &raw, t) is called next. *)
Definition GR_bs2I (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t s : Z,
  rcore cx fp GR_bs2 t W3 ms3 /\ k <= 4 /\ acc <= GE_A2 MT + mo_malloc MT RAW_SW /\
  gblk2 cx ly3 S3 t s /\ gtab B cx ly3 S3 W3 ms3 t (GrantSlotPlan.T_end (c_pl cx)) /\
  4096 <= s /\ getr (ms_regs ms3) 18 = w64 s /\
  getr (ms_regs ms3) 10 = w64 0 /\ getr (ms_regs ms3) 11 = w64 1 /\
  getr (ms_regs ms3) 12 = w64 (gF cx fp + GO_RAW) /\ getr (ms_regs ms3) 13 = w64 t.

(* 0x813a8: the null sweep was refused (s3 = -1); reac_grant_build_sweep (s, 128, NULL, t)
   is called next. *)
Definition GR_bs3I (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t s : Z,
  rcore cx fp GR_bs3 t W3 ms3 /\ k <= 4 /\ acc <= GE_A2 MT + mo_malloc MT RAW_SW /\
  gblk2 cx ly3 S3 t s /\ gtab B cx ly3 S3 W3 ms3 t (GrantSlotPlan.T_end (c_pl cx)) /\
  4096 <= s /\ getr (ms_regs ms3) 18 = w64 s /\ getr (ms_regs ms3) 19 = w64 (-1) /\
  getr (ms_regs ms3) 10 = w64 s /\ getr (ms_regs ms3) 11 = w64 128 /\
  getr (ms_regs ms3) 12 = w64 0 /\ getr (ms_regs ms3) 13 = w64 t.

(* 0x813b4: the null allocation was refused; free (s) is called next. *)
Definition GR_freeI (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t s : Z,
  rcore cx fp GR_free t W3 ms3 /\ k <= 4 /\ acc <= GE_A2 MT + mo_malloc MT RAW_SW /\
  gblk2 cx ly3 S3 t s /\ gtab B cx ly3 S3 W3 ms3 t (GrantSlotPlan.T_end (c_pl cx)) /\
  4096 <= s /\ getr (ms_regs ms3) 18 = w64 s /\ getr (ms_regs ms3) 10 = w64 s.

End c.
End b.
End a.
