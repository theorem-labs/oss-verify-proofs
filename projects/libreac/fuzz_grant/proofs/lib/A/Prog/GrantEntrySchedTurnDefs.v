(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySchedTurnDefs), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AB1w.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACa1.v. *)
(* One turn of the scheduler's frame loop in fuzz_grant's entry function
   LLVMFuzzerTestOneInput (0x806b0) on the ASan build: slots 0x815c4 .. 0x817c8
   (GP_sched .. GP_freeT), fuzz_grant.c:396-449, with the error slots 0x8178c..0x817c4
   and 0x81b1c..0x81b2c.

   One turn marks the three one-byte cells `ch`, `param`, `value` (F+784, F+800, F+816)
   usable in the shadow, writes s10 into each, calls reac_headamp_tx_next, checks its
   answer with reac_headamp_tx_effective and reac_headamp_default and against the
   harness's own tables, counts an unset cell in `unset_sent`, marks the three cells
   unusable again and turns. Every check that ends in abort() is discharged from
   HeadampSched.frame_ok, the address-free statement of the five checks.

   The turn is cut at the slots where the paths join and around each call:
     GP_sched 0xf14 (0x815c4)  the head of the loop (GI_sched)
     GP_nx    0xf40 (0x815f0)  reac_headamp_tx_next has returned
     GP_eff   0xf74 (0x81624)  before the call of reac_headamp_tx_effective
     GP_effr  0xf7c (0x8162c)  reac_headamp_tx_effective has returned
     GP_dfl   0xff4 (0x816a4)  the call of reac_headamp_default
     GP_scn   0xffc (0x816ac)  the scene and unset checks
     GP_end   0x10c4 (0x81774) the end of the turn
   and the loop is an induction on the turns left. *)
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
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaJournal GrantSyms GrantList GrantPa GrantPaLib GrantBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import YC85 GrantFrame YC1h YC1g ACj1 GrantACjr.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
GrantEntryDefs GrantEntrySeat HeadampTxEffective HeadampDefault HeadampTxNext.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require
HeadampModel NextModel GrantModel SlotNeeds_c GrantSlotPlan HeadampSched SegSetModel Seg_sched_turn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* This file wants lia to turn / and mod into equations, so it sets zify's euclidean-division flag true itself. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition GP_nx : Z := 0xf40.
Definition GP_eff : Z := 0xf74.
Definition GP_effr : Z := 0xf7c.
Definition GP_dfl : Z := 0xff4.
Definition GP_scn : Z := 0xffc.
Definition GP_end : Z := 0x10c4.

(* The frame's shadow while a turn runs: the three cells marked usable, one byte each. *)
Definition GSH_turn : list Z := gsh_set (gsh_set (gsh_set GSH_sched 98 1 1) 100 1 1) 102 1 1.

(* dm poses the two facts of x / c and x mod c by hand; lia here also turns / and mod into equations
   (the flag is true from :53). *)
Ltac dm x c :=
  let H1 := fresh "DM" in let H2 := fresh "DM" in
  pose proof (Z.div_mod x c ltac:(lia)) as H1; pose proof (Z.mod_pos_bound x c ltac:(lia)) as H2.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation SIGMA := (pa_sigma).
#[local] Notation BASE := (pa_val A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.

(* What every cut of the turn carries: the body, the budget, the blocks, the registers
   the loop keeps, the spill slots and the harness's tables; `tcom` adds the turn count. *)
Definition tbody (cx : ecx) (fp pc : Z) (sh : list Z) (t k acc : Z) (ly3 : alayout) (S3 : astate)
  (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  ge_body cx fp pc W3 ms3 sh /\ k <= 5 /\ acc <= GE_A3 MT /\
  gblk1 B cx ly3 S3 t /\ c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 20 = w64 t /\
  getr (ms_regs ms3) 21 = w64 (gF cx fp + GO_PAR) /\
  getr (ms_regs ms3) 22 = w64 (gSH cx fp) /\
  getr (ms_regs ms3) 23 = w64 47 /\ getr (ms_regs ms3) 24 = w64 1 /\
  getr (ms_regs ms3) 25 = w64 (-8) /\ getr (ms_regs ms3) 27 = w64 2 /\
  (let '(sb, sw, per, fr, pe) := GrantSlotPlan.sched_rd (c_pl cx) in
     gslot cx W3 ms3 96 sb /\ gslot cx W3 ms3 88 (sb + sw) /\
     gslot cx W3 ms3 120 (GrantSlotPlan.sched_flag (c_pl cx))) /\
  gslots_late cx fp W3 ms3 /\
  gfarr cx fp W3 ms3 GO_WAS (GrantSlotPlan.ws_end (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_SET (GrantSlotPlan.st_end (c_pl cx)) /\
  GrantSlotPlan.Hrel (GrantSlotPlan.T_end (c_pl cx)) (GrantSlotPlan.ws_end (c_pl cx)) (GrantSlotPlan.st_end (c_pl cx)).

Definition tcom (cx : ecx) (fp pc : Z) (sh : list Z) (i : nat) (t k acc : Z) (ly3 : alayout) (S3 : astate)
  (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  tbody cx fp pc sh t k acc ly3 S3 W3 ms3 /\
  Z.of_nat i < GrantSlotPlan.frames (c_pl cx) /\
  getr (ms_regs ms3) 18 = w64 (Z.of_nat i - GrantSlotPlan.frames (c_pl cx)).

Definition gcut := ecx -> Z -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop.

(* The head of the loop with `m` turns left. *)
Definition GSn (m : nat) : gcut :=
  fun cx fp k acc ly3 S3 W3 ms3 md3 =>
  GI_sched B MT cx fp k acc ly3 S3 W3 ms3 md3 /\ getr (ms_regs ms3) 18 = w64 (- Z.of_nat m) /\ (m < 4097)%nat.

(* reac_headamp_tx_next has returned: its answer is next_model of the table the
   scheduler left after `i` turns. *)
Definition TB (m : nat) : gcut :=
  fun cx fp k acc ly3 S3 W3 ms3 md3 =>
  exists (i : nat) (t : Z) (T us : list byte) (r c p v : Z) (T' : list byte),
  tcom cx fp GP_nx GSH_turn i t k acc ly3 S3 W3 ms3 /\
  GrantSlotPlan.frames (c_pl cx) - Z.of_nat i = Z.of_nat m /\
  getr (ms_regs ms3) 19 = w64 (gF cx fp + GO_CH) /\
  GrantSlotPlan.sched_at (c_pl cx) t i = (T, us) /\ NextModel.next_model T t = (r, (c, p, v), T') /\
  getr (ms_regs ms3) 10 = w64 r /\ gtab B cx ly3 S3 W3 ms3 t T' /\
  length us = 144%nat /\ gfarr cx fp W3 ms3 GO_UNSET us /\
  (r = 1 -> gfb cx fp W3 ms3 GO_CH c /\ gfb cx fp W3 ms3 GO_PAR p /\ gfb cx fp W3 ms3 GO_VAL v).

(* The record went out (r = 1); what every later cut of that path carries. *)
Definition trec (cx : ecx) (fp pc : Z) (m : nat) (k acc : Z) (ly3 : alayout) (S3 : astate)
  (W3 : world SEGS) (ms3 : machine_state) (i : nat) (t : Z) (T us : list byte) (c p v : Z) (T' : list byte) : Prop :=
  tcom cx fp pc GSH_turn i t k acc ly3 S3 W3 ms3 /\
  GrantSlotPlan.frames (c_pl cx) - Z.of_nat i = Z.of_nat m /\
  GrantSlotPlan.sched_at (c_pl cx) t i = (T, us) /\ NextModel.next_model T t = (1, (c, p, v), T') /\
  gtab B cx ly3 S3 W3 ms3 t T' /\ length us = 144%nat /\ gfarr cx fp W3 ms3 GO_UNSET us /\
  gfb cx fp W3 ms3 GO_CH c /\ gfb cx fp W3 ms3 GO_PAR p /\ gfb cx fp W3 ms3 GO_VAL v.

(* 0x81624: the value is legal for its parameter; a1, a2 and s3 hold ch, param, value. *)
Definition TC (m : nat) : gcut :=
  fun cx fp k acc ly3 S3 W3 ms3 md3 =>
  exists i t T us c p v T', trec cx fp GP_eff m k acc ly3 S3 W3 ms3 i t T us c p v T' /\
  getr (ms_regs ms3) 11 = w64 c /\ getr (ms_regs ms3) 12 = w64 p /\ getr (ms_regs ms3) 19 = w64 v.

(* 0x8162c: reac_headamp_tx_effective has returned. *)
Definition TCr (m : nat) : gcut :=
  fun cx fp k acc ly3 S3 W3 ms3 md3 =>
  exists i t T us c p v T', trec cx fp GP_effr m k acc ly3 S3 W3 ms3 i t T us c p v T' /\
  getr (ms_regs ms3) 10 = w64 (HeadampModel.eff T' t c p) /\ getr (ms_regs ms3) 19 = w64 v.

(* 0x816a4: the cell was not set by the input; a0 holds param, s3 the value. *)
Definition TD (m : nat) : gcut :=
  fun cx fp k acc ly3 S3 W3 ms3 md3 =>
  exists i t T us c p v T', trec cx fp GP_dfl m k acc ly3 S3 W3 ms3 i t T us c p v T' /\
  getr (ms_regs ms3) 10 = w64 p /\ getr (ms_regs ms3) 19 = w64 v /\
  HeadampModel.tb (GrantSlotPlan.ws_end (c_pl cx)) (3 * c + p) = 0.

(* 0x816ac: the value check is done; the scene and unset checks follow. *)
Definition TE (m : nat) : gcut :=
  fun cx fp k acc ly3 S3 W3 ms3 md3 =>
  exists i t T us c p v T', trec cx fp GP_scn m k acc ly3 S3 W3 ms3 i t T us c p v T'.

(* 0x81774: the turn's checks are done; the scheduler state is that of turn i + 1. *)
Definition TF (m : nat) : gcut :=
  fun cx fp k acc ly3 S3 W3 ms3 md3 =>
  exists (i : nat) (t : Z) (T' us' : list byte),
  tcom cx fp GP_end GSH_turn i t k acc ly3 S3 W3 ms3 /\
  GrantSlotPlan.frames (c_pl cx) - Z.of_nat i = Z.of_nat m /\
  getr (ms_regs ms3) 19 = w64 (gF cx fp + GO_CH) /\
  GrantSlotPlan.sched_at (c_pl cx) t (S i) = (T', us') /\
  gtab B cx ly3 S3 W3 ms3 t T' /\ SlotNeeds_c.I1 T' /\ length us' = 144%nat /\ gfarr cx fp W3 ms3 GO_UNSET us'.

(* The addresses a turn may write, and the addresses whose bytes the cuts track. *)
Definition gwr (cx : ecx) (fp a : Z) : Prop :=
  (gF cx fp + GO_UNSET <= a < gF cx fp + GO_UNSET + 144) \/
  a = gF cx fp + GO_CH \/ a = gF cx fp + GO_PAR \/ a = gF cx fp + GO_VAL \/
  a = gSH cx fp + 98 \/ a = gSH cx fp + 100 \/ a = gSH cx fp + 102.
Definition gtracked (cx : ecx) (fp a : Z) : Prop :=
  (c_sp1 cx <= a < spZ (c_regs cx)) \/
  (exists b n, In (b, n) (ablocks B (c_ly cx) (c_S cx)) /\ b <= a < b + req_size n) \/
  (gF cx fp <= a < gF cx fp + 1024) \/ (gSH cx fp <= a < gSH cx fp + 128).

(* The registers every cut of the turn names. *)
Definition gtregs (r3 r4 : bvmap 5 word) : Prop :=
  getr r4 2 = getr r3 2 /\ getr r4 3 = getr r3 3 /\ getr r4 4 = getr r3 4 /\
  getr r4 8 = getr r3 8 /\ getr r4 9 = getr r3 9 /\
  getr r4 20 = getr r3 20 /\ getr r4 21 = getr r3 21 /\ getr r4 22 = getr r3 22 /\
  getr r4 23 = getr r3 23 /\ getr r4 24 = getr r3 24 /\ getr r4 25 = getr r3 25 /\
  getr r4 27 = getr r3 27.

Section d.
Hypothesis LAWS : AR_laws SEGS B.

Lemma fsb4 : fs_frame_bytes GE_CID = 1024.
Proof. reflexivity. Qed.

(* What a cut's context gives about the frame and the stack. *)
Lemma gctx : forall cx fp k ly3 S3 W3 mem3 md3,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 mem3 md3 k ->
  frames S3 = [(GE_CID, fp)] ->
  frame_addr ly3 GE_CID fp = gF cx fp /\
  4096 <= gF cx fp /\ gF cx fp + 1024 <= alloc_ceiling /\ in_app (gF cx fp) 1024 /\ gF cx fp mod 64 = 0 /\
  gSH cx fp = SHADOW_OFF + gF cx fp / 8 /\
  alloc_ceiling <= spZ (c_regs cx) - GE_STK /\ spZ (c_regs cx) <= 2 ^ 47 /\ spZ (c_regs cx) mod 16 = 0 /\
  spZ (c_regs cx) - 320 <= c_sp1 cx <= spZ (c_regs cx) - 288 /\ c_sp1 cx mod 32 = 0.
Proof.
  intros cx fp k ly3 S3 W3 mem3 md3 HB HJ Hfr.
  destruct HB as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _).
  pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof HJ as (HAR3 & HLY & _).
  assert (Hin : In (GE_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
  assert (EFA : frame_addr ly3 GE_CID fp = gF cx fp).
  { unfold gF, frame_addr. destruct HLY as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ GE_CID fp HAR3 Hin) as (HF4096 & HFceil & HFapp).
  destruct (frame_al64 SEGS B _ _ _ _ _ GE_CID fp HAR3 Hin) as (HF64 & _).
  rewrite EFA in HF4096, HFceil, HFapp, HF64. rewrite fsb4 in HFceil, HFapp.
  assert (GS : GE_STK = 32768) by reflexivity.
  pose proof (Z.mul_div_le (spZ (c_regs cx) + -288) 32 ltac:(lia)) as D1.
  pose proof (Z.div_mod (spZ (c_regs cx) + -288) 32 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) + -288) 32 ltac:(lia)) as D3.
  split; [exact EFA|]. split; [exact HF4096|]. split; [exact HFceil|]. split; [exact HFapp|]. split; [exact HF64|].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact Hal16|].
  split; [rewrite Hsp1; lia|]. rewrite Hsp1. rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

(* The addresses the cuts track and the turn does not write. *)
Lemma gaddr_ok : forall cx fp,
  4096 <= gF cx fp -> gF cx fp + 1024 <= alloc_ceiling -> in_app (gF cx fp) 1024 ->
  alloc_ceiling <= spZ (c_regs cx) - GE_STK -> spZ (c_regs cx) - 320 <= c_sp1 cx <= spZ (c_regs cx) - 288 ->
  (forall a, c_sp1 cx <= a < spZ (c_regs cx) -> gtracked cx fp a /\ ~ gwr cx fp a) /\
  (forall a, (gF cx fp <= a < gF cx fp + GO_UNSET \/ gF cx fp + 1016 <= a < gF cx fp + 1024) ->
     gtracked cx fp a /\ ~ gwr cx fp a) /\
  (forall j, 0 <= j < 128 -> j <> 98 -> j <> 100 -> j <> 102 ->
     gtracked cx fp (gSH cx fp + j) /\ ~ gwr cx fp (gSH cx fp + j)).
Proof.
  intros cx fp HF4096 HFceil HFapp Hceil Hsp1.
  pose proof asan_consts as (C1 & _).
  assert (GS : GE_STK = 32768) by reflexivity.
  assert (HSH : gSH cx fp = SHADOW_OFF + gF cx fp / 8) by reflexivity.
  assert (Hsep : gSH cx fp + 128 <= gF cx fp \/ gF cx fp + 1024 <= gSH cx fp).
  { rewrite HSH. dm (gF cx fp) 8. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *.
    destruct HFapp as (_ & [Hlo | (Hhi & _)]); [right | left]; lia. }
  assert (Hshi : gSH cx fp + 128 <= alloc_ceiling).
  { rewrite HSH. dm (gF cx fp) 8. unfold SHADOW_OFF. lia. }
  unfold gtracked, gwr, GO_UNSET, GO_CH, GO_PAR, GO_VAL.
  split; [|split].
  - intros a Ha. split; [left; exact Ha|]. lia.
  - intros a Ha. split; [right; right; left; lia|]. lia.
  - intros j Hj H98 H100 H102. split; [right; right; right; lia|]. lia.
Qed.

(* The bytes of the input block are tracked and not written. *)
Lemma ginput_ok : forall cx fp k ly3 S3 W3 mem3 md3 t,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 mem3 md3 k ->
  frames S3 = [(GE_CID, fp)] -> gblk1 B cx ly3 S3 t ->
  forall a, c_p cx <= a < c_p cx + c_n cx -> gtracked cx fp a /\ ~ gwr cx fp a.
Proof.
  intros cx fp k ly3 S3 W3 mem3 md3 t HB HJ Hfr Hbl a Ha.
  destruct (gctx cx fp k ly3 S3 W3 mem3 md3 HB HJ Hfr) as (EFA & HF4096 & HFceil & HFapp & _ & HSH & _).
  pose proof HB as (_ & _ & _ & Hpn & _).
  destruct Hpn as [(Hn0 & _) | (Hn & Hin0)]; [lia|].
  assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3)) by (rewrite Hbl; apply in_app_iff; left; exact Hin0).
  assert (Hfin : In (GE_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
  pose proof (proj1 HJ) as HAR3.
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ GE_CID fp HAR3 Hin3 Hfin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA, fsb4 in Hd.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (_ & _ & _ & Happ & _).
  assert (Hrq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
  rewrite Hrq in Hd, Happ.
  pose proof asan_consts as (C1 & _).
  split; [right; left; exists (c_p cx), (c_n cx); split; [exact Hin0 | rewrite Hrq; lia]|].
  unfold gwr, GO_UNSET, GO_CH, GO_PAR, GO_VAL. rewrite HSH.
  unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *.
  dm (gF cx fp) 8.
  intros [HW | [HW | [HW | [HW | [HW | [HW | HW]]]]]]; clear - HW Hd Happ Ha Hn HFapp HFceil C1 DM DM0; lia.
Qed.

(* A cut's body carries over to a later state that agrees on the tracked bytes the
   turn does not write, and keeps the registers the turn names. *)
Lemma tbody_keep : forall cx fp pc pc' sh sh' t k acc ly3 S3 W3 ms3 W4 ms4,
  4096 <= gF cx fp -> gF cx fp + 1024 <= alloc_ceiling -> in_app (gF cx fp) 1024 ->
  alloc_ceiling <= spZ (c_regs cx) - GE_STK -> spZ (c_regs cx) - 320 <= c_sp1 cx <= spZ (c_regs cx) - 288 ->
  (forall a, c_p cx <= a < c_p cx + c_n cx -> gtracked cx fp a /\ ~ gwr cx fp a) ->
  tbody cx fp pc sh t k acc ly3 S3 W3 ms3 ->
  ms_pc_val ms4 = w64 (BASE + pc') -> ms_resv ms4 = None -> ms_svc_pending ms4 = None ->
  ms_rom ms4 = seg_rom SEGS -> ms_fregs ms4 = fp_regs -> ms_fcsr ms4 = fp_csr ->
  gtregs (ms_regs ms3) (ms_regs ms4) ->
  (forall a, gtracked cx fp a -> ~ gwr cx fp a ->
     aview SEGS (w_H W4) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  gshadow cx fp W4 ms4 sh' -> length sh' = GE_NSH ->
  tbody cx fp pc' sh' t k acc ly3 S3 W4 ms4.
Proof.
  intros cx fp pc pc' sh sh' t k acc ly3 S3 W3 ms3 W4 ms4 HF4096 HFceil HFapp Hceil Hsp1 HIN HT
    Hpc Hrv Hsvc Hrom Hfr Hfc HR HK Hsh Hlen.
  destruct (gaddr_ok cx fp HF4096 HFceil HFapp Hceil Hsp1) as (KS & KF & _).
  assert (KV : forall a, gtracked cx fp a /\ ~ gwr cx fp a ->
     aview SEGS (w_H W4) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a) by (intros a [H1 H2]; exact (HK a H1 H2)).
  assert (KSL : forall off v, 8 <= off <= 176 -> gslot cx W3 ms3 off v -> gslot cx W4 ms4 off v).
  { intros off v Hoff Hs. unfold gslot in *. rewrite <- Hs. apply rdword_ext. intros kk Hkk. apply KV, KS. lia. }
  assert (KAR : forall off l, 0 <= off -> off + Z.of_nat (length l) <= GO_UNSET ->
     gfarr cx fp W3 ms3 off l -> gfarr cx fp W4 ms4 off l).
  { intros off l Ho Hl Ha. unfold gfarr in *. eapply garr8_frame; [exact Ha|]. intros a Hra.
    apply (mbyte_of_aview SEGS). apply KV, KF. rewrite length_map in Hra. lia. }
  destruct HT as ((Hpc3 & Hrv3 & Hsvc3 & Hrom3 & Hfr3 & Hfc3 & HG & HS & _ & HFL & _ & HINP) &
    Hk & Hacc & Hbl & Hn & R20 & R21 & R22 & R23 & R24 & R25 & R27 & HSC & HSL & HWS & HST & HH).
  destruct HR as (Q2 & Q3 & Q4 & Q8 & Q9 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & Q27).
  split.
  { split; [exact Hpc|]. split; [exact Hrv|]. split; [exact Hsvc|]. split; [exact Hrom|].
    split; [exact Hfr|]. split; [exact Hfc|].
    split; [destruct HG as (G2 & G8 & G9 & G3 & G4); unfold gregs; rewrite Q2, Q8, Q9, Q3, Q4; tauto|].
    split.
    { destruct HS as (S8 & S16). split.
      - rewrite <- S8. apply rdword_ext. intros kk Hkk. apply KV, KS. lia.
      - intros j Hj. rewrite <- (S16 j Hj). apply rdword_ext. intros kk Hkk. apply KV, KS. lia. }
    split; [exact Hsh|].
    split; [rewrite <- HFL; apply rdword_ext; intros kk Hkk; apply KV, KF; lia|].
    split; [exact Hlen|].
    eapply garr8_frame; [exact HINP|]. intros a Hra. apply (mbyte_of_aview SEGS). apply KV, HIN.
    rewrite length_map in Hra. unfold c_n. lia. }
  split; [exact Hk|]. split; [exact Hacc|]. split; [exact Hbl|]. split; [exact Hn|].
  split; [rewrite Q20; exact R20|]. split; [rewrite Q21; exact R21|].
  split; [rewrite Q22; exact R22|]. split; [rewrite Q23; exact R23|]. split; [rewrite Q24; exact R24|].
  split; [rewrite Q25; exact R25|]. split; [rewrite Q27; exact R27|].
  split.
  { destruct (GrantSlotPlan.sched_rd (c_pl cx)) as [[[[sb sw] per] fr] pe].
    destruct HSC as (S96 & S88 & S120). split; [|split]; apply KSL; first [lia | assumption]. }
  split.
  { destruct HSL as ((M16 & M24 & M48 & M56 & M136 & M144 & M152 & M176) & L8 & L32 & L40 & L72 & L80 & L104 & L112 & L128).
    repeat split; apply KSL; first [lia | assumption]. }
  split; [apply KAR; [unfold GO_WAS; lia | | exact HWS]|].
  { pose proof (proj1 (proj2 (SegSetModel.tables_end_inv (c_pl cx)))) as Lw.
    rewrite Lw. unfold GO_WAS, GO_UNSET. lia. }
  split; [apply KAR; [unfold GO_SET; lia | | exact HST]|].
  { pose proof (proj1 (proj2 (proj2 (SegSetModel.tables_end_inv (c_pl cx))))) as Ls.
    rewrite Ls. unfold GO_SET, GO_UNSET. lia. }
  exact HH.
Qed.

Lemma tcom_keep : forall cx fp pc pc' sh sh' i i' t k acc ly3 S3 W3 ms3 W4 ms4,
  4096 <= gF cx fp -> gF cx fp + 1024 <= alloc_ceiling -> in_app (gF cx fp) 1024 ->
  alloc_ceiling <= spZ (c_regs cx) - GE_STK -> spZ (c_regs cx) - 320 <= c_sp1 cx <= spZ (c_regs cx) - 288 ->
  (forall a, c_p cx <= a < c_p cx + c_n cx -> gtracked cx fp a /\ ~ gwr cx fp a) ->
  tcom cx fp pc sh i t k acc ly3 S3 W3 ms3 ->
  ms_pc_val ms4 = w64 (BASE + pc') -> ms_resv ms4 = None -> ms_svc_pending ms4 = None ->
  ms_rom ms4 = seg_rom SEGS -> ms_fregs ms4 = fp_regs -> ms_fcsr ms4 = fp_csr ->
  gtregs (ms_regs ms3) (ms_regs ms4) ->
  Z.of_nat i' < GrantSlotPlan.frames (c_pl cx) ->
  getr (ms_regs ms4) 18 = w64 (Z.of_nat i' - GrantSlotPlan.frames (c_pl cx)) ->
  (forall a, gtracked cx fp a -> ~ gwr cx fp a ->
     aview SEGS (w_H W4) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  gshadow cx fp W4 ms4 sh' -> length sh' = GE_NSH ->
  tcom cx fp pc' sh' i' t k acc ly3 S3 W4 ms4.
Proof.
  intros cx fp pc pc' sh sh' i i' t k acc ly3 S3 W3 ms3 W4 ms4 HF4096 HFceil HFapp Hceil Hsp1 HIN (HT & _ & _)
    Hpc Hrv Hsvc Hrom Hfr Hfc HR Hi' R18' HK Hsh Hlen.
  split; [|split; [exact Hi' | exact R18']].
  eapply tbody_keep; eassumption.
Qed.

(* ---- the machine state and the symbolic state ---- *)

Lemma gms_eq : forall H pc (ms : machine_state),
  ms_pc_val ms = w64 (BASE + pc) -> ms_resv ms = None -> ms_svc_pending ms = None ->
  ms_rom ms = seg_rom SEGS -> ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr ->
  restrict H ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + pc)) (mrestrict H (ms_mem ms)) (seg_rom SEGS).
Proof. intros H pc [] Hpc Hrv Hsvc Hrom Hfr Hfc; cbn in *; subst; reflexivity. Qed.

Lemma stf : forall E ss H ms, st_ok_pi SEGS VAL E ss (restrict H ms) -> ss_resv ss = None ->
  ms_pc_val ms = w64 (BASE + ss_pc ss) /\ ms_resv ms = None /\ ms_svc_pending ms = None /\
  ms_rom ms = seg_rom SEGS /\ ms_fregs ms = fp_regs /\ ms_fcsr ms = fp_csr.
Proof.
  intros E ss H ms HS Hrv. unfold st_ok_pi, st_ok, abs_ss, setpc in HS.
  destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & _). cbn [ss_pc ss_resv] in *. rewrite Hrv in H4.
  destruct ms; cbn in *. repeat split; assumption.
Qed.

Lemma length_gsh_set1 : forall sh lo v, (lo < length sh)%nat -> length (gsh_set sh lo 1 v) = length sh.
Proof.
  intros sh lo v H. unfold gsh_set. rewrite !length_app, repeat_length, length_firstn, length_skipn. lia.
Qed.

Lemma nth_gsh_set1 : forall sh lo v j, (lo < length sh)%nat ->
  nth j (gsh_set sh lo 1 v) 0 = if Nat.eqb j lo then v else nth j sh 0.
Proof.
  intros sh lo v j H. unfold gsh_set.
  assert (Lf : length (firstn lo sh) = lo) by (rewrite length_firstn; lia).
  destruct (Nat.lt_trichotomy j lo) as [Hlt | [-> | Hgt]].
  - rewrite app_nth1 by lia. rewrite nth_firstn. replace (j <? lo)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    replace (Nat.eqb j lo) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity.
  - rewrite app_nth2 by lia. rewrite Lf, Nat.sub_diag, Nat.eqb_refl. reflexivity.
  - rewrite app_nth2 by lia. rewrite Lf. rewrite app_nth2 by (cbn; lia). cbn [length repeat].
    rewrite nth_skipn. replace (Nat.eqb j lo) with false by (symmetry; apply Nat.eqb_neq; lia).
    f_equal. lia.
Qed.

Lemma gshadow_set3 : forall cx fp W3 ms3 W4 ms4 sh v98 v100 v102,
  gshadow cx fp W3 ms3 sh -> length sh = GE_NSH ->
  (forall j, 0 <= j < 104 -> j <> 98 -> j <> 100 -> j <> 102 ->
     aview SEGS (w_H W4) (ms_mem ms4) (gSH cx fp + j) = aview SEGS (w_H W3) (ms_mem ms3) (gSH cx fp + j)) ->
  aview SEGS (w_H W4) (ms_mem ms4) (gSH cx fp + 98) = Some v98 ->
  aview SEGS (w_H W4) (ms_mem ms4) (gSH cx fp + 100) = Some v100 ->
  aview SEGS (w_H W4) (ms_mem ms4) (gSH cx fp + 102) = Some v102 ->
  gshadow cx fp W4 ms4 (gsh_set (gsh_set (gsh_set sh 98 1 v98) 100 1 v100) 102 1 v102) /\
  length (gsh_set (gsh_set (gsh_set sh 98 1 v98) 100 1 v100) 102 1 v102) = GE_NSH.
Proof.
  intros cx fp W3 ms3 W4 ms4 sh v98 v100 v102 Hsh Hlen HK H98 H100 H102. unfold GE_NSH in Hlen.
  assert (L1 : length (gsh_set sh 98 1 v98) = 104%nat) by (rewrite length_gsh_set1; lia).
  assert (L2 : length (gsh_set (gsh_set sh 98 1 v98) 100 1 v100) = 104%nat) by (rewrite length_gsh_set1; lia).
  assert (L3 : length (gsh_set (gsh_set (gsh_set sh 98 1 v98) 100 1 v100) 102 1 v102) = 104%nat) by (rewrite length_gsh_set1; lia).
  split; [|exact L3].
  intros j Hj. rewrite L3 in Hj.
  rewrite !nth_gsh_set1 by lia.
  destruct (Nat.eqb_spec j 102) as [-> | N102]; [exact H102|].
  destruct (Nat.eqb_spec j 100) as [-> | N100]; [exact H100|].
  destruct (Nat.eqb_spec j 98) as [-> | N98]; [exact H98|].
  rewrite HK by lia. apply Hsh. lia.
Qed.

Lemma chunk1_aview : forall E H mem n lo hi wlo whi cs off e b,
  region_ok SEGS E (mrestrict H mem) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  In (YP09.mkChunk off (CVal 1 e)) cs -> bv_unsigned (ew E n) = b ->
  aview SEGS H mem (b + off) = Some (bv_unsigned (sv_denot E e) mod 256).
Proof.
  intros E H mem n lo hi wlo whi cs off e b (_ & _ & _ & Hcs) Hin Hn.
  pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
  destruct (Hck 0 ltac:(cbn; lia)) as (bb & Hcb & Hm). cbn [YP09.c_off YP09.c_val cbyte] in Hcb, Hm.
  injection Hcb as <-. rewrite Z.add_0_r in Hm. unfold aview. rewrite Hm. cbn [option_map].
  f_equal; try (unfold byte_of_word; rewrite Z.mul_0_r, Z.shiftr_0_r, Z_to_bv_unsigned; reflexivity).
Qed.

Lemma aluw_inc : forall E n x, ew E n = Z_to_bv 64 x -> -4097 <= x < 0 ->
  sv_denot E (SAluw ALU_ADD (SOff n 0) (SLit 1)) = Z_to_bv 64 (x + 1).
Proof.
  intros E n x Hn Hx. transitivity (sv_denot E (SLit (x + 1))); [|reflexivity].
  apply S_inj. rewrite S_SAluw, S_SLit. cbn [zalu_raw]. rewrite U_SOff, U_SLit, Hn.
  rewrite Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap, bv_swrap, bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). change (bv_half_modulus 32) with (2 ^ 31).
  change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 64) with (2 ^ 63).
  lia.
Qed.

Lemma gagree0 : forall regs xs, env_agree 32 (Ereg regs xs) (Eimg (Ereg regs xs)).
Proof. intros regs xs. split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

Lemma gagree_ext : forall E0 E K ws, env_agree 32 E0 E -> (32 <= K)%nat -> env_agree 32 E0 (extK E K ws).
Proof.
  intros E0 E K ws [A1 B1] HK. destruct (env_agree_extK E K ws) as [A2 B2].
  split; [intros n Hn; rewrite A2 by lia; apply A1; lia | congruence].
Qed.

Lemma gpres : forall cx fp k ly3 S3 W3 mem3 md3,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 mem3 md3 k ->
  frames S3 = [(GE_CID, fp)] ->
  (forall j, 0 <= j < 1024 -> apresent (w_H W3) mem3 (gF cx fp + j)) /\
  (forall j, 0 <= j < 128 -> apresent (w_H W3) mem3 (gSH cx fp + j)).
Proof.
  intros cx fp k ly3 S3 W3 mem3 md3 HB HJ Hfr.
  destruct (gctx cx fp k ly3 S3 W3 mem3 md3 HB HJ Hfr) as (EFA & _).
  assert (Hin : In (GE_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
  destruct (al_frames _ _ LAWS _ _ _ _ _ GE_CID fp (proj1 HJ) Hin) as (_ & _ & HFp & HSp).
  rewrite EFA, fsb4 in HFp, HSp. change (1024 / 8) with 128 in HSp.
  split.
  - intros j Hj. apply (proj1 (HFp (gF cx fp + j) ltac:(lia))).
  - intros j Hj. apply (proj1 (HSp j Hj)).
Qed.

(* One byte of the frame's shadow, as a region of its own. *)
Definition shr (o : Z) : YP09.region := YP09.mkRegion (Some 22%nat) o (o + 1) o (o + 1) [].

Lemma shr_ok : forall E m o b, bv_unsigned (ew E 22) = b -> 0 <= b + o -> b + o + 1 <= 2 ^ 64 ->
  writable_at SEGS m (b + o) -> region_ok SEGS E m (shr o).
Proof.
  intros E m o b Hb H0 H1 Hw. unfold region_ok, shr.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hb.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros o' Ho'. replace o' with o by lia. exact Hw.
Qed.

Lemma gtracked_rng : forall cx fp a, ge_base B MT cx -> 4096 <= gF cx fp -> gF cx fp + 1024 <= alloc_ceiling ->
  spZ (c_regs cx) <= 2 ^ 47 -> 0 <= c_sp1 cx -> gtracked cx fp a -> 0 <= a < 2 ^ 64.
Proof.
  intros cx fp a HB HF1 HF2 Hsp Hs1 Ha. pose proof asan_consts as (C1 & _).
  destruct HB as ((HAR0 & _) & _).
  assert (HSH : gSH cx fp = SHADOW_OFF + gF cx fp / 8) by reflexivity.
  unfold gtracked in Ha. destruct Ha as [Ha | [(b & n & Hin & Ha) | [Ha | Ha]]].
  - lia.
  - destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR0 Hin) as (_ & H4 & Hc & _). lia.
  - lia.
  - rewrite HSH in Ha. unfold SHADOW_OFF in Ha. lia.
Qed.

(* The table's bytes lie apart from what a turn writes. *)
Lemma table_out : forall cx fp k ly3 S3 W3 mem3 md3 t,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 mem3 md3 k ->
  frames S3 = [(GE_CID, fp)] -> gblk1 B cx ly3 S3 t ->
  forall j, 0 <= j < 460 -> ~ gwr cx fp (t + j) /\ 0 <= t + j < 2 ^ 64.
Proof.
  intros cx fp k ly3 S3 W3 mem3 md3 t HB HJ Hfr Hbl j Hj.
  destruct (gctx cx fp k ly3 S3 W3 mem3 md3 HB HJ Hfr) as (EFA & HF4096 & HFceil & HFapp & _ & HSH & _).
  assert (Hin3 : In (t, 460) (ablocks B ly3 S3)) by (rewrite Hbl; apply in_app_iff; right; left; reflexivity).
  assert (Hfin : In (GE_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ GE_CID fp (proj1 HJ) Hin3 Hfin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA, fsb4 in Hd. change (req_size 460) with 460 in Hd.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ) Hin3) as (_ & H4 & Hc & Happ & _).
  change (req_size 460) with 460 in Hc, Happ.
  pose proof asan_consts as (C1 & _).
  split; [|lia].
  unfold gwr, GO_UNSET, GO_CH, GO_PAR, GO_VAL. rewrite HSH.
  unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

Lemma gtab_keep : forall cx ly3 S3 W3 ms3 W4 ms4 t T,
  gtab B cx ly3 S3 W3 ms3 t T ->
  (forall j, 0 <= j < 460 -> aview SEGS (w_H W4) (ms_mem ms4) (t + j) = aview SEGS (w_H W3) (ms_mem ms3) (t + j)) ->
  gtab B cx ly3 S3 W4 ms4 t T.
Proof.
  intros cx ly3 S3 W3 ms3 W4 ms4 t T (H1 & H2 & H3 & H4) HK.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. intros j Hj H438 H439 H451. rewrite HK by lia. apply H4; assumption.
Qed.

Lemma gfarr_keep : forall cx fp W3 ms3 W4 ms4 off l,
  gfarr cx fp W3 ms3 off l ->
  (forall a, gF cx fp + off <= a < gF cx fp + off + Z.of_nat (length l) ->
     aview SEGS (w_H W4) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  gfarr cx fp W4 ms4 off l.
Proof.
  intros cx fp W3 ms3 W4 ms4 off l Ha HK. unfold gfarr in *. eapply garr8_frame; [exact Ha|].
  intros a Hra. apply (mbyte_of_aview SEGS). apply HK. rewrite length_map in Hra. lia.
Qed.

Lemma kept2 : forall E1 rs1 E2 rs2 H (m0 m1 m2 : word -> option byte),
  frame_of E1 rs1 (mrestrict H m0) (mrestrict H m1) -> frame_of E2 rs2 (mrestrict H m1) (mrestrict H m2) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E1 rs1 a -> ~ in_wrange E2 rs2 a ->
  aview SEGS H m2 a = aview SEGS H m0 a.
Proof.
  intros E1 rs1 E2 rs2 H m0 m1 m2 F1 F2 a Ha N1 N2.
  rewrite (aview_kept_out E2 rs2 H m1 m2 F2 a Ha N2). exact (aview_kept_out E1 rs1 H m0 m1 F1 a Ha N1).
Qed.

Lemma GI_sched_of : forall cx fp i t k acc ly3 S3 W3 ms3 md3,
  tcom cx fp GP_sched GSH_sched i t k acc ly3 S3 W3 ms3 ->
  getr (ms_regs ms3) 19 = w64 (gF cx fp + GO_CH) ->
  (let '(T, us) := GrantSlotPlan.sched_at (c_pl cx) t i in
     gtab B cx ly3 S3 W3 ms3 t T /\ SlotNeeds_c.I1 T /\ length us = 144%nat /\ gfarr cx fp W3 ms3 GO_UNSET us) ->
  GI_sched B MT cx fp k acc ly3 S3 W3 ms3 md3.
Proof.
  intros cx fp i t k acc ly3 S3 W3 ms3 md3
    ((HBD & Hk & Hacc & Hbl & Hn & R20 & R21 & R22 & R23 & R24 & R25 & R27 & HSC & HSL & HWS & HST & HH) & Hi & R18) R19 HU.
  exists i, t.
  exact (conj HBD (conj Hk (conj Hacc (conj Hbl (conj Hn (conj Hi (conj R18 (conj R19 (conj R20 (conj R21
    (conj R22 (conj R23 (conj R24 (conj R25 (conj R27 (conj HSC (conj HSL (conj HU (conj HWS (conj HST HH)))))))))))))))))))).
Qed.

Lemma tcom_of_GI_sched : forall cx fp k acc ly3 S3 W3 ms3 md3,
  GI_sched B MT cx fp k acc ly3 S3 W3 ms3 md3 ->
  exists i t, tcom cx fp GP_sched GSH_sched i t k acc ly3 S3 W3 ms3 /\
  getr (ms_regs ms3) 19 = w64 (gF cx fp + GO_CH) /\
  (let '(T, us) := GrantSlotPlan.sched_at (c_pl cx) t i in
     gtab B cx ly3 S3 W3 ms3 t T /\ SlotNeeds_c.I1 T /\ length us = 144%nat /\ gfarr cx fp W3 ms3 GO_UNSET us).
Proof.
  intros cx fp k acc ly3 S3 W3 ms3 md3
    (i & t & HBD & Hk & Hacc & Hbl & Hn & Hi & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R27 & HSC & HSL & HU & HWS & HST & HH).
  exists i, t. split; [|split; [exact R19 | exact HU]].
  split; [|split; [exact Hi | exact R18]].
  exact (conj HBD (conj Hk (conj Hacc (conj Hbl (conj Hn (conj R20 (conj R21 (conj R22 (conj R23 (conj R24
    (conj R25 (conj R27 (conj HSC (conj HSL (conj HWS (conj HST HH)))))))))))))))).
Qed.

Lemma GI_freeT_of : forall cx fp t k acc ly3 S3 W3 ms3 md3,
  tbody cx fp GP_freeT GSH_sched t k acc ly3 S3 W3 ms3 ->
  GI_freeT B MT cx fp k acc ly3 S3 W3 ms3 md3.
Proof.
  intros cx fp t k acc ly3 S3 W3 ms3 md3
    (HBD & Hk & Hacc & Hbl & Hn & R20 & R21 & R22 & R23 & R24 & R25 & R27 & HSC & HSL & HWS & HST & HH).
  exists t. exact (conj HBD (conj Hk (conj Hacc (conj Hbl (conj Hn (conj R20 (conj R22 HSL))))))).
Qed.

Lemma GSH_back : gsh_set (gsh_set (gsh_set GSH_turn 98 1 248) 100 1 248) 102 1 248 = GSH_sched.
Proof. vm_compute. reflexivity. Qed.
Lemma GSH_turn_len : length GSH_turn = GE_NSH.
Proof. vm_compute. reflexivity. Qed.
Lemma GSH_sched_len : length GSH_sched = GE_NSH.
Proof. vm_compute. reflexivity. Qed.

Definition G_sh : facts := mkFacts [(22%nat, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0)] [] [].
Definition BxL : sv := SLit SHADOW_OFF.
Definition Bsp0 : Z * Z := (0, 0).

Lemma pw_last : forall {X} (R : X -> X -> Prop) l x y, pairwise R (l ++ [x]) -> In y l -> R y x.
Proof.
  intros X R l. induction l as [|z l IH]; intros x y H Hin; [destruct Hin|].
  cbn [app pairwise] in H. destruct H as [Hf Hp]. destruct Hin as [<- | Hin].
  - apply Forall_app in Hf as [_ Hf2]. inversion Hf2; assumption.
  - exact (IH x y Hp Hin).
Qed.

Lemma table_sep : forall cx ly3 S3 W3 mem3 md3 t b n,
  AR SEGS B ly3 S3 W3 mem3 md3 -> gblk1 B cx ly3 S3 t -> In (b, n) (ablocks B (c_ly cx) (c_S cx)) ->
  b + req_size n <= t \/ t + 460 <= b.
Proof.
  intros cx ly3 S3 W3 mem3 md3 t b n HAR Hbl Hin.
  assert (Hin3 : In (t, 460) (ablocks B ly3 S3)) by (rewrite Hbl; apply in_app_iff; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin3) as (_ & _ & _ & _ & _ & Hpw & _).
  rewrite Hbl, map_app in Hpw. cbn [map] in Hpw.
  pose proof (pw_last _ _ _ _ Hpw (in_map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) _ _ Hin)) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size 460) with 460 in Hd. lia.
Qed.

Lemma table_new : forall cx ly3 S3 W3 mem3 md3 t,
  AR SEGS B ly3 S3 W3 mem3 md3 -> gblk1 B cx ly3 S3 t -> ~ In (t, 460) (ablocks B (c_ly cx) (c_S cx)).
Proof.
  intros cx ly3 S3 W3 mem3 md3 t HAR Hbl Hin.
  pose proof (table_sep cx ly3 S3 W3 mem3 md3 t t 460 HAR Hbl Hin) as Hd. change (req_size 460) with 460 in Hd. lia.
Qed.

(* The image's read-only bytes are kept since the call began. *)
Lemma garo : forall cx fp k ly3 S3 W3 mem3 md3,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 mem3 md3 k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) mem3).
Proof.
  intros cx fp k ly3 S3 W3 mem3 md3 HB HJ a Hro Ho He.
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  rewrite (F3 a); [exact (HRO a Hro Ho He) | | exact Ho | exact He | apply fp_spares_closed; intros (r & Hr & _); destruct Hr].
  destruct Hro as [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr]|].
  exact (pa_relro_img a Hgot).
Qed.

(* The bytes LAY_TX names are the table's bytes but its three padding bytes. *)
Lemma fbyte_iff : forall i, tx_fbyte i = true <-> (0 <= i < 460 /\ i <> 438 /\ i <> 439 /\ i <> 451).
Proof.
  intros i. split.
  - intros H. pose proof (tx_fbyte_range i H) as Hr.
    split; [exact Hr|]. split; [|split]; intros ->; vm_compute in H; discriminate H.
  - intros (Hr & H1 & H2 & H3).
    assert (Hb : forallb (fun n => orb (orb (orb (Nat.eqb n 438) (Nat.eqb n 439)) (Nat.eqb n 451)) (tx_fbyte (Z.of_nat n)))
                   (seq 0 460) = true) by (vm_compute; reflexivity).
    rewrite forallb_forall in Hb.
    specialize (Hb (Z.to_nat i) (proj2 (in_seq 460 0 (Z.to_nat i)) ltac:(lia))).
    rewrite Z2Nat.id in Hb by lia.
    apply orb_prop in Hb as [Hb | Hb]; [|exact Hb]. exfalso.
    repeat (apply orb_prop in Hb as [Hb | Hb]); apply Nat.eqb_eq in Hb; lia.
Qed.

Lemma gtab_obj : forall cx ly3 S3 W3 ms3 t T,
  gtab B cx ly3 S3 W3 ms3 t T -> obj_at SEGS (mrestrict (w_H W3) (ms_mem ms3)) t LAY_TX (tx_vals T).
Proof.
  intros cx ly3 S3 W3 ms3 t T (_ & _ & _ & H4). apply (proj2 (tx_obj_bytes SEGS _ t T)).
  intros i Hi. apply fbyte_iff in Hi as (Hr & H1 & H2 & H3).
  specialize (H4 i Hr H1 H2 H3). unfold aview in H4.
  destruct (mbyte SEGS (mrestrict (w_H W3) (ms_mem ms3)) (t + i)) as [b|]; [|discriminate H4].
  cbn [option_map] in H4. injection H4 as H4. f_equal. apply bv_eq. rewrite H4. reflexivity.
Qed.

Lemma obj_gtab : forall cx ly3 S3 W3 ms3 t T,
  In (t, 460) (ablocks B ly3 S3) -> 0 < t -> length T = 460%nat ->
  obj_at SEGS (mrestrict (w_H W3) (ms_mem ms3)) t LAY_TX (tx_vals T) -> gtab B cx ly3 S3 W3 ms3 t T.
Proof.
  intros cx ly3 S3 W3 ms3 t T Hin Ht HL Hobj. split; [exact Hin|]. split; [exact Ht|]. split; [exact HL|].
  intros i Hr H1 H2 H3.
  pose proof (proj1 (tx_obj_bytes SEGS _ t T) Hobj i (proj2 (fbyte_iff i) (conj Hr (conj H1 (conj H2 H3))))) as Hm.
  unfold aview. rewrite Hm. reflexivity.
Qed.

(* One cell of the frame, as a region of its own. *)
Definition cellr (n : nat) (o : Z) : YP09.region := YP09.mkRegion (Some n) o (o + 1) o (o + 1) [].

Lemma cellr_ok : forall E m n o b, bv_unsigned (ew E n) = b -> 0 <= b + o -> b + o + 1 <= 2 ^ 64 ->
  writable_at SEGS m (b + o) -> region_ok SEGS E m (cellr n o).
Proof.
  intros E m n o b Hb H0 H1 Hw. unfold region_ok, cellr.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hb.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros o' Ho'. replace o' with o by lia. exact Hw.
Qed.

Definition stk128 : YP09.region := YP09.mkRegion (Some 9%nat) 128 136 0 0 [YP09.mkChunk 128 (CVal 8 (SOff 19 32))].
Definition G_A : facts := mkFacts [(19%nat, mkAF 4096 (2 ^ 47) 0); (21%nat, mkAF 4096 (2 ^ 47) 0);
  (22%nat, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0)] [] [].
Definition rs_A : YP09.smem := [stk128; cellr 19 0; cellr 21 0; cellr 19 32; shr 98; shr 100; shr 102].

End d.

(* ---- the segments of the turn, as statements ---- *)
Section e.
Variable POST : ecx -> world SEGS -> config -> Prop.
(* 0x81774 .. 0x815c4 (another turn) or 0x817c8 (the last turn). *)
Definition seg_F_ok : Prop :=
  forall n, ge_from B MT POST (GI_freeT B MT) -> ge_from B MT POST (GSn n) -> ge_from B MT POST (TF (S n)).
(* 0x815c4 .. 0x815f0: the cells marked usable, the call of reac_headamp_tx_next. *)
Definition seg_A_ok : Prop := forall m, ge_from B MT POST (TB m) -> ge_from B MT POST (GSn m).
(* 0x815f0 .. 0x81774 (no record) or 0x81624 (a record: answer, channel and value checks). *)
Definition seg_B_ok : Prop :=
  forall m, ge_from B MT POST (TF m) -> ge_from B MT POST (TC m) -> ge_from B MT POST (TB m).
(* 0x81624 .. 0x8162c: the call of reac_headamp_tx_effective. *)
Definition seg_C_ok : Prop := forall m, ge_from B MT POST (TCr m) -> ge_from B MT POST (TC m).
(* 0x8162c .. 0x816a4 (an unset cell: the call of reac_headamp_default) or 0x816ac (a set cell:
   the value against set_to). *)
Definition seg_Cr_ok : Prop :=
  forall m, ge_from B MT POST (TD m) -> ge_from B MT POST (TE m) -> ge_from B MT POST (TCr m).
(* 0x816a4 .. 0x816ac: the call of reac_headamp_default and the value against it. *)
Definition seg_D_ok : Prop := forall m, ge_from B MT POST (TE m) -> ge_from B MT POST (TD m).
(* 0x816ac .. 0x81774: the scene check and the unset_sent count. *)
Definition seg_E_ok : Prop := forall m, ge_from B MT POST (TF m) -> ge_from B MT POST (TE m).
End e.

End c.
End b.
End a.

(* ---- the tactics the segments share ---- *)
(* The write windows of a run that writes the three shadow bytes only. *)
Ltac awr_sh3 fp E22 EFA HSH :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fpl ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fpl b0 bc ly own) end;
  repeat (first [ apply awr_ok_nil
    | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 22%nat); [reflexivity | exact E22 |
        let a := fresh "a" in let Ha := fresh "Ha" in
        intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; exists GE_CID, fp;
        split; [left; reflexivity|]; right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite EFA, fsb4;
        change (1024 / 8) with 128; rewrite <- HSH; lia | ] ]).

(* A run's write windows are the regions given: an address outside them is kept. *)
Ltac inw_tac E22 :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Ha := fresh "Ha" in
  intros (r & Hr & Ha);
  lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
  repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?E22 in Ha | ]);
  try destruct Hr.

(* The write windows of a run that writes frame cells and shadow bytes of the own frame. *)
Ltac awr_fr fp EFA HSH :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fpl ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fpl b0 bc ly own) end;
  repeat (first [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn; lia|]
    | eapply awr_ok_cons_gen; [reflexivity | eassumption |
        let a := fresh "a" in let Ha := fresh "Ha" in
        intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; exists GE_CID, fp;
        split; [left; reflexivity|];
        first [ left; unfold in_zr; cbn [fst snd]; rewrite EFA, fsb4; lia
              | right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite EFA, fsb4; change (1024 / 8) with 128;
                rewrite <- HSH; lia ] | ] ]).

