(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryRawMalloc), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACjo.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntryRawMalloc.v, with its module paths changed; 105 of its 137 lines of code are new or changed and 228 lines of the source are left out. *)
(* Ported from lib/A/Prog/GrantEntryRawLib.v of a working branch 7c8c67da870 (blob 8178472223b). *)
(* Facts every segment of the hand-built allocation phase uses after a call or a run: rcore
   and gtab (LLVMFEntryRawDefs.v) hold at a new pc and state when the bytes they read and the
   registers they name are unchanged; and a call that owns no byte of the caller keeps every
   byte they read (call_keep). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05 YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaRun PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC88.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantPa GrantPaLib YC1g YC1h YC85 GrantFrame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
LLVMFEntryDefs LLVMFEntrySetDefs LLVMFEntryRawDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require
GrantSlotPlan SlotNeeds_c SegSetModel.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation BASE := (pa_val A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.

(* The bytes the facts of rcore and gtab read: the spill slots and the saved words from s1
   up, the caller's input, the frame on the side stack for frames, its shadow and the
   table. *)
Definition rm_at (cx : ecx) (fp t a : Z) : Prop :=
  c_sp1 cx <= a < 2 ^ 64 \/ c_p cx <= a < c_p cx + c_n cx \/
  gF cx fp <= a < gF cx fp + 1024 \/ gSH cx fp <= a < gSH cx fp + 128 \/ t <= a < t + 460.

(* rcore at a new pc, from a state that keeps those bytes and the registers rcore reads. *)
Lemma rm_rcore : forall cx fp pc pc' t W ms W' ms',
  rcore cx fp pc t W ms ->
  spZ (c_regs cx) <= 2 ^ 47 -> c_sp1 cx <= spZ (c_regs cx) - 288 ->
  (forall a, rm_at cx fp t a -> aview SEGS (w_H W') (ms_mem ms') a = aview SEGS (w_H W) (ms_mem ms) a) ->
  ms_pc_val ms' = w64 (BASE + pc') -> ms_resv ms' = None -> ms_svc_pending ms' = None ->
  ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  getr (ms_regs ms') 2 = getr (ms_regs ms) 2 -> getr (ms_regs ms') 3 = getr (ms_regs ms) 3 ->
  getr (ms_regs ms') 4 = getr (ms_regs ms) 4 -> getr (ms_regs ms') 8 = getr (ms_regs ms) 8 ->
  getr (ms_regs ms') 9 = getr (ms_regs ms) 9 -> getr (ms_regs ms') 19 = getr (ms_regs ms) 19 ->
  getr (ms_regs ms') 21 = getr (ms_regs ms) 21 -> getr (ms_regs ms') 22 = getr (ms_regs ms) 22 ->
  getr (ms_regs ms') 23 = getr (ms_regs ms) 23 ->
  rcore cx fp pc' t W' ms'.
Proof.
intros cx fp pc pc' t W ms W' ms'
  ((_ & _ & _ & _ & _ & _ & (G2 & G8 & G9 & G3 & G4) & (HRA & HSJ) & HSH & HFL & HLEN & HIN)
   & Hn & R19 & R21 & R22 & R23 & S48 & SL & B0 & B1 & AW & AS & HREL & HI1)
  Hsp47 Hsp1 HK Hpc Hrv Hsv Hro Hfr Hfc Q2 Q3 Q4 Q8 Q9 Q19 Q21 Q22 Q23.
assert (RD : forall a v, (forall j, 0 <= j < 8 -> rm_at cx fp t (a + j)) ->
  rdword (aview SEGS (w_H W) (ms_mem ms)) a = Some v -> rdword (aview SEGS (w_H W') (ms_mem ms')) a = Some v).
{ intros a v Ha Hr.
  rewrite (rdword_tr (aview SEGS (w_H W) (ms_mem ms)) (aview SEGS (w_H W') (ms_mem ms')) a); [exact Hr|].
  intros j Hj. exact (HK (a + j) (Ha j Hj)). }
assert (SLOT : forall off v, 0 <= off <= 184 -> gslot cx W ms off v -> gslot cx W' ms' off v).
{ intros off v Hoff Hs. unfold gslot in *. apply RD; [|exact Hs]. intros j Hj. left. lia. }
assert (FB : forall off v, 0 <= off < 1024 -> gfb cx fp W ms off v -> gfb cx fp W' ms' off v).
{ intros off v Hoff Hb. unfold gfb in *. rewrite HK; [exact Hb|]. right; right; left. lia. }
assert (FA : forall off (l : list byte), 0 <= off -> off + Z.of_nat (length l) <= 1024 ->
  gfarr cx fp W ms off l -> gfarr cx fp W' ms' off l).
{ intros off l H0 H1 Ha. unfold gfarr in *.
  apply (garr8_aview_kept SEGS (w_H W) (w_H W') (ms_mem ms) (ms_mem ms')); [|exact Ha].
  intros a Ha'. rewrite length_map in Ha'. apply HK. right; right; left. lia. }
pose proof (SegSetModel.tables_end_inv (c_pl cx)) as (_ & LW & LS & _ & _).
destruct SL as (L8 & L40 & L64 & L72 & L96 & L112 & L128 & L136 & L144 & L152).
unfold rcore, ge_body, gregs, gsaved, rslots.
splits.
all: first
  [ exact Hpc | exact Hrv | exact Hsv | exact Hro | exact Hfr | exact Hfc
  | exact HLEN | exact Hn | exact HREL | exact HI1
  | (rewrite Q2; exact G2) | (rewrite Q8; exact G8) | (rewrite Q9; exact G9)
  | (rewrite Q3; exact G3) | (rewrite Q4; exact G4)
  | (rewrite Q19; exact R19) | (rewrite Q21; exact R21) | (rewrite Q22; exact R22)
  | (rewrite Q23; exact R23)
  | (apply RD; [intros j Hj; left; lia | exact HRA])
  | (intros jj Hjj; apply RD; [intros j Hj; left; lia | exact (HSJ jj Hjj)])
  | (apply RD; [intros j Hj; right; right; left; lia | exact HFL])
  | (intros i Hi; rewrite HK; [exact (HSH i Hi) | right; right; right; left; rewrite HLEN in Hi; unfold GE_NSH in Hi; lia])
  | (apply (garr8_aview_kept SEGS (w_H W) (w_H W') (ms_mem ms) (ms_mem ms')); [|exact HIN];
     intros a Ha; rewrite length_map in Ha; apply HK; right; left; unfold c_n; lia)
  | (apply SLOT; [lia | assumption])
  | (apply FB; [unfold GO_RAW; lia | assumption])
  | (apply FA; [unfold GO_WAS, GO_SET; lia | rewrite ?LW, ?LS; unfold GO_WAS, GO_SET; lia | assumption])
  | (match goal with |- ?g => idtac "RM-RCORE-LEFT" g end; fail) ].
Qed.

(* gtab at a new state, from one that keeps the table's bytes and still holds its block. *)
Lemma rm_gtab : forall cx ly S ly' S' W ms W' ms' t T,
  gtab B cx ly S W ms t T -> In (t, 460) (ablocks B ly' S') ->
  (forall a, t <= a < t + 460 -> aview SEGS (w_H W') (ms_mem ms') a = aview SEGS (w_H W) (ms_mem ms) a) ->
  gtab B cx ly' S' W' ms' t T.
Proof.
intros cx ly S ly' S' W ms W' ms' t T (_ & Ht & Hl & Hb) Hin HK.
split; [exact Hin|]. split; [exact Ht|]. split; [exact Hl|].
intros i Hi H1 H2 H3. rewrite HK by lia. exact (Hb i Hi H1 H2 H3).
Qed.

(* A call made from s1 whose callee owns no byte of the caller (FP has no address) and keeps
   the blocks keeps every byte of rm_at. *)
Lemma call_keep : forall cx fp t ly3 S3 W3 memc mdc STK FP ly2 S2 W2 mem2 md2 k1,
  ge_base B MT cx -> frames S3 = [(GE_CID, fp)] ->
  frame_addr ly3 GE_CID fp = gF cx fp -> gSH cx fp = SHADOW_OFF + gF cx fp / 8 ->
  alloc_ceiling <= c_sp1 cx ->
  (forall p n, In (p, n) (ablocks B (c_ly cx) (c_S cx)) -> In (p, n) (ablocks B ly3 S3)) ->
  In (t, 460) (ablocks B ly3 S3) -> ablocks B ly2 S2 = ablocks B ly3 S3 ->
  (forall a, ~ inFP FP a) ->
  ajournal SEGS B STK (c_sp1 cx) FP ly3 S3 W3 memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
  forall a, rm_at cx fp t a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) memc a.
Proof.
  intros cx fp t ly3 S3 W3 memc mdc STK FP ly2 S2 W2 mem2 md2 k1 HB HFR EFA HSH Hceil Hbl Hint Hab HnFP HJ1 a Ha.
  pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & _ & F4 & _).
  destruct HB as (_ & _ & _ & Hpn & _).
  assert (Hfb : fs_frame_bytes GE_CID = 1024) by (vm_compute; reflexivity).
  assert (Hsa : shadow_addr (gF cx fp) = gSH cx fp) by (unfold shadow_addr; rewrite HSH; reflexivity).
  assert (Hfin : In (GE_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
  - apply F1; lia.
  - destruct Hpn as [[Hn0 _] | [Hn Hin]]; [lia|].
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hq].
    replace a with (c_p cx + (a - c_p cx)) by lia.
    apply (F2 (c_p cx) (c_n cx) (a - c_p cx) (Hbl _ _ Hin)); [rewrite Hab; exact (Hbl _ _ Hin) | lia | apply HnFP].
  - apply (F4 GE_CID fp a Hfin); [|apply HnFP].
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA, Hfb. lia.
  - apply (F4 GE_CID fp a Hfin); [|apply HnFP].
    right. unfold in_zr. cbn [fst snd]. rewrite EFA, Hsa, Hfb. change (1024 / 8) with 128. lia.
  - replace a with (t + (a - t)) by lia.
    apply (F2 t 460 (a - t) Hint); [rewrite Hab; exact Hint | change (req_size 460) with 460; lia | apply HnFP].
Qed.

End c.
End b.
End a.
