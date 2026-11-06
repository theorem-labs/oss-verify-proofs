(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMrecL.v (commit 67fc7ef5787, lane B1 drain composition, DoRecycle chain; the chain's two function pairs, Quarantine::DoRecycle and LocalCache::Deallocate, re-checked EQUAL-mod-pcrel by cmpkit 4bbd3a74be89 strictcmp2 16982e3ef42b; file sha256 f734f80ccc69) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 5 image addresses moved by code-verified function pairs (5 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 4 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (lane B1 of ReallocPrimary's Theorem Labs lane walk lanes, slice H2, a Theorem Labs lane; interface
   DMwalkIF.v at a working branch 3e29c198d40): the STATES of Quarantine::DoRecycle (0x33cf8) over the OPAQUE cut
   relation [ARXr] and recycle invariant [DRq] of DMwalkIF.v section 3, for [dorecycle_spec_r].
   They are cgif's released states (YFhd.v, restated with the raw frame and the DIface window in DGif1da.v, errno in
   DGif1daE.v, memnorm in DGif1daM.v) with three changes:
   - the cut relation is [ARXr (as_inst B)] and the owned set [AOX], not cgif's AR / aowned;
   - the recycle invariant is [DRq] in its folded form (the chunks and the batch objects still to recycle), not cgif's
     RIx, and the batch lengths are carried separately with NO lower bound: MergeBatches extracts EMPTY batches, so a
     batch of count 0 reaches DoRecycle (the arm walked in DMrecZ.v);
   - errno and memnorm are kept in the accumulated frame itself (DGif1daE / DGif1daM carry them beside it), because
     dr_leaf_r states both.
   The relation-free pieces (registers, frame and temp-list cells, header addresses) are YFhd's.
   rule 24: proves function __sanitizer::Quarantine<__asan::QuarantineCallback, __asan::AsanChunk>::DoRecycle (states;
   lane B1 reuse search LOOKUP-B1-drain.txt (sha256 c6e48b676fd5; internal record), B1LookupCheck CONFIRM). *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane): the image-B (asan-ubsan) twin of lib/A/DMrecL.v at a working branch 14a6b2561a69, relocated by a Theorem Labs lane's alreloc a5c53bb2bed4ad03 (every moved numeral a DoRecycle / LocalCache::Deallocate pc, +0x58) with the A twins A<r> renamed to the B twins Y<r>; the comment blocks above keep the A file's text and its A pcs. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YP09 YN3v YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YF0m YF0x YFl1 YFeq YFeu YFf2 YFh9 YFhd.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseDG AGif2reply DGif0reply DIfaceR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import DMspec DMiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require DMwalkIF ErrnoG MemnormT.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable B : asyms.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Variables (ly : alayout) (X0 : astate) (W0 : world tfibsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Local Notation sp0 := (YFhd.sp0 regs0).
Local Notation sp1 := (YFhd.sp1 regs0).
Local Notation DRSTACK_X := DMwalkIF.DRSTACK_X.
(* DoRecycle's own stack window and the temp list's header it writes *)
Definition SYr (a : Z) : Prop := sp0 - DRSTACK_X <= a < sp0 + 32.
(* The accumulated frame from DoRecycle's entry to a cut: the released DGif1da.acc over ARXr / AOX, with errno and
   memnorm kept. *)
Record accr (X : astate) (W : world tfibsegs) (mem : word -> option byte) (md : Model) : Prop := {
ar_AR : ARXr (as_inst B) ly X W mem md;
ar_wle : wle W0 W;
ar_io : same_io md0 md;
ar_own : forall a, AOX ly X a -> AOX ly X0 a;
ar_frame : forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly X0 a -> ~ AOX ly X a -> ~ ascratch B DRSTACK_X regs0 a -> ~ (sp0 <= a < sp0 + 32) ->
  aview tfibsegs (w_H W) mem a = aview tfibsegs (w_H W0) mem0 a;
ar_pres : forall a, SYr a -> apresent (w_H W) mem a;
ar_inited : st_cache_inited X = true;
ar_raw : forall x : word, ~ AOX ly X0 (bv_unsigned x) -> ~ AOX ly X (bv_unsigned x) -> ~ ascratch B DRSTACK_X regs0 (bv_unsigned x) ->
  ~ (sp0 <= bv_unsigned x < sp0 + 32) -> mem x = mem0 x;
ar_ek : ErrnoG.errno_kept B mem0 mem;
ar_mk : MemnormT.memnorm_keep tfibsegs mem0 mem
}.
Local Notation common_regs := (YFhd.common_regs regs0).
Local Notation loop_regs := (YFhd.loop_regs regs0).
Local Notation frame_cells := (YFhd.frame_cells ly regs0).
Local Notation tmp_cells := (YFhd.tmp_cells ly regs0).
Local Notation batch_regs := (YFhd.batch_regs ly).
Local Notation zlen := (@YFhd.zlen _).
Local Notation hdra := (YFhd.hdra B ly).
(* the slot bound of every batch still to recycle; NO lower bound (count 0 is allowed) *)
Definition blen_ok (P : list batch) : Prop := Forall (fun b => (length (b_items b) <= Z.to_nat kBatchSlots)%nat) P.
(* the outer loop head 0x33dc8 *)
Record ostr (X : astate) (rest : list batch) (lz qb : Z) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop := {
o_acc : accr X W mem md;
o_drq : DRq X (flat_map b_items rest) (map b_self rest);
o_bl : blen_ok rest;
o_ne : rest <> [];
o_len : zlen rest < 2 ^ 40;
o_cregs : common_regs regs;
o_lregs : loop_regs regs;
o_a0 : getr regs 10 = w64 (zlen rest);
o_frame : frame_cells W mem;
o_tmp : tmp_cells W mem rest lz qb;
o_cells : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (batch_cells rest)
}.
(* the item loop's call of QuarantineCallback::Recycle (A_RChunk) *)
Record rcstr (X : astate) (b : batch) (t : list batch) (its : list chunk) (i : nat) (lz qb : Z)
(W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop := {
rc_acc : accr X W mem md;
rc_drq : DRq X (its ++ flat_map b_items t) (b_self b :: map b_self t);
rc_bl : blen_ok t;
rc_items : exists done, b_items b = done ++ its /\ length done = i;
rc_ne : its <> [];
rc_blen : (1 <= length (b_items b) <= Z.to_nat kBatchSlots)%nat;
rc_len : zlen t < 2 ^ 40;
rc_cregs : common_regs regs;
rc_lregs : loop_regs regs;
rc_bregs : batch_regs regs b;
rc_ra : getr regs 1 = w64 0x33e14;
rc_a0 : getr regs 10 = w64 (sp1 + 8);
rc_a1 : forall k ks, its = k :: ks -> getr regs 11 = w64 (hdra k);
rc_s7 : getr regs 23 = w64 (ly_space ly + b_self b + 152 + 8 * Z.of_nat i);
rc_s9 : getr regs 25 = w64 (16 + Z.of_nat i);
rc_frame : frame_cells W mem;
rc_tmp : tmp_cells W mem t lz qb;
rc_cells : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (batch_cells (b :: t))
}.
(* the item loop's return point 0x33e14 *)
Record rstr (X : astate) (b : batch) (t : list batch) (its : list chunk) (i : nat) (lz qb : Z)
(W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop := {
r_acc : accr X W mem md;
r_drq : DRq X (its ++ flat_map b_items t) (b_self b :: map b_self t);
r_bl : blen_ok t;
r_items : exists done, b_items b = done ++ its /\ length done = i;
r_i : (1 <= i)%nat;
r_blen : (1 <= length (b_items b) <= Z.to_nat kBatchSlots)%nat;
r_len : zlen t < 2 ^ 40;
r_cregs : common_regs regs;
r_lregs : loop_regs regs;
r_bregs : batch_regs regs b;
r_s7 : getr regs 23 = w64 (ly_space ly + b_self b + 144 + 8 * Z.of_nat i);
r_s9 : getr regs 25 = w64 (15 + Z.of_nat i);
r_frame : frame_cells W mem;
r_tmp : tmp_cells W mem t lz qb;
r_cells : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (batch_cells (b :: t))
}.
(* the call of CacheDealloc for the batch object (A_CDealloc), from the item loop's end or the count-0 arm *)
Record cdstr (X : astate) (b : batch) (t : list batch) (lz qb : Z)
(W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop := {
cd_acc : accr X W mem md;
cd_drq : DRq X (flat_map b_items t) (b_self b :: map b_self t);
cd_bl : blen_ok t;
cd_len : zlen t < 2 ^ 40;
cd_cregs : common_regs regs;
cd_lregs : loop_regs regs;
cd_ra : getr regs 1 = w64 0x33e4c;
cd_a0 : getr regs 10 = w64 (ly_T ly + t_cache);
cd_a1 : getr regs 11 = w64 A_ALLOCATOR;
cd_a2 : getr regs 12 = w64 kBatchClass;
cd_a3 : getr regs 13 = w64 (ly_space ly + b_self b);
cd_frame : frame_cells W mem;
cd_tmp : tmp_cells W mem t lz qb;
cd_cells : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (batch_cells t)
}.
(* CacheDealloc's return point 0x33e4c *)
Record qstr (X : astate) (t : list batch) (lz qb : Z)
(W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop := {
q_acc : accr X W mem md;
q_drq : DRq X (flat_map b_items t) (map b_self t);
q_bl : blen_ok t;
q_len : zlen t < 2 ^ 40;
q_cregs : common_regs regs;
q_lregs : loop_regs regs;
q_frame : frame_cells W mem;
q_tmp : tmp_cells W mem t lz qb;
q_cells : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (batch_cells t)
}.
Definition OSTr (X : astate) (rest : list batch) (W : world tfibsegs) (c : config) : Prop :=
exists lz qb regs mem md, c = cfg_at tfibsegs 0x33dc8 regs mem md /\ ostr X rest lz qb W regs mem md.
Definition RCSTr (X : astate) (b : batch) (t : list batch) (its : list chunk) (i : nat) (W : world tfibsegs) (c : config) : Prop :=
exists lz qb regs mem md, c = cfg_at tfibsegs A_RChunk regs mem md /\ rcstr X b t its i lz qb W regs mem md.
Definition RSTr (X : astate) (b : batch) (t : list batch) (its : list chunk) (i : nat) (W : world tfibsegs) (c : config) : Prop :=
exists lz qb regs mem md, c = cfg_at tfibsegs 0x33e14 regs mem md /\ rstr X b t its i lz qb W regs mem md.
Definition CDSTr (X : astate) (b : batch) (t : list batch) (W : world tfibsegs) (c : config) : Prop :=
exists lz qb regs mem md, c = cfg_at tfibsegs A_CDealloc regs mem md /\ cdstr X b t lz qb W regs mem md.
Definition QSTr (X : astate) (t : list batch) (W : world tfibsegs) (c : config) : Prop :=
exists lz qb regs mem md, c = cfg_at tfibsegs 0x33e4c regs mem md /\ qstr X t lz qb W regs mem md.
End e.

Lemma blen_ok_cons : forall b P, blen_ok (b :: P) <-> (length (b_items b) <= Z.to_nat kBatchSlots)%nat /\ blen_ok P.
Proof. intros b P. unfold blen_ok. rewrite Forall_cons_iff. tauto. Qed.
End d.
