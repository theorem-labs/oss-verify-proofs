(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMwalkIF.v (commit aa7efba8a4e3, Quarantine::Drain walk set; file sha256 dcd705c22ea1) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 7 image addresses moved by code-verified function pairs (4 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 3 code pcs the tool read as sizes, by funcpair.py), and 42 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (lane B1 of ReallocPrimary's Theorem Labs lane walk lanes, brief B-WALK-LANES.md (sha256 68c13c734927; internal record) of the lane's
   frame directory, section 'Lane B1'): the INTERFACE of the real-merge drain walk at
   cgif_file_fuzzer's asan-ubsan image - the statement head of every slice, so the slices can be written in
   parallel against a fixed text.  This file states; it proves nothing about the machine.
   rule 24: no function proved here (kind: statement heads; the lane's reuse search is LOOKUP-B1-drain.txt (sha256 c6e48b676fd5; internal record),
   `proof-index MergeBatches Recycle QuarantineCallback_Recycle Drain` 2026-10-29T23:07:48Z exit 0, rule-24
   check B1LookupCheck CONFIRM).

   The four slices and their heads:
   - H1 [mb_ok_t], [mb_model_facts]: QuarantineCache::MergeBatches (0x33b74 .. the return to 0x33a38) against the
     shared model's merge_batches_cf (YG00cf.v:287-301), over the cell vocabulary of section 1 below.
   - H2 [dorecycle_spec_r]: Quarantine::DoRecycle (0x33cf8) over the OPAQUE cut relation [ARXr] and recycle
     invariant [DRq], with the COUNT-0 batch arm (0x33d9c / 0x33da0) and fuel [length P].
   - H3 [cdealloc_m_t_cgif]: SizeClassAllocator64LocalCache::Deallocate (0x34234) over [ARXr] / [DRq], in
     MnRecycle.de_cdealloc_m_t's form (raw frame + errno + memnorm), from the read fields [cd_reads].
   - H4 [rchunk_m_t_cgif]: __asan::QuarantineCallback::Recycle (0x33e30) over [ARXr] / [DRq], in
     MnRecycle.de_rchunk_m_t's form, from the read fields [rc_reads] and H3's contract.
   - mine, the DMdrain files [drain_m_cf_t]: Quarantine::Drain (0x337ec) with the real merge, MnDrain.de_drain_m_t at
     [drain_body_cf], from the DIface read fields, H1, H2 and H3 / H4's contracts.

   Every head is stated at the cgif image (segments tfibsegs; the AImg / DImg instances AGif2cgif.AImg_cgif and
   DGif0cgif.DImg_cgif), over an opaque allocator relation, so the layer instantiates it for preset and for
   fuzz_reply.  No head mentions ARX_cf, ARcf or any 2 ^ 28 literal (Main's rule of 23:3xZ): a size bound is a
   Section Variable with its premise where a slice needs one.

   Facts a slice may cite (file:line), beside the Stdlib and the LPS semantics:
   - the model: YG00.v (batch, b_bytes :149, sum_bytes YG01.v:316, all_batches YG01.v:260, pop_batches :518,
     do_recycle :510, recycle_chunk :495, cache_dealloc), YG00cf.v (merge_batches_cf :283-297, maybe_drain_cf),
     DMspec.v (merge_split_cf :50, recycle_body_cf :56, drain_body_cf :61, acall_post_x :102);
   - the cells: YG0n.v (batch_cells :77, qc_cells :89, quar_cells :95), YG0f.v (cell_holds :262);
   - the segments of the merge walk: DMsegD.v (at_MB :49, merge_test :71, postDm :72), DMseg_mbe.v (segE :178,
     at_MBH :119), DMseg_mbh.v (segH :274, at_ADV :153, at_EXH :160, at_TOCOPY :165, at_TOTAIL :174, postH :182),
     DMseg_mbc.v (segC :192, postC :131), DMseg_mbt.v (segT :398, at_TCONT :222, at_TEXIT :231, postT :237),
     DMseg_rj.v (segR :197, at_RJL :129, at_RJX :138, postR :145);
   - the dequeue loop after the merge: DMdeq.v (deq_pre :675, tfib_deq_ok :707, ATDR :193);
   - the released DoRecycle walk and its DIface restatement: YFhd / YFhg / YFhl / YFhf / YFhi / YFhk / YFh9 / YFha /
     YFhb / YFhc, DGif1da.v / DGif1db.v / DGif1dc.v / DGif1daE.v / DGif1daM.v;
   - the released recycle callees: YFg0 / YFfi / YFez / YFgk / YFgy / YFgz (CacheDealloc), YFfs / YFg7 / YFgs /
     YFfr / YFh7 / YFf3 / YFg8 / YFg9 / YFgv / YFf4 (Recycle), FGt.v / FGc.v / FGk.v / FGs.v / FGw.v
     (EnsureFreeArraySpace, allocator-relation free), and their DIface restatements DGif1dr.v / DGif1drM.v /
     DGif1drMr.v / DGif1dIE.v;
   - the interface types: DMiface.v (qview :74, dmem_q :117, rcc_pre_x :135, cd_pre_x :147, KSTACK_CF :132, the
     di_*_t types :174-254), DIfaceR.v (acall_raw_x :50), ErrnoG.v (errno_kept :63), MemnormT (memnorm_keep),
     MnDrain.v (de_drain_m_t :48), MnRecycle.v (de_rchunk_m_t :47, de_cdealloc_m_t :61).
   A slice that needs a fact from a file not in this list asks ReallocPrimary before it states a new premise. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1w AFeq AFew AFeu AFgj.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require DMsegD.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseDG AGif2reply DGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import DMspec DMiface DIfaceR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ErrnoG MemnormT MnDrain MnRecycle.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. The cell vocabulary of the merge walk (H1).                                                                   *)
(* A batch object sits at [ly_space ly + b_self b]; its cell words are next, byte count, item count and the live
   slots, as YG0n.batch_cells (:77-86) states them with the slot word of an item [k] abstracted to [iw k] (at the
   instance, iw k = aeval B ly (sptr_exp (ck_hdr k))). *)
Definition addrb (ly : alayout) (b : batch) : Z := ly_space ly + b_self b.
Definition zl {A : Type} (l : list A) : Z := Z.of_nat (length l).
(* the address the previous batch's next word holds: the first batch of [l], else [z] *)
Definition fa (ly : alayout) (l : list batch) (z : Z) : Z := match l with [] => z | b :: _ => addrb ly b end.
Definition la (ly : alayout) (l : list batch) : Z := match rev l with [] => 0 | b :: _ => addrb ly b end.
Definition bcell (ly : alayout) (iw : chunk -> Z) (m : word -> option byte) (b : batch) (nxt : Z) : Prop :=
val_mem tfibsegs m (addrb ly b) 8 nxt /\ val_mem tfibsegs m (addrb ly b + 8) 8 (b_bytes b) /\
val_mem tfibsegs m (addrb ly b + 16) 8 (zl (b_items b)) /\
(forall j k, nth_error (b_items b) j = Some k -> val_mem tfibsegs m (addrb ly b + 24 + 8 * Z.of_nat j) 8 (iw k)).
(* a linked list of batches whose last next word is [z] *)
Fixpoint lcn (ly : alayout) (iw : chunk -> Z) (m : word -> option byte) (l : list batch) (z : Z) : Prop :=
match l with [] => True | b :: t => bcell ly iw m b (fa ly t z) /\ lcn ly iw m t z end.
(* the cell words of one batch (what the walk may write in it): next, size, count, the live slots *)
Definition bcells_of (ly : alayout) (b : batch) (a : Z) : Prop :=
addrb ly b <= a < addrb ly b + 24 + 8 * zl (b_items b).
(* the whole batch object *)
Definition bobj_of (ly : alayout) (b : batch) (a : Z) : Prop := addrb ly b <= a < addrb ly b + kBatchBytes.

(* The merge of the model, with exact fuel (DMmerge.v:51 states the same definition). *)
Definition MB (l : list batch) : list batch * list batch := merge_batches_cf (length l) l.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. H1: MergeBatches (0x33b74), from Recycle's call to its return at 0x33a38.                                     *)
Section mb.
Variable W : world tfibsegs.
Variable ly : alayout.
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variable mat0 : list word.
(* the slot word of an item, and the global list at the call *)
Variable iw : chunk -> Z.
Variable L0 : list batch.
(* Recycle's sp: the temp (to-deallocate) list's header is at [spr .. spr + 32); MergeBatches' own frame is
   [spr - 16, spr) (DMseg_mbe.v:51 R_STK, DMseg_mbt.v:93-96 R_STK at the tail's sp = spr - 16). *)
Let spr : Z := bv_unsigned (getr regs0 2).
Let m0 : word -> option byte := mrestrict (w_H W) mem0.
Let cfgMB : config :=
mkCfg (mkst regs0 (w64 0x33b74) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).

(* The call's registers are DMsegD.at_MB's (DMsegD.v:49-69) with Drain's a3 and T + t_cache kept in s3 / s4;
   the walk reads s0 / s1 / s2 only to return them (DMseg_mbh.SREGSX). *)
Record mb_pre : Prop := MbPre {
mb_LY : layout_ok ly;
mb_sp : kHighMemBeg + 16 <= spr /\ spr + 32 <= kHighMemEnd;
mb_sp_al : spr mod 16 = 0;
mb_ra : getr regs0 1 = w64 0x33a38;
mb_a0 : getr regs0 10 = w64 (A_QUAR + 160);
mb_a1 : getr regs0 11 = w64 spr;
mb_s0 : getr regs0 8 = w64 (A_QUAR + 160);
mb_s1 : getr regs0 9 = w64 kQuarantineMin;
mb_s2 : getr regs0 18 = w64 A_QUAR;
(* MergeBatches is entered only on the merge arm.  merge_test alone (DMsegD.v:71, the machine's 0x33a00 / 0x33a14)
   does NOT give this: with |L0| = 1 any 8192 < bytes < 16384 passes it, and the walk would leave through
   0x33b88 -> 0x33ca8, which no shell covers.  DMsegD.postDm (:73-74) reaches at_MB only when
   kQuarantineMax < bytes, and kQuarantineMax = 2 ^ 28 (YG00.v:27) with bytes < 2 * kBatchBytes * |L0| forces
   |L0| > 16384.  DMdrain discharges mb_len from those two and the count word. *)
mb_len : (2 <= length L0)%nat;
(* every batch: a kBatchBytes object of the primary space, 8192-aligned, apart from Recycle's frame window, with
   1 .. kBatchSlots items of non-negative user size *)
mb_bfacts : forall b, In b L0 ->
  kHighMemBeg <= addrb ly b /\ addrb ly b + kBatchBytes <= ASAN_CEIL /\ addrb ly b mod 8192 = 0 /\
  (1 <= length (b_items b) <= Z.to_nat kBatchSlots)%nat /\
  (addrb ly b + kBatchBytes <= spr - 16 \/ spr + 32 <= addrb ly b);
(* List.NoDup, the Stdlib one: DMdeq.dq_ND (DMdeq.v:679), the consumer, is List.NoDup, while the ambient NoDup
   is stdpp's (DMiface.qview's qv_nodup, DMiface.v:96, is stdpp's; DMdrainQ.nodup_of_stdpp bridges the two) *)
mb_nodup : List.NoDup (map b_self L0);
mb_nn : forall k, In k (flat_map b_items L0) -> 0 <= ck_n k;
mb_iw : forall k, In k (flat_map b_items L0) -> 0 <= iw k < 2 ^ 64;
(* the byte bound the walk's arithmetic uses: DMiface.qview's qv_bytes (DMiface.v:105), not a size literal *)
mb_bytes : sum_bytes L0 <= 2 ^ 31;
(* the global list's header (count, first, last, bytes) at inst + o_quar + 160 .. 192 *)
mb_hdr : val_mem tfibsegs m0 (A_QUAR + 160) 8 (zl L0) /\ val_mem tfibsegs m0 (A_QUAR + 168) 8 (fa ly L0 0) /\
  val_mem tfibsegs m0 (A_QUAR + 176) 8 (la ly L0) /\ val_mem tfibsegs m0 (A_QUAR + 184) 8 (sum_bytes L0);
(* the temp list's header, zeroed by Recycle's prologue (DMsegD.at_MB, DMsegD.v:66) *)
mb_tmp : val_mem tfibsegs m0 spr 8 0 /\ val_mem tfibsegs m0 (spr + 8) 8 0 /\
  val_mem tfibsegs m0 (spr + 16) 8 0 /\ val_mem tfibsegs m0 (spr + 24) 8 0;
(* the two lock bytes Recycle holds and the two bytes after them (DMsegD.at_MB, DMsegD.v:61: the word at
   inst + o_quar + 152 is 257).  MergeBatches never writes them - they are outside mbwin - and the segment at
   0x33a38 seeds from them (DMseg_rj.SS0's R_QW, DMseg_rj.v:58-60), so the post carries the value. *)
mb_mutex : val_mem tfibsegs m0 (A_QUAR + 152) 4 257;
(* the list's cells, linked, last next word 0 *)
mb_cells : lcn ly iw m0 L0 0;
(* presence: Recycle's frame window and every batch object *)
mb_pres : forall a, spr - 16 <= a < spr + 32 -> apresent (w_H W) mem0 a;
mb_bpres : forall b a, In b L0 -> bobj_of ly b a -> apresent (w_H W) mem0 a
}.
(* H1 builds DMseg_mbe.SS0's seed (st_ok at 0x33b74) from these facts, as DMdeq.SEED1_ok (DMdeq.v:373) builds
   YFgl's from its cells; no seed is assumed here. *)

(* The callee-saved registers and gp / tp MergeBatches returns unchanged (DMseg_mbh.SREGSX, DMseg_mbt.SREGSX). *)
Definition SREGSX : list (bv 5) := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* What MergeBatches may have written: Recycle's frame window (its own frame and the temp list's header), the
   global list's header, and the CELL words (not the whole objects) of the entry list, of the kept list and of the
   extracted list.  This is DMiface.dwin_q's shape (DMiface.v:114-115), so the drain's cut memory relation
   [dmem_q] follows from it. *)
Definition mbwin (Lk ex : list batch) (a : Z) : Prop :=
(spr - 16 <= a < spr + 32) \/ (A_QUAR + 160 <= a < A_QUAR + 192) \/
(exists b, In b (L0 ++ Lk ++ ex) /\ bcells_of ly b a).

(* The return at 0x33a38: the kept list [Lk] is the global list, the extracted (emptied) batches [ex] are the temp
   list at Recycle's sp, and the global byte word has lost kBatchBytes per extracted batch - merge_split_cf's
   (gm, ex) exactly (DMspec.v:51-56). *)
Definition mb_post (W' : world tfibsegs) (c' : config) : Prop :=
let Lk := fst (MB L0) in let ex := snd (MB L0) in
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 0x33a38) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs' 2 = w64 spr /\
getr regs' 1 = w64 0x33a38 /\
(forall r : bv 5, In r SREGSX -> getr regs' r = getr regs0 r) /\
(forall x : word, ~ mbwin Lk ex (bv_unsigned x) -> mem' x = mem0 x) /\
(forall a, mbwin Lk ex a -> kHighMemBeg <= a -> apresent (w_H W) mem' a) /\
(let m := mrestrict (w_H W) mem' in
 val_mem tfibsegs m (A_QUAR + 160) 8 (zl Lk) /\ val_mem tfibsegs m (A_QUAR + 168) 8 (fa ly Lk 0) /\
 val_mem tfibsegs m (A_QUAR + 176) 8 (la ly Lk) /\
 val_mem tfibsegs m (A_QUAR + 184) 8 (sum_bytes L0 - kBatchBytes * zl ex) /\
 val_mem tfibsegs m spr 8 (zl ex) /\ val_mem tfibsegs m (spr + 8) 8 (fa ly ex 0) /\
 val_mem tfibsegs m (spr + 16) 8 (la ly ex) /\ val_mem tfibsegs m (spr + 24) 8 (kBatchBytes * zl ex) /\
 val_mem tfibsegs m (A_QUAR + 152) 4 257 /\
 lcn ly iw m Lk 0 /\ lcn ly iw m ex 0).

(* H1's machine head. *)
Definition mb_ok_t : Prop := mb_pre -> SRr tfibsegs W cfgMB mb_post.

(* The loop invariant at the outer loop head 0x33bac (DMseg_mbh.SS0), as H1 states it: the kept prefix [done], the
   current batch [cur], its successor [nx], the rest [t], and the extracted batches [ex].  Registers: a4 = cur,
   t0 = nx, a2 = the extracted bytes, a5 = kBatchSlots, a6 = -8192, a7 = 8192, a0 = the list head, a1 = Recycle's
   sp, sp = spr - 16, ra = 0x33a38 (DMseg_mbh.at_ADV :153 names the same registers).  [mb_inv] is stated here so
   that H1, the reviewer and DMdrain read ONE text; H1 proves [mb_inv_entry] (its satisfiability at the loop's
   first arrival, from DMseg_mbe.at_MBH) as its first lemma, then the loop. *)
Definition mb_inv (done : list batch) (cur nx : batch) (t ex : list batch)
(W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\
(* the model: the merge of the whole list is the kept prefix plus the merge of what is left *)
MB L0 = (done ++ fst (MB (cur :: nx :: t)), ex ++ snd (MB (cur :: nx :: t))) /\
(* the lists' shape *)
(forall b, In b (done ++ cur :: nx :: t) -> In (b_self b) (map b_self L0)) /\
(forall b, In b ex -> In (b_self b) (map b_self L0) /\ b_items b = []) /\
List.NoDup (map b_self (done ++ cur :: nx :: t ++ ex)) /\
Forall (fun b => (length (b_items b) <= Z.to_nat kBatchSlots)%nat) (done ++ cur :: nx :: t) /\
(* the items are the entry list's, in order: a merged batch is NOT in L0, so its size bound
   (DMseg_mbh.fh_Hcsz :96, DMseg_mbt.fh_Hsz :135, fh_Hby :143) comes from here, not from mb_nn *)
flat_map b_items (done ++ cur :: nx :: t) = flat_map b_items L0 /\
sum_bytes (done ++ cur :: nx :: t) + kBatchBytes * zl ex = sum_bytes L0 /\
(exists regs' mem' mat,
 c' = mkCfg (mkst regs' (w64 0x33bac) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
 getr regs' 2 = w64 (spr - 16) /\ getr regs' 1 = w64 0x33a38 /\
 (forall r : bv 5, In r SREGSX -> getr regs' r = getr regs0 r) /\
 getr regs' 10 = w64 (A_QUAR + 160) /\ getr regs' 11 = w64 spr /\
 getr regs' 12 = w64 (kBatchBytes * zl ex) /\ getr regs' 14 = w64 (addrb ly cur) /\
 getr regs' 5 = w64 (addrb ly nx) /\ getr regs' 15 = w64 kBatchSlots /\
 (* a6 = -8192, which the tail adds into size (cur) at 0x33c04 and DMseg_mbt's seed pins (DMseg_mbt.v:128) *)
 getr regs' 16 = w64 18446744073709543424 /\ getr regs' 17 = w64 kBatchBytes /\
 (forall x : word, ~ mbwin (done ++ cur :: nx :: t) ex (bv_unsigned x) -> mem' x = mem0 x) /\
 (forall a, mbwin (done ++ cur :: nx :: t) ex a -> kHighMemBeg <= a -> apresent (w_H W) mem' a) /\
 (let m := mrestrict (w_H W) mem' in
  (* the global list's header.  The loop DOES write the count word (0x33c30 / 0x33c58: count - 1 per merge) and
     the last word (0x33c50: last := cur when the extracted batch was the last one), so both are stated at the
     cut over the current list; the first word (+168) is never written; the bytes word (+184) is written only at
     the exit, 0x33c90-0x33c98 (DMseg_mbt.tail_cells :219, DMseg_mbh.at_EXH :164) *)
  val_mem tfibsegs m (A_QUAR + 160) 8 (zl (done ++ cur :: nx :: t)) /\
  val_mem tfibsegs m (A_QUAR + 168) 8 (fa ly L0 0) /\
  val_mem tfibsegs m (A_QUAR + 176) 8 (la ly (done ++ cur :: nx :: t)) /\
  val_mem tfibsegs m (A_QUAR + 184) 8 (sum_bytes L0) /\
  (* the temp list's header over [ex] *)
  val_mem tfibsegs m spr 8 (zl ex) /\ val_mem tfibsegs m (spr + 8) 8 (fa ly ex 0) /\
  val_mem tfibsegs m (spr + 16) 8 (la ly ex) /\ val_mem tfibsegs m (spr + 24) 8 (kBatchBytes * zl ex) /\
  (* MergeBatches' saved return address *)
  val_mem tfibsegs m (spr - 8) 8 0x33a38 /\
  (* the list and the temp list, linked *)
  lcn ly iw m (done ++ cur :: nx :: t) 0 /\ lcn ly iw m ex 0)).

(* H1's first lemma: the invariant holds when the loop is first entered (from DMseg_mbe.segE / at_MBH), with
   [done] and [ex] empty and [cur :: nx :: t] the whole list.  This is the satisfiability witness VERIFY 21:4xZ
   asks for: it is PROVED, not assumed. *)
Definition mb_inv_entry_t : Prop :=
mb_pre -> forall b1 b2 t, L0 = b1 :: b2 :: t ->
SRr tfibsegs W cfgMB (mb_inv [] b1 b2 t []).

(* H1's model obligations (pure, no machine): what DMdrain reads off merge_batches_cf. *)
Definition mb_model_facts : Prop :=
forall l : list batch,
(* the bytes: each extracted batch is an empty one, worth kBatchBytes *)
sum_bytes (fst (MB l)) + kBatchBytes * zl (snd (MB l)) = sum_bytes l /\
(* the items are kept, in order *)
flat_map b_items (fst (MB l)) = flat_map b_items l /\
(* the extracted batches are empty *)
Forall (fun b => b_items b = []) (snd (MB l)) /\
(* the batch objects are the same ones (with the lengths, this transfers NoDup) *)
(forall s, In s (map b_self l) <-> In s (map b_self (fst (MB l)) ++ map b_self (snd (MB l)))) /\
length l = (length (fst (MB l)) + length (snd (MB l)))%nat /\
(* the kept list keeps the slot bound and is non-empty when the input is *)
(Forall (fun b => (length (b_items b) <= Z.to_nat kBatchSlots)%nat) l ->
 Forall (fun b => (length (b_items b) <= Z.to_nat kBatchSlots)%nat) (fst (MB l))) /\
(l <> [] -> fst (MB l) <> []) /\
(* the first batch is kept (the list's first word is never written) *)
(forall b t, l = b :: t -> exists t', fst (MB l) = b :: t' \/ exists its, fst (MB l) = mkBatch (b_self b) its :: t').
End mb.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2b. The two reads of the cut that DMiface's field list does not carry (measured 2026-10-30 by the lane's two
   read-only scouts over the released walks; reported to CfF2b, who discharges them at ARXr_cf / DRq_cf, and to
   DGif1dI / DGif1dr for the cgif instance).  They are stated here, not in DMiface.v / DGif0.v, which are
   a Theorem Labs lane's files.
   - [di_rview_x_t]: DMiface.di_rview_t plus the class-24 region's allocated bound.  DoRecycle's segments need it
     at every cut (YFhc.fh_Hb YFhc.v:94, DMrec.RZ.fh_Hb DMrec.v:93, the s7 bound DGif1db.v:197, region_in_prim);
     the released walk takes it from Wf inside YFhf.slot_carved (YFhf.v:70-79), and DMiface.qview's qv_geom
     (DMiface.v:92-95) holds only at Drain's entry and bounds by kFreeArrayOffset, which is larger.  The bound is
     NOT the literal 2 ^ 31: that is cgif's event-derived wr_mapped_bound (YG06.v:132, YFgq.v:134), while the cf
     class bound is wrc_mapped_bound = kFreeArrayOffset = 0xE0000000 (YG01cf.v:48-49; preset's class 17 maps
      3,584 MiB), so it is the Section Variable [RMAXD] with [rmaxd_ok] (2 ^ 31 <= RMAXD <= kFreeArrayOffset), the name
     and premise lane B2 uses in EnqGbase (ReallocPrimary 00:0xZ): 2 ^ 31 at cgif, kFreeArrayOffset at cf.
     CfF2b proves the kFreeArrayOffset form at every cut (YGcfInstDrainQ.slot_carved_cf).
   The free-array room is NOT a field: CfF2b measured (00:0xZ) that YG03cf.RIx_cf / WfR_cf carry none and that
   the property is FALSE on reachable cf states - a Theorem Labs lane dropped cgif's wf_fa_room (YG01cf.v:55-67) because
   cgif's room came from an event term (the remaining event budget), which the EVENT-TERM GATE forbids, and the free
   path really does grow the free array.  So H3 WALKS EnsureFreeArraySpace (FGt.tfib_efa_spec, FGt.v:85-88); its
   first deliverable is the list of fields the 13 premises of FGt.efa_pre (FGt.v:56-79) need at a CacheDealloc
   cut, reported to WalkB1, who states them here and sends them to CfF2b (who offers a growth-funded budget
   conjunct on ARXr_cf for the KMapFreeArray grant). *)
Section rd.
Variable B : asyms.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Variable RMAXD : Z.
(* The upper bound is kFreeArrayOffset, not 2 ^ 32 (reviewer RevIF2, finding 4): the class's free array sits at
   region_off c + kFreeArrayOffset and ImgBaseDG's puser covers region_base .. + rg_alloc_user, so an allocated
   part above kFreeArrayOffset would put the free-array stores INSIDE puser and make cdealloc_g_t's puser frame
   false; YFgk's fh_Hoff (YFgk.v:153) wants RELv + class_size <= kFreeArrayOffset for the same reason.  Both
   instances fit: 2 ^ 31 at cgif, kFreeArrayOffset at cf.  Lane B2 uses the same premise in EnqGbase. *)
Definition rmaxd_ok : Prop := 2 ^ 31 <= RMAXD <= kFreeArrayOffset.
Definition di_rview_x_t : Prop :=
di_rview_t B ARXr DRq /\
(forall inst ly X W mem md its zs, ARXr inst ly X W mem md -> DRq X its zs ->
 rg_alloc_user (reg X kBatchClass) <= RMAXD).
End rd.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. H2: DoRecycle (0x33cf8) over the opaque cut relation and recycle invariant.                                   *)
(* The released walk (YFes / YFhd / YFhg / YFhl, restated to the DIface types in DGif1da / DGif1db / DGif1dc and
   with errno / memnorm in DGif1daE / DGif1daM) runs over cgif's AR and RIx, fuel 100000, and never enters the
   COUNT-0 batch arm (its RIx demands 1 <= count).  H2 restates it over [ARXr] and [DRq], with fuel [length P]
   and that arm (0x33d9c ld s6 = count, 0x33da0 beqz -> 0x33dc8; the shell is DMrec.v's module RZ).
   H2 also writes the twins of the three places that fix the class-24 region bound at the LITERAL 2 ^ 31 -
   DMrec.RZ.fh_Hb (DMrec.v:93), YFhc.fh_Hb (YFhc.v:94) and the s7 step they carry (DGif1db.v:197) - restated as
   b + kBatchBytes <= ly_space ly + region_off kBatchClass + RMAXD (reviewer RevIF2, finding 3; the class
   computation at 0x33ddc-0x33de4, bits 32..36 of b - base, stays 24 for every RMAXD <= 2 ^ 32). *)
Section dr.
Variable B : asyms.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Variable RMAXD : Z.

(* DoRecycle's own frame (112) plus the recycle callees' window KSTACK_CF = 2048 (DMiface.v:133), rounded up to
   16: DGif1da.DRSTACK_X (DGif1da.v:30), kept here so H2 and DMdrain read one number. *)
Definition DRSTACK_X : Z := 2176.

(* Recycle calls DoRecycle with a0 = inst + o_quar, a1 = Recycle's sp (the temp list), a2 = T + t_cache
   (DMseg_rj.at_RJX, DMseg_rj.v:138-144; DMdeq.ATDR, DMdeq.v:193-207).  The model premises are the instance's:
   [ARXr] at the cut, [DRq] with every chunk and every batch object of [P] still to recycle.
   [inst = as_inst B] is NOT redundant: DoRecycle overwrites a0 at 0x33d28 and builds the allocator address as a
   CONSTANT with auipc at 0x33d3c / 0x33d44 (the space-base load at 0x33dc8 reads A_ALLOCATOR + 32; DMrec.RZ's
   fh_regs DMrec.v:91 and at_CD0 DMrec.v:174 are over A_ALLOCATOR), so the walk needs the instance to BE the
   image's allocator; with TfibSyms B that is as_inst B = TFIB_INST = A_ALLOCATOR.  The released DGif1da fixes
   TFIB_INST outright (DGif1da.v:47-50). *)
Definition dr_pre_r (inst : Z) (ly : alayout) (X : astate) (P : list batch) (W : world tfibsegs)
(regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
ARXr inst ly X W mem md /\ inst = as_inst B /\ DRq X (flat_map b_items P) (map b_self P) /\
(* The two facts DoRecycle's segment seeds read from the relation at cgif (DMrec.RZ.free_hyps' fh_LY / fh_IMG,
   DMrec.v:85-86, through YFhl.entry_facts; YFha / YFhc the same), as CONJUNCTS of the call's premise and NOT as
   instance fields: the drain discharges both at the call site - the layout from DMiface.qview's qv_ly / qv_img
   at Drain's entry, since ly does not change inside the drain, and the stack clause from drain_reads'
   di_stack_t ARX AOX at the pre-transfer state with di_requar_r_t's owned shrink - and inside DoRecycle both
   stay true by themselves, ly being unchanged and every callee post shrinking AOX (H2's and Main's form,
   00:43Z; it replaces the di_stack_t ARXr AOX field of the 00:3xZ request). *)
layout_ok ly /\ img_cover ly /\
(forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ AOX ly X a) /\
Forall (fun b => (length (b_items b) <= Z.to_nat kBatchSlots)%nat) P /\
zl P < 2 ^ 40 /\ st_cache_inited X = true /\
YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + DRSTACK_X <= spZ regs /\ spZ regs + 32 <= ly_stk_hi ly /\
(forall a, spZ regs - DRSTACK_X <= a < spZ regs + 32 -> apresent (w_H W) mem a) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 10 = w64 (inst + o_quar) /\ getr regs 11 = w64 (spZ regs) /\ getr regs 12 = w64 (ly_T ly + t_cache) /\
Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (YFeuC.plist_cells (spZ regs) P).

(* The return: the post of DMspec.acall_post_x over ARXr with the temp-list header as the extra changed set
   [E], the raw frame (DIfaceR.acall_raw_x), errno and memnorm kept, and nothing left to recycle. *)
Definition dr_leaf_r (inst : Z) (ly : alayout) (X : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (r : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
acall_post_x B ARXr AOX inst DRSTACK_X ly X W regs mem md (fun a => spZ regs <= a < spZ regs + 32)
  ly (snd r) W' regs' mem' md' /\
acall_raw_x B AOX inst DRSTACK_X ly X W regs mem md (fun a => spZ regs <= a < spZ regs + 32)
  ly (snd r) W' regs' mem' md' /\
ErrnoG.errno_kept B mem mem' /\ MemnormT.memnorm_keep tfibsegs mem mem' /\
DRq (snd r) [] [] /\ st_cache_inited (snd r) = true /\
(forall a, AOX ly (snd r) a -> AOX ly X a) /\
(forall a, spZ regs <= a < spZ regs + 32 -> apresent (w_H W') mem' a).

(* H2's head.  Its callee hypotheses are H4's and H3's contracts, in MnRecycle's forms. *)
Definition dorecycle_spec_r : Prop :=
forall inst ly X P W regs mem md,
dr_pre_r inst ly X P W regs mem md ->
amreal tfibsegs (do_recycle (length P) P X) W (cfg_at tfibsegs A_DoRecycle regs mem md)
  (dr_leaf_r inst ly X W regs mem md).

Definition dorecycle_ok_t : Prop :=
TfibSyms B -> rmaxd_ok RMAXD ->
di_frame_t ARXr AOX -> di_rview_x_t B ARXr DRq RMAXD ->
MnRecycle.de_rchunk_m_t B ARXr AOX DRq -> MnRecycle.de_cdealloc_m_t B ARXr AOX DRq ->
dorecycle_spec_r.
End dr.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. H3 / H4: the recycle callees over the opaque cut relation.                                                    *)
(* Their heads are MnRecycle's types at the cgif image.  SIZE BOUNDS (Main 23:3xZ, DEALLOC-NMAX.md (sha256 5c7eb4623df3; internal record)): the released
   cgif frames these two slices copy carry the request bound 2 ^ 28 (YFgp.v:97, YFgq.v:125, YFgr.v:146,
   YFgs.v:154, YFgx.v:122, YFh7.v:252) and the secondary map bound 2 ^ 29 (YFgx.v:119), and fuzz_reply's blocks
   and maps pass both.  No new statement may hold such a literal: the two
   bounds are the Section Variables [NMAXD] (a quarantined chunk's user size) and [LMAXD] (its mapped extent)
   with the premises below, and the slice reads them off the recycle invariant through [drq_sizes].
   What each walk may read of the machine is DMiface.di_rview_t plus the fields the slice names in its own file
   (a record in DMcd*.v / DMrc*.v).  A slice that needs a field beyond the hypotheses below does NOT add it to
   its own head: it reports the field (statement + why) to ReallocPrimary, who sends it to WalkB1; WalkB1 adds it
   here and to CfF2b's discharge list, so the seam and the tops stay one text. *)
Section callees.
Variable B : asyms.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Variables (NMAXD LMAXD RMAXD : Z).
(* stated, not assumed: each head below takes the premise it needs *)
Definition nmaxd_ok : Prop := 2 ^ 28 <= NMAXD <= 2 ^ 30.
(* the cap is 2 ^ 31 - 8192: the cf big arm's mapped extent is sec_map_size (2 ^ 30 - 15) = 2 ^ 30 + 8192 (YG00.v:74),
   and H4's secondary arm needs its map length LMAXD + kPage below 2 ^ 31 (DMrcSecFc.GEOMw) *)
Definition lmaxd_ok : Prop := NMAXD <= LMAXD <= 2 ^ 31 - 8192.

(* The sizes of what is still to recycle, as the instance's invariant gives them (cgif: RIx's chunk facts with
   NMAXD := 2 ^ 28; cf: DRq_cf's, with NMAXD := kQuarantineMax = 2 ^ 28, the quarantine-entry bound - one meaning
   across the layer, CF-LAYER-LANES.md (sha256 f291131825b7; internal record) 'NMAXD, ONE MEANING'). *)
Definition drq_sizes : Prop :=
forall S its zs k, DRq S its zs -> In k its -> 0 <= ck_n k < NMAXD /\ ck_extent k <= LMAXD.

(* H3: SizeClassAllocator64LocalCache::Deallocate (0x34234), the released YFg0 / YFfi / YFez / YFgk / YFgy / YFgz
   walk over an opaque ARXr.  Two forms, because H4's primary arm TAIL-CALLS this function for a USER chunk of
   class [prim_class off] (1 .. 30), not for a class-24 batch object, so MnRecycle.de_cdealloc_m_t (class fixed to
   kBatchClass, premise DRq X its (z :: zs)) cannot serve it (measured by the lane's scout over YFg7.CDPRE /
   YFgs):
   - [cdealloc_g_t], the CLASS-GENERIC form over the model premises [cd_model] - H3's main deliverable, which H4
     uses for its tail call;
   - [cdealloc_m_t] = MnRecycle.de_cdealloc_m_t, from it and the invariant's bookkeeping [drq_cd].
   The free-array growth arm (ReturnToAllocator 0x3476c -> EnsureFreeArraySpace 0x34a94) IS reached at cf and
   must be walked, through the released allocator-relation-free callee FGt.tfib_efa_spec (FGt.v:85-88): cgif
   refutes it from the invariant's free-array room (DGif1dr.v:26-30, YFfi.v:462, YG0l.return_room), but that room
   is event-derived (the remaining event budget) and a Theorem Labs lane dropped it at cf (YG01cf.v:55-67; CfF2b 00:0xZ), so it
   is neither a premise here nor a field.  The stack then reaches 1264 bytes (frames 48 + 64 + 128 and FGt's
   RSTACK 1024), inside KSTACK_CF = 2048.  H3's FIRST deliverable is the list of fields FGt.efa_pre's 13
   premises (FGt.v:56-79: the vm reservation, the map, the budget, the shadow presence, mf's alignment and
   bound) need at a CacheDealloc cut; it reports them to WalkB1, who states them here and sends them to CfF2b. *)
Definition cd_pre_cx (inst : Z) (ly : alayout) (X : astate) (c off : Z) (W : world tfibsegs)
(regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
ARXr inst ly X W mem md /\ inst = as_inst B /\ st_cache_inited X = true /\
YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + KSTACK_CF <= spZ regs /\ spZ regs <= ly_stk_hi ly /\
(forall a, spZ regs - KSTACK_CF <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 10 = w64 (ly_T ly + t_cache) /\ getr regs 11 = w64 inst /\ getr regs 12 = w64 c /\
getr regs 13 = w64 (ly_space ly + off) /\
(* the room the free-array GROWTH arm needs at the call (only that arm: the guard is its branch test), the
   inequality a Theorem Labs lane's room of record gives at the cut; stated without the cf layer, which sits above this
   interface *)
(rg_mapped_fa (reg X c) < 4 * (fa_len (rg_free (reg X c)) + max_cached c / 2) ->
 eager_used md + A_bytes (w_A W) + 2 * kUserMapSize + 32768 <= vm_limit (m_vmmaps md)).

(* The model premises the walk needs of the object it returns to the cache (the scout's M1 / M2 over the released
   seed YFfi.FH_ok and leaf YFg0.FINKH, with reviewer RevIF2's finding 5).  cgif's wf_class / wr_* are NOT used:
   the cf instance's class well-formedness is YG01cf.wf_class_cf, so only the consequences the walk reads are
   listed, with the class bound at [RMAXD].  The five conjuncts the first draft lacked are the ones the released
   seed takes from wf_class and the growth arm needs: the cache's limit word (YFfi's reg_facts through wr_cache,
   YG01.v:378 - the model branches on pc_max, YG00.v:471, so without the equation the model and the machine can
   take different arms), the allocated part's alignment (wr_alloc_al, YFfi.v:85, which with the RMAXD bound
   gives fh_Hoff's RELv + class_size <= kFreeArrayOffset), the mapped free array's bound and its alignment
   (wr_fa_bound, YFfi.v:86; seed atoms YFgk.v:121 and FGt.efa_pre's FGt.v:61), the count bound FGt.efa_pre asks
   (FGt.v:60), and the growth step's room, which refutes ensure_free_array's mcheck (YG00.v:266, an IFail arm
   that asafe makes False). *)
Definition cd_model (S : astate) (c off : Z) : Prop :=
1 <= c <= 30 /\ st_cache_inited S = true /\
Z.of_nat (length (pc_chunks (cache S c))) <= max_cached c /\
pc_max (cache S c) = max_cached c /\
0 <= off - region_off c /\ off - region_off c < rg_alloc_user (reg S c) /\
(off - region_off c) mod class_size c = 0 /\ ~ In (off - region_off c) (class_elems S c) /\
rg_alloc_user (reg S c) <= RMAXD /\ rg_alloc_user (reg S c) mod class_size c = 0 /\
0 <= fa_len (rg_free (reg S c)) /\ 4 * fa_len (rg_free (reg S c)) <= rg_mapped_fa (reg S c) /\
rg_mapped_fa (reg S c) <= kFreeArrayMax /\ rg_mapped_fa (reg S c) mod kFreeArrayMapSize = 0 /\
fa_len (rg_free (reg S c)) + max_cached c / 2 <= 2 ^ 27 /\
(rg_mapped_fa (reg S c) < 4 * (fa_len (rg_free (reg S c)) + max_cached c / 2) ->
 rg_mapped_fa (reg S c) + kFreeArrayMapSize <= kFreeArrayMax).

Definition cdealloc_g_t : Prop :=
forall inst ly X c off W regs mem md,
cd_pre_cx inst ly X c off W regs mem md -> cd_model X c off ->
amreal tfibsegs (cache_dealloc c off X) W (cfg_at tfibsegs A_CDealloc regs mem md)
(fun r W' c' => exists regs' mem' md',
  c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
  acall_post_x B ARXr AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  acall_raw_x B AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  ErrnoG.errno_kept B mem mem' /\ MemnormT.memnorm_keep tfibsegs mem mem' /\
  (forall a, 0 <= a < 2 ^ 64 -> YFeuC.puser ly X a -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) /\
  (forall a, YFeuC.puser ly X a -> YFeuC.puser ly (snd r) a) /\
  st_cache_inited (snd r) = true /\ (forall a, AOX ly (snd r) a -> AOX ly X a)).

(* CacheDealloc's model RETURNS with the state [S']: either at once, or - on the free-array growth arm, whose
   root is the request KMapFreeArray (YG00.v:267, ensure_free_array) - through a GRANTED answer of that request
   (aGranted, YG00.v:104), the only continuation amreal follows without spinning (YG0d.v:82-89).  The consumer
   names the grant its walk saw; the only granted answer is 1 (aGranted z := z =? 1). *)
Definition cd_returns (c z : Z) (S S' : astate) : Prop :=
cache_dealloc c z S = IRet (tt, S') \/
exists c0 old dl snap k g, cache_dealloc c z S = IAsk (KMapFreeArray c0 old dl) snap k /\
  aGranted g = true /\ k g = IRet (tt, S').

(* The invariant's bookkeeping for a batch object: its premises, and the invariant after the step. *)
Definition drq_cd : Prop :=
forall S its z zs, DRq S its (z :: zs) ->
cd_model S kBatchClass z /\
(forall S', cd_returns kBatchClass z S S' -> DRq S' its zs).

Definition cdealloc_m_t : Prop := MnRecycle.de_cdealloc_m_t B ARXr AOX DRq.
Definition cdealloc_ok_t : Prop :=
TfibSyms B -> nmaxd_ok -> lmaxd_ok -> rmaxd_ok RMAXD -> drq_sizes ->
di_frame_t ARXr AOX -> di_rview_x_t B ARXr DRq RMAXD ->
cdealloc_g_t /\ (drq_cd -> cdealloc_m_t).

(* H4: __asan::QuarantineCallback::Recycle (0x33e30): the primary arm (header write, poison, the thread stats, the
   chunk's shadow, then the TAIL CALL into CacheDealloc at 0x34234 with a2 = prim_class off) and the secondary arm
   (LargeMmapAllocator::Deallocate: the chunks array, the stats, the munmap ecall at 0x65a14, world
   wrefund (MAP, MAP + LEN)), the released YFfs / YFg7 / YFgs / YFfr / YFh7 / YFf3 / YFg8 / YFg9 / YFgv / YFf4
   walks over an opaque ARXr.  It takes H3's CLASS-GENERIC contract for the tail call. *)
Definition rchunk_m_t : Prop := MnRecycle.de_rchunk_m_t B ARXr AOX DRq.
Definition rchunk_ok_t : Prop :=
TfibSyms B -> nmaxd_ok -> lmaxd_ok -> rmaxd_ok RMAXD -> drq_sizes ->
di_frame_t ARXr AOX -> di_rview_x_t B ARXr DRq RMAXD -> cdealloc_g_t -> rchunk_m_t.
End callees.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 5. The lane's top (mine, the DMdrain files): Quarantine::Drain (0x337ec) with the REAL MergeBatches.             *)
Section t1.
Variable B : asyms.
Variable ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable L24 : Z.
Variable QB : astate -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Variable RMAXD : Z.

(* What the drain reads of the machine through the opaque relations: DGif0.DIface's drain-side field types
   (DGif0.v:346-354, :375-376), which CfF2a and CfF2b discharge at the cf instance. *)
Definition drain_reads : Prop :=
di_qview_t B ARX L24 QB /\ di_qowned_t ARX AOX L24 QB /\ di_stack_t ARX AOX /\
di_frame_t ARX AOX /\ di_frame_t ARXr AOX /\
di_requar_x_t B ARX AOX L24 QB /\ di_requar_r_t B ARX ARXr AOX L24 QB DRq /\
di_requar_e_t ARX ARXr DRq /\ di_rview_x_t B ARXr DRq RMAXD.

(* The lane's top: the drain contract of the seam (CfF2b's YGcfInstDrainSig ds_drain) at the shared model's
   drain tree, from the read fields and the three walks. *)
Definition drain_m_cf_t : Prop :=
TfibSyms B -> drain_reads ->
MnRecycle.de_rchunk_m_t B ARXr AOX DRq -> MnRecycle.de_cdealloc_m_t B ARXr AOX DRq ->
MnDrain.de_drain_m_t B ARX AOX drain_body_cf L24 QB.

(* The top with its instance premises inside the contract, as rchunk_ok_t / cdealloc_ok_t carry theirs: QB's two
   byte bounds (at the shared instance DMdrainG4.QBB_of_QB_cf with NMAXD = kQuarantineMax = 2 ^ 28), the batch
   bound on L24 (at cf L24MAX_cf = kFreeArrayOffset / class_size kBatchClass) and rmaxd_ok (H2's DoRecycle walk
   takes it).  The instance discharges these three; the rest of drain_m_cf_t is the seam's contract. *)
Definition drain_ok_t : Prop :=
rmaxd_ok RMAXD -> L24 < 2 ^ 40 ->
(forall X, QB X -> qc_bytes (st_qglobal X) <= 2 ^ 30 /\ qc_bytes (st_qthread X) <= 2 ^ 29) ->
drain_m_cf_t.
End t1.
End d.
