(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DGif0.v (commit 30a1993588f, c5 + memnorm; file sha256 ecff08057d88) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from lib/A/DGif0.v (commit d2dafa219c1, file sha256 f198d42624d1) onto plugin-hostd/fuzz_reply's asan-ubsan image (unstripped fuzz_reply.asan-ubsan, sha256 3389287e1d61; pin 10ffb5f9202a) by alreloc ced0368250cb6538 (A -> B, direct map 541d2a13b9d2): 0 numerals moved; module paths lib.A -> lib.B and the image twins A<r> -> Y<r>. *)
(* The interface between the frame-generic walk of Allocator::Deallocate (the DG* files) and an allocator model.

   DeallocG.adealloc_realizes is stated over an opaque allocator relation [ARX inst ly S W mem md], an owned set
   [AOX ly S a], a premise [rpre S n], a free tree [ft], a post [lpost] and the free call site's premise [fpre].  The
   walk reads the machine through [ARX] only by the fields of [DIface] below; an instance (cgif_file: ARX_cgif, the
   shared instance) proves each field once.  [dpost] is the post of the depot callee (AGif0n's pattern).

   The fields:
   - [di_inst]: the instance object lies where the image puts it ([dg_inst_ok]; cgif: AGif0cgif.inst_ok);
   - [di_view_n], [di_view]: the machine facts the seeds need (DGgn.SS0: [dview_n]; DGgi.SS0 / DGgm.SS0: [dview],
     with the last batch's cells [dbview] for the arm whose last batch has room);
   - [di_shape_n], [di_shape]: the free tree after its entry step (the tick and the no-op internal-allocator init):
     [ret tt] for NULL; for a live block: depot_put, the change to CQuarantined, enqueue, then [dmd dbody] (the
     thread-cache test, and the drain tree [dbody] above it: cgif drain_body, the shared instance drain_body_cf);
   - [di_depot], [di_dpost_aok]: StackDepotPut's contract (QuarantineChunk's call), and the depot answer it gives;
   - [di_enqueue]: QuarantineCache::Enqueue's contract at Put's call (the batch-allocating path; arms mid and drain),
     from the state at Deallocate's entry and the memory at the call ([dmem_m]);
   - [di_drain]: Quarantine::Drain's contract, DMspec.drain_spec_cf over ARX / AOX / [dbody] / [L24] / [QB]
     (a0 = inst + o_quar; arm drain); [di_lpost_d]: lpost at the end of a granted path of the drain tree;
   - [di_post_c], [di_post_n]: the post at Deallocate's return of the arm whose last batch has room ([dmem_c]) and of
     the NULL arm ([dmem_n]) gives ARX and lpost of the final state;
   - [di_frame], [di_stack]: ARX does not depend on memory outside AOX, and AOX avoids the stack (the released
     AR_frame_law / AR_stack_law; DMiface's types);
   - [di_qview], [di_qowned], [di_requar_x], [di_requar_r], [di_requar_e], [di_rchunk], [di_cdealloc],
     [di_frame_r], [di_rview]: the real-merge drain's reads (DMiface.v): the quarantine's view at Drain's entry,
     its owned words, the relation re-established at the drain's cuts (ARX after the transfer; the cut relation
     [ARXr] and the recycle invariant [DRq] at DoRecycle's call, ARX again when nothing is left), Recycle's and
     CacheDealloc's contracts and the frame law over ARXr, and what DoRecycle reads at every cut (the space-base
     word, the pending chunks' headers, the pending batch objects);
   - [di_owned], [di_owned_b], [di_owned_i], [di_owned_x]: the addresses the walk writes outside its stack windows
     are owned (or are the freed block's bytes), and the owned set of the quarantined state is the entry state's
     plus the block.

   The file is image-free: the binary's segments, data cells, image window and zones and the entry pcs it calls are
   the fields of the classes ImgBase.AImg and ImgBaseDG.DImg ([Context {IM : AImg} {DI : DImg}]); cgif_file's
   instances are AGif2cgif.AImg_cgif and DGif0cgif.DImg_cgif.  The image-free names it borrows from the cgif walk
   files (DGgi / DGgm geometry, the stack sizes, depot_after, drain_body) are ImgBaseDG's copies (DGgiC.Bv is the
   copy of DGgi.Bv). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import DMspec DMiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import DeallocG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseDG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {IM : AImg} {DI : DImg}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Model-level names.                                                                                               *)

(* The quarantine step after Enqueue: the thread-cache test, then the drain tree [dbody] (YFeu.maybe_drain_eq /
   DMspec.maybe_drain_cf_eq: cgif maybe_drain = dmd drain_body, the shared maybe_drain_cf = dmd drain_body_cf). *)
Definition dmd (dbody : astate -> M unit) : M unit :=
s <- get ;; if qc_bytes (st_qthread s) <=? kQuarantineCacheMax then ret tt else dbody s.
Lemma dmd_cgif : maybe_drain = dmd YFeuC.drain_body. Proof. reflexivity. Qed.
Lemma dmd_cf : YG00cf.maybe_drain_cf = dmd drain_body_cf. Proof. reflexivity. Qed.
(* The state after the tick. *)
Definition dtick (S : astate) : astate := set_nev (st_nev S + 1) S.
(* The quarantined chunk, and the state after the depot answer [z] and the chunk's change (before Enqueue). *)
Definition qk (k : chunk) : chunk := mkChunk (ck_beg k) (ck_req k) CQuarantined.
Definition qx (S : astate) (k : chunk) (z : Z) (tr : list Z) : astate :=
set_chunks (upd_chunk (st_chunks (YFl0C.depot_after z tr (dtick S))) (qk k)) (YFl0C.depot_after z tr (dtick S)).
(* The final state of the arm whose last batch has room (Enqueue inline, no drain). *)
Definition qfin_c (S : astate) (k : chunk) (z : Z) (tr : list Z) : astate :=
set_qthread (qc_push (st_qthread (qx S k z tr)) (qk k) None) (qx S k z tr).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Machine-level predicates.                                                                                        *)

(* The freed block's shadow bytes. *)
Definition dshadow (pa nn a : Z) : Prop := DGgiC.SPv pa <= a < DGgiC.SPv pa + DGgiC.CNT8v nn.

(* (view) The facts every seed needs (DGgn.SS0: the NULL seed). *)
Record dview_n (B : asyms) (W : world im_segs) (ly : alayout) (inst : Z) (mem : word -> option byte) : Prop := {
  dn_ly : layout_ok ly;
  dn_img : im_img_cover ly;
  dn_tsd : ly_tsd ly = im_tsd;
  (* the image's constant cells (global literals, the thread and context objects' fixed words) *)
  dn_const : Forall (cell_holds B ly (aview im_segs (w_H W) mem)) (as_const B ly);
  (* the instance's quarantine fields read by the seed *)
  dn_inst : val_mem im_segs (mrestrict (w_H W) mem) (inst + 0x318) 8 0x10000000 /\
            val_mem im_segs (mrestrict (w_H W) mem) (inst + 0x328) 8 0x100000;
  (* the internal allocator is initialized *)
  dn_ial : dg_ial_post W mem;
  (* the thread's unwinding flag is clear *)
  dn_unw : val_mem im_segs (mrestrict (w_H W) mem) (ly_T ly + t_unwinding) 1 0
}.

(* (view) The last batch of the thread's quarantine cache (the arm whose last batch has room: DGgi.SS0). *)
Record dbview (W : world im_segs) (ly : alayout) (mem : word -> option byte) (q : qcache) (lastb : batch) (pa nn : Z) : Prop := {
  db_qc : val_mem im_segs (mrestrict (w_H W) mem) (ly_T ly + t_qc) 8 (DGgiC.QSv q) /\
          val_mem im_segs (mrestrict (w_H W) mem) (ly_T ly + t_qc + 8) 8 (DGgiC.QFv ly q) /\
          val_mem im_segs (mrestrict (w_H W) mem) (ly_T ly + t_qc + 16) 8 (DGgiC.Bv ly lastb) /\
          val_mem im_segs (mrestrict (w_H W) mem) (ly_T ly + t_qc + 24) 8 (DGgiC.QBv q);
  db_b : val_mem im_segs (mrestrict (w_H W) mem) (DGgiC.Bv ly lastb + 8) 8 (DGgiC.BBv lastb) /\
         val_mem im_segs (mrestrict (w_H W) mem) (DGgiC.Bv ly lastb + 16) 8 (DGgiC.BCv lastb);
  (* the slot word is inside the batch object only while the batch has room: at BCv = kBatchSlots, SLOTv is the
     first word after it *)
  db_pres : forall a, DGgiC.Bv ly lastb + 8 <= a < DGgiC.Bv ly lastb + 24 \/
              (DGgiC.BCv lastb < kBatchSlots /\ DGgiC.SLOTv ly lastb <= a < DGgiC.SLOTv ly lastb + 8) ->
            apresent (w_H W) mem a;
  db_range : ly_space ly <= DGgiC.Bv ly lastb /\ DGgiC.Bv ly lastb + kBatchBytes <= ly_space ly + kSpaceSize /\
             0 <= DGgiC.QFv ly q < 2 ^ 64 /\ DGgiC.Bv ly lastb mod 8192 = 0;
  db_disj : DGgiC.PBDISJ ly pa nn lastb;
  db_bounds : 0 <= DGgiC.BBv lastb /\ DGgiC.BBv lastb + nn < 2 ^ 48 /\ DGgiC.QSv q < 2 ^ 48;
  db_slots : DGgiC.BCv lastb <= kBatchSlots
}.

(* (view) The facts the live-block seeds need (DGgi.SS0, DGgm.SS0), for the block [p] of size [n]. *)
Record dview (B : asyms) (W : world im_segs) (ly : alayout) (inst : Z) (mem : word -> option byte) (S : astate) (p : sptr) (n : Z) : Prop := {
  dv_n : dview_n B W ly inst mem;
  dv_nonnull : p <> PNull;
  (* the model's chunk *)
  dv_chunk : exists k, find_user (st_chunks S) p = Some k /\ ck_state k = CAllocated /\ ck_user k = p /\ ck_req k = n;
  (* the chunk header: chunk_state CHUNK_ALLOCATED (2), the second byte [hb1], the user size *)
  dv_hdr : exists hb1, 0 <= hb1 < 256 /\ Z.land hb1 127 = 17 /\
           val_mem im_segs (mrestrict (w_H W) mem) (sptr_addr B ly p - 16) 4 (2 + 256 * hb1) /\
           val_mem im_segs (mrestrict (w_H W) mem) (sptr_addr B ly p - 12) 4 (req_size n);
  (* the header, the block's first word and the block's shadow are present; the thread's stats words are present *)
  dv_pres : forall a, sptr_addr B ly p - 16 <= a < sptr_addr B ly p + 8 -> apresent (w_H W) mem a;
  dv_shpres : forall a, dshadow (sptr_addr B ly p) (req_size n) a -> apresent (w_H W) mem a;
  dv_junk : forall a, ly_T ly + t_stats + 24 <= a < ly_T ly + t_stats + 40 -> apresent (w_H W) mem a;
  (* where the block is *)
  dv_zone : dg_zone3 (sptr_addr B ly p - 16) (DGgiC.N8v (req_size n) + 16) /\ DGgiC.PSTATIC ly (sptr_addr B ly p) (req_size n) /\
            sptr_addr B ly p mod 16 = 0 /\ 1 <= req_size n <= 2 ^ 28;
  (* the thread's quarantine cache is within its bound *)
  dv_qb : 0 <= qc_bytes (st_qthread S) <= kQuarantineCacheMax;
  (* its last batch *)
  dv_batch : forall lastb initr, rev (qc_list (st_qthread S)) = lastb :: initr ->
             dbview W ly mem (st_qthread S) lastb (sptr_addr B ly p) (req_size n)
}.

(* The memory at Deallocate's return, arm "last batch has room" (DGge.at_RET with the depot's and the seed's
   frames composed), relative to the entry memory [mem0]: the depot zone is the depot's memory [memD] (with its post
   [DP]); outside the walk's windows, the depot zone, the internal allocator's zone and the block's shadow, nothing
   changed; the block's shadow is kAsanHeapFreeMagic (253); the written cells hold the values below. *)
Definition dwin_c (ly : alayout) (sp0 pa : Z) (lastb : batch) (a : Z) : Prop :=
(sp0 - DGbaseC.DFSTACK <= a < sp0) \/ DGgiC.WINT ly a \/ DGgiC.WINB ly pa lastb a.
Definition dmem_c (W : world im_segs) (ly : alayout) (sp0 : Z) (mem0 : word -> option byte) (pa nn hb1 : Z) (q : qcache)
(lastb : batch) (DP : (word -> option byte) -> Prop) (mem' : word -> option byte) : Prop :=
(exists memD, DP memD /\ (forall a, dg_dzone ly a -> apresent (w_H W) mem0 a -> apresent (w_H W) memD a) /\
 forall x : word, dg_dzone ly (bv_unsigned x) -> mem' x = memD x) /\
(forall x : word, ~ dwin_c ly sp0 pa lastb (bv_unsigned x) -> ~ dg_dzone ly (bv_unsigned x) -> ~ dg_izone (bv_unsigned x) ->
 ~ dshadow pa nn (bv_unsigned x) -> mem' x = mem0 x) /\
dg_ial_post W mem' /\
(forall x : word, dshadow pa nn (bv_unsigned x) -> mem' x = Some (Z_to_bv 8 253)) /\
(forall a, sp0 - DGbaseC.DFSTACK <= a < sp0 -> apresent (w_H W) mem' a) /\
(forall a, DGgiC.WINT ly a \/ DGgiC.WINB ly pa lastb a -> apresent (w_H W) mem' a) /\
val_mem im_segs (mrestrict (w_H W) mem') (pa - 16) 4 (3 + 256 * hb1) /\ val_mem im_segs (mrestrict (w_H W) mem') (pa - 12) 4 nn /\
val_mem im_segs (mrestrict (w_H W) mem') (ly_T ly + t_qc) 8 (DGgiC.QSv q) /\
val_mem im_segs (mrestrict (w_H W) mem') (ly_T ly + t_qc + 8) 8 (DGgiC.QFv ly q) /\
val_mem im_segs (mrestrict (w_H W) mem') (ly_T ly + t_qc + 16) 8 (DGgiC.Bv ly lastb) /\
val_mem im_segs (mrestrict (w_H W) mem') (ly_T ly + t_qc + 24) 8 (DGgiC.QBv q + nn) /\
val_mem im_segs (mrestrict (w_H W) mem') (ly_T ly + t_unwinding) 1 0 /\
val_mem im_segs (mrestrict (w_H W) mem') (DGgiC.Bv ly lastb + 8) 8 (DGgiC.BBv lastb + nn) /\
val_mem im_segs (mrestrict (w_H W) mem') (DGgiC.Bv ly lastb + 16) 8 (DGgiC.BCv lastb + 1) /\
val_mem im_segs (mrestrict (w_H W) mem') (DGgiC.SLOTv ly lastb) 8 (pa - 16).

(* The memory at Put's call of QuarantineCache::Enqueue (arms mid and drain: DGgf.at_ENQ with the depot's and the
   seed's frames composed), relative to the entry memory [mem0]. *)
Definition dwin_m (ly : alayout) (sp0 pa : Z) (a : Z) : Prop :=
(sp0 - DGbaseC.DFSTACK <= a < sp0) \/ DGgmC.WINT ly a \/ DGgmC.WINB pa a.
Definition dmem_m (W : world im_segs) (ly : alayout) (sp0 : Z) (mem0 : word -> option byte) (pa nn hb1 : Z)
(DP : (word -> option byte) -> Prop) (mem' : word -> option byte) : Prop :=
(exists memD, DP memD /\ (forall a, dg_dzone ly a -> apresent (w_H W) mem0 a -> apresent (w_H W) memD a) /\
 forall x : word, dg_dzone ly (bv_unsigned x) -> mem' x = memD x) /\
(forall x : word, ~ dwin_m ly sp0 pa (bv_unsigned x) -> ~ dg_dzone ly (bv_unsigned x) -> ~ dg_izone (bv_unsigned x) ->
 ~ dshadow pa nn (bv_unsigned x) -> mem' x = mem0 x) /\
dg_ial_post W mem' /\
(forall x : word, dshadow pa nn (bv_unsigned x) -> mem' x = Some (Z_to_bv 8 253)) /\
(forall a, sp0 - DGbaseC.DFSTACK <= a < sp0 -> apresent (w_H W) mem' a) /\
(forall a, DGgmC.WINT ly a \/ DGgmC.WINB pa a -> apresent (w_H W) mem' a) /\
val_mem im_segs (mrestrict (w_H W) mem') (pa - 16) 4 (3 + 256 * hb1) /\ val_mem im_segs (mrestrict (w_H W) mem') (pa - 12) 4 nn /\
val_mem im_segs (mrestrict (w_H W) mem') (ly_T ly + t_unwinding) 1 0.

(* The memory at Deallocate's early return (the NULL arm: DGh1.at_RETN), relative to the entry memory. *)
Definition dmem_n (W : world im_segs) (ly : alayout) (sp0 : Z) (mem0 mem' : word -> option byte) : Prop :=
(forall x : word, ~ (sp0 - DGbaseC.DFSTACK <= bv_unsigned x < sp0) -> ~ (ly_T ly + t_unwinding <= bv_unsigned x < ly_T ly + t_unwinding + 1) ->
 ~ dg_izone (bv_unsigned x) -> mem' x = mem0 x) /\
dg_ial_post W mem' /\
val_mem im_segs (mrestrict (w_H W) mem') (ly_T ly + t_unwinding) 1 0 /\
(forall a, sp0 - DGbaseC.DFSTACK <= a < sp0 -> apresent (w_H W) mem' a).

(* The addresses the walk writes outside its stack windows: the thread's quarantine / unwinding / stats cells, the
   chunk header, the block's first word, the depot zone and the block's shadow (all arms but NULL); the last batch's
   byte count, item count and slot (the arm whose last batch has room). *)
Definition dwrites (ly : alayout) (pa nn a : Z) : Prop :=
DGgiC.WINT ly a \/ (pa - 16 <= a < pa - 8) \/ (pa <= a < pa + 8) \/ dg_dzone ly a \/ dshadow pa nn a.
Definition bwrites (ly : alayout) (lastb : batch) (a : Z) : Prop :=
(DGgiC.Bv ly lastb + 8 <= a < DGgiC.Bv ly lastb + 24) \/ (DGgiC.SLOTv ly lastb <= a < DGgiC.SLOTv ly lastb + 8).

(* The walk's virtual register file regs0 (DGbase: atom 10 = the block's address, aINST = 11 = this, aBP = 12 = the
   trace buffer, aSO = 13 = the stack object): the actual entry registers with x10..x13 replaced. *)
Definition dregs (regs : bvmap 5 word) (pa inst bp so : Z) : bvmap 5 word :=
regupd (regupd (regupd (regupd regs 10%bv (w64 pa)) 11%bv (w64 inst)) 12%bv (w64 bp)) 13%bv (w64 so).
Lemma dregs_other : forall regs pa inst bp so (r : bv 5),
bv_unsigned r <> 10 -> bv_unsigned r <> 11 -> bv_unsigned r <> 12 -> bv_unsigned r <> 13 ->
getr (dregs regs pa inst bp so) r = getr regs r.
Proof.
intros regs pa inst bp so r H10 H11 H12 H13. unfold dregs.
rewrite getr_other by (intros ->; apply H13; reflexivity).
rewrite getr_other by (intros ->; apply H12; reflexivity).
rewrite getr_other by (intros ->; apply H11; reflexivity).
rewrite getr_other by (intros ->; apply H10; reflexivity). reflexivity.
Qed.
Lemma dregs_10 : forall regs pa inst bp so, getr (dregs regs pa inst bp so) 10%bv = w64 pa.
Proof.
intros. unfold dregs. do 3 (rewrite getr_other by (intros X; discriminate X)).
apply getr_same. intros X; discriminate X.
Qed.
Lemma dregs_11 : forall regs pa inst bp so, getr (dregs regs pa inst bp so) 11%bv = w64 inst.
Proof.
intros. unfold dregs. do 2 (rewrite getr_other by (intros X; discriminate X)).
apply getr_same. intros X; discriminate X.
Qed.
Lemma dregs_12 : forall regs pa inst bp so, getr (dregs regs pa inst bp so) 12%bv = w64 bp.
Proof.
intros. unfold dregs. rewrite getr_other by (intros X; discriminate X).
apply getr_same. intros X; discriminate X.
Qed.
Lemma dregs_13 : forall regs pa inst bp so, getr (dregs regs pa inst bp so) 13%bv = w64 so.
Proof. intros. unfold dregs. apply getr_same. intros X; discriminate X. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The interface.                                                                                                   *)
Section b.
Variable B : asyms.
(* The trace premise (DeallocG's): [U tr S] for the trace [tr] at the state [S] of the call. *)
Variable U : list Z -> astate -> Prop.
Variable ft : sptr -> list Z -> M unit.
Variable ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
(* The relation at the drain's DoRecycle cuts (DMiface: cgif ARX_cgif; the shared instance ARcf over WfR_cf). *)
Variable ARXr : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable lpost : astate -> Prop.
Variable fpre : alayout -> astate -> world im_segs -> (word -> option byte) -> sptr -> Z -> Prop.
(* The post of the depot call: [dpost inst ly S W tr z mem'] after StackDepotPut(tr) answered [z] from the
   allocator at [inst, ly, S, W] (AGif0n's). *)
Variable dpost : Z -> alayout -> astate -> world im_segs -> list Z -> Z -> (word -> option byte) -> Prop.
(* The drain tree (run as [dbody X X]) and the class-24 batch bound of the drain contract (DMspec). *)
Variable dbody : astate -> M unit.
Variable L24 : Z.
(* The drain entry's byte premise (DMspec / DMiface: cgif qloose; the shared instance its cf bounds). *)
Variable QB : astate -> Prop.
(* The instance's recycle invariant (DMiface): [DRq S its zs] with the chunks [its] and the batch objects [zs] still
   to recycle (cgif: YG03.RIx (as_universe B) 0 0 0 S its [] zs). *)
Variable DRq : astate -> list chunk -> list Z -> Prop.
(* The memory predicate at Put's call of Enqueue (di_enqueue's premise).  The walks take it at Deallocate's entry
   memory and carry it to the call by their keep law over dmem_m's frame (DGfz / DGg2: MP_keep).  cgif: fun _ => True;
   cf: memnorm /\ arodata_ok_cf (MP_keep_cf). *)
Variable MP : (word -> option byte) -> Prop.

Record DIface : Prop := {
  di_inst : forall inst ly S W mem md, ARX inst ly S W mem md -> dg_inst_ok inst;
  (* (view) *)
  di_view_n : forall inst ly S W mem md n, ARX inst ly S W mem md -> rpre S n -> dview_n B W ly inst mem;
  di_view : forall inst ly S W mem md p n, ARX inst ly S W mem md -> rpre S n -> fpre ly S W mem p n -> In (p, n) (blocks S) ->
    dview B W ly inst mem S p n;
  (* (shape) *)
  di_shape_n : forall n tr S, rpre S n -> ft PNull tr S = ret tt (dtick S);
  di_shape : forall p n tr S k, p <> PNull -> rpre S n -> In (p, n) (blocks S) -> find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
    ft p tr S = (depot_put tr ;; modify (fun s => set_chunks (upd_chunk (st_chunks s) (qk k)) s) ;; enqueue (qk k) ;; dmd dbody) (dtick S);
  (* the depot callee (QuarantineChunk's call), entered with the depot zone and the constant cells outside the
     internal allocator's zone as at [mem0] *)
  di_depot : forall inst ly S W mem0 md0 tr (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (buf : Z),
    ARX inst ly S W mem0 md0 -> U tr S ->
    (forall x : word, dg_dzone ly (bv_unsigned x) \/ (dg_czone ly (bv_unsigned x) /\ ~ dg_izone (bv_unsigned x)) -> mem x = mem0 x) ->
    getr regs 10 = Z_to_bv 64 buf -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
    getr regs 3 = Z_to_bv 64 (as_gp B) -> getr regs 4 = Z_to_bv 64 im_tp -> YK0s.ret_ok (getr regs 1) ->
    (forall i, (i < length tr)%nat -> val_mem im_segs (mrestrict (w_H W) mem) (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
    buf mod 8 = 0 -> ly_stk_lo ly <= buf -> buf + 8 * 30 <= ly_stk_hi ly ->
    buf + 8 * 30 <= bv_unsigned (getr regs 2) - YFl0C.DEP_STK \/ bv_unsigned (getr regs 2) <= buf ->
    bv_unsigned (getr regs 2) mod 16 = 0 -> ly_stk_lo ly <= bv_unsigned (getr regs 2) - YFl0C.DEP_STK ->
    bv_unsigned (getr regs 2) <= ly_stk_hi ly ->
    (forall a, bv_unsigned (getr regs 2) - YFl0C.DEP_STK <= a < bv_unsigned (getr regs 2) -> apresent (w_H W) mem a) ->
    SRr im_segs W (mkCfg (mkst regs (Z_to_bv 64 dg_depot) mem (seg_rom im_segs)) md)
    (fun W' c' => W' = W /\ exists z regs' mem' mat,
      c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom im_segs)) (with_vm_backing (m_vm_lazy md) mat md) /\
      regs_preserved regs regs' /\
      (forall x : word, ~ (bv_unsigned (getr regs 2) - YFl0C.DEP_STK <= bv_unsigned x < bv_unsigned (getr regs 2)) ->
         ~ dg_dzone ly (bv_unsigned x) -> mem' x = mem x) /\
      (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
      dpost inst ly S W tr z mem');
  di_dpost_aok : forall inst ly S W tr z m, dpost inst ly S W tr z m -> aok S (KDepot tr) z;
  (* QuarantineCache::Enqueue at Put's call (sp = Deallocate's entry sp - 80), arms mid and drain: from the entry
     state, the depot's answer [z] and the memory at the call, at which MP holds; the post is over ARX of the enqueued
     state, whose owned set is the quarantined state's, and gives lpost when no drain follows *)
  di_enqueue : forall inst ly S W mem0 md0 p n tr k z hb1 sp0 (regs : bvmap 5 word) (mem : word -> option byte) mat,
    ARX inst ly S W mem0 md0 -> rpre S n -> fpre ly S W mem0 p n -> In (p, n) (blocks S) -> U tr S ->
    find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
    ly_stk_lo ly + DGbaseC.DFSTACK <= sp0 -> sp0 <= ly_stk_hi ly -> ly_bot ly < sp0 -> sp0 mod 16 = 0 ->
    0 <= hb1 < 256 -> val_mem im_segs (mrestrict (w_H W) mem0) (sptr_addr B ly p - 16) 4 (2 + 256 * hb1) ->
    dmem_m W ly sp0 mem0 (sptr_addr B ly p) (req_size n) hb1 (dpost inst ly S W tr z) mem ->
    MP mem ->
    YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs -> spZ regs = sp0 - 80 ->
    getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
    getr regs 10 = w64 (ly_T ly + t_qc) -> getr regs 11 = w64 (ly_T ly + t_cache) ->
    getr regs 13 = w64 (sptr_addr B ly p - kChunkHeaderSize) -> getr regs 14 = w64 (req_size n) ->
    amreal im_segs (enqueue (qk k) (qx S k z tr)) W
      (cfg_at im_segs dg_enqueue regs mem (with_vm_backing (m_vm_lazy md0) mat md0))
      (fun r W' c' => exists regs' mem' md' nb,
        c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
        acall_post_x B ARX AOX inst YFewC.QSTACK ly (qx S k z tr) W regs mem (with_vm_backing (m_vm_lazy md0) mat md0) (fun _ => False)
          ly (snd r) W' regs' mem' md' /\
        st_qthread (snd r) = qc_push (st_qthread (qx S k z tr)) (qk k) nb /\
        match nb with None => need_new_batch (st_qthread (qx S k z tr)) = false | Some _ => need_new_batch (st_qthread (qx S k z tr)) = true end /\
        st_chunks (snd r) = st_chunks (qx S k z tr) /\ st_qglobal (snd r) = st_qglobal (qx S k z tr) /\
        (forall a, AOX ly (snd r) a -> AOX ly (qx S k z tr) a) /\
        (* the thread cache's byte count, which Put reads after Enqueue returns *)
        val_mem im_segs (mrestrict (w_H W') mem') (ly_T ly + t_qc + 24) 8 (qc_bytes (st_qthread (snd r))) /\
        (qc_bytes (st_qthread (snd r)) <= kQuarantineCacheMax -> lpost (snd r)) /\
        (kQuarantineCacheMax < qc_bytes (st_qthread (snd r)) -> QB (snd r) /\ Z.of_nat (length (all_batches (snd r))) <= L24));
  (* Quarantine::Drain at Put's call (a0 = inst + o_quar), arm drain: DMspec's contract *)
  di_drain : drain_spec_cf B ARX AOX dbody L24 QB;
  (* lpost at the end of a granted path of the drain tree from the enqueued state [X'] (ARX at X': the drain
     tree's lpost needs the state's well-formedness) *)
  di_lpost_d : forall inst ly S W mem md p n tr k z nb X' (W' : world im_segs) (mem' : word -> option byte) (md' : Model) trc r,
    ARX inst ly S W mem md -> rpre S n -> In (p, n) (blocks S) -> U tr S ->
    find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
    st_qthread X' = qc_push (st_qthread (qx S k z tr)) (qk k) nb ->
    match nb with None => need_new_batch (st_qthread (qx S k z tr)) = false | Some _ => need_new_batch (st_qthread (qx S k z tr)) = true end ->
    st_chunks X' = st_chunks (qx S k z tr) -> st_qglobal X' = st_qglobal (qx S k z tr) ->
    ARX inst ly X' W' mem' md' ->
    kQuarantineCacheMax < qc_bytes (st_qthread X') ->
    apath (dbody X' X') trc r -> gflag trc = true -> lpost (snd r);
  (* the real-merge drain's reads of the machine (DMiface; h-verbs-5's DMdrain consumes them) *)
  di_qview : di_qview_t B ARX L24 QB;
  di_qowned : di_qowned_t ARX AOX L24 QB;
  di_requar_x : di_requar_x_t B ARX AOX L24 QB;
  di_requar_r : di_requar_r_t B ARX ARXr AOX L24 QB DRq;
  di_requar_e : di_requar_e_t ARX ARXr DRq;
  di_rchunk : di_rchunk_t B ARXr AOX DRq;
  di_cdealloc : di_cdealloc_t B ARXr AOX DRq;
  di_frame_r : di_frame_t ARXr AOX;
  di_rview : di_rview_t B ARXr DRq;
  (* (post) the arm whose last batch has room: the memory at Deallocate's return gives ARX and lpost of the final
     state *)
  di_post_c : forall inst ly S W mem0 md0 p n tr k lastb initr hb1 z sp0 mem' mat,
    ARX inst ly S W mem0 md0 -> rpre S n -> fpre ly S W mem0 p n -> In (p, n) (blocks S) -> U tr S ->
    find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
    rev (qc_list (st_qthread S)) = lastb :: initr -> Z.of_nat (length (b_items lastb)) < kBatchSlots ->
    qc_bytes (st_qthread S) + req_size n <= kQuarantineCacheMax ->
    ly_stk_lo ly + DGbaseC.DFSTACK <= sp0 -> sp0 <= ly_stk_hi ly -> ly_bot ly < sp0 -> sp0 mod 16 = 0 ->
    0 <= hb1 < 256 -> val_mem im_segs (mrestrict (w_H W) mem0) (sptr_addr B ly p - 16) 4 (2 + 256 * hb1) ->
    dmem_c W ly sp0 mem0 (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) lastb (dpost inst ly S W tr z) mem' ->
    (exists trc, apath (ft p tr S) trc (tt, qfin_c S k z tr) /\ gflag trc = true) ->
    ARX inst ly (qfin_c S k z tr) W mem' (with_vm_backing (m_vm_lazy md0) mat md0) /\ lpost (qfin_c S k z tr);
  (* (post) the NULL arm *)
  di_post_n : forall inst ly S W mem0 md0 n tr sp0 mem' mat,
    ARX inst ly S W mem0 md0 -> rpre S n -> fpre ly S W mem0 PNull n -> U tr S ->
    ly_stk_lo ly + DGbaseC.DFSTACK <= sp0 -> sp0 <= ly_stk_hi ly -> ly_bot ly < sp0 -> sp0 mod 16 = 0 ->
    dmem_n W ly sp0 mem0 mem' ->
    (exists trc, apath (ft PNull tr S) trc (tt, dtick S) /\ gflag trc = true) ->
    ARX inst ly (dtick S) W mem' (with_vm_backing (m_vm_lazy md0) mat md0) /\ lpost (dtick S);
  (* (laws) *)
  di_frame : di_frame_t ARX AOX;
  di_stack : di_stack_t ARX AOX;
  (* (owned) *)
  di_owned : forall inst ly S W mem md p n k a,
    ARX inst ly S W mem md -> rpre S n -> In (p, n) (blocks S) -> find_user (st_chunks S) p = Some k ->
    0 <= a < 2 ^ 64 -> dwrites ly (sptr_addr B ly p) (req_size n) a ->
    AOX ly S a \/ (sptr_addr B ly p <= a < sptr_addr B ly p + req_size n);
  di_owned_b : forall inst ly S W mem md lastb initr a,
    ARX inst ly S W mem md -> rev (qc_list (st_qthread S)) = lastb :: initr -> 0 <= a < 2 ^ 64 -> bwrites ly lastb a -> AOX ly S a;
  di_owned_i : forall inst ly S W mem md a, ARX inst ly S W mem md -> dg_izone a -> AOX ly S a;
  di_owned_x : forall inst ly S W mem md p n k z tr a,
    ARX inst ly S W mem md -> rpre S n -> In (p, n) (blocks S) -> find_user (st_chunks S) p = Some k ->
    AOX ly (qx S k z tr) a -> AOX ly S a \/ (sptr_addr B ly p <= a < sptr_addr B ly p + req_size n)
}.
End b.
End a.
