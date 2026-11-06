(* copied from proofs/cgif/cgif_file_fuzzer/lib/DMiface.v @ 86aa4177b94 (c-asan, cold/c-asan-nmax-param: F1 / F2 + NMAX-PARAM + EV_MAX value-independence; installs in c5 ~18:30Z), module paths changed only. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* The names the real-merge drain proof (DMdrain.v) reads the allocator relation by.

   The drain proof is over an opaque allocator relation [ARX inst] and owned set [AOX] (DMspec.v), and over
   [ARXr inst], the relation at DoRecycle's cuts (between Recycle's call of DoRecycle and its return; cgif: ARX_cgif;
   the shared instance: ARcf over WfR_cf, without Compl0, which a cut with batches still to free breaks).  It reads
   the machine through them only by the facts below; they are fields of DeallocG's DIface (DGif0.v: di_qview,
   di_qowned, di_stack, di_frame (and its ARXr form, di_frame_t ARXr AOX), di_requar_x, di_requar_r, di_requar_e,
   di_rchunk, di_cdealloc; field list kept by lane h-verbs-5).

   - [qview]: the quarantine as the machine holds it at Drain's entry, in cgif's cell vocabulary (YG0n.quar_cells:
     the two mutex bytes, the thread cache's and the global cache's headers and batch cells), with the batch objects'
     geometry and the quarantine's well-formedness;
   - [dmem_q]: the memory at a cut of the drain (Drain's return after the transfer, or Recycle's call of DoRecycle)
     relative to the entry memory: outside the stack window, the quarantine's header words and the batch cells, nothing
     changed; the quarantine cells of the cut state hold; presence is kept off the header words;
   - [drain_xfer], [drain_recyc]: the model state at those cuts, computed from the entry state as drain_body_cf does;
   - [rcc_pre_x], [cd_pre_x]: QuarantineCallback::Recycle's and CacheDealloc's call pre over ARX (YFeu.rcc_pre /
     cd_pre with ARX for AR, without the model conjuncts, which the instance's recycle invariant [DRq] gives);
   - [DRq S its zs]: the instance's recycle invariant at state S with the chunks [its] and the batch objects [zs] (their
     offsets in the space) still to recycle (cgif: YG03.RIx U 0 0 0 S its [] zs).

   The file is image-free: the binary's segments, TSD slot and image window and the entry pcs of Recycle and
   CacheDealloc are the fields of ImgBase.AImg and ImgBaseDG.DImg ([Context {IM : AImg} {DI : DImg}]; cgif_file's
   instances AGif2cgif.AImg_cgif and DGif0cgif.DImg_cgif); transfer_g, DSTACK, plist_cells and puser are
   ImgBaseDG's copies of YFeu's. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/Reusable/DMiface.v, derived mechanically (bkit derive_b.py): its Require lines name the lib/B copies; nothing else differs. The comments are the A file's. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK0i YP0m YP0e YP09 YP0l YP06 YO0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG06 YG03.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YGcfNames YG00cf DMspec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import ImgBase ImgBaseDG.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {IM : AImg} {DI : DImg}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Model-level names.                                                                                               *)

(* The cut after the transfer, when the drain returns without recycling. *)
Definition drain_xfer (X S' : astate) : Prop :=
qc_bytes (YFeuC.transfer_g X) <= kQuarantineMax /\ S' = set_qglobal (YFeuC.transfer_g X) (set_qthread qc0 X).
(* The cut at Recycle's call of DoRecycle: the kept global cache [g'] and the temp list [P] = the extracted batches
   then the dequeued ones (drain_body_cf's recycle_body_cf). *)
Definition drain_recyc (X S' : astate) (P : list batch) : Prop :=
kQuarantineMax < qc_bytes (YFeuC.transfer_g X) /\
exists gm ex g' popped,
merge_split_cf (YFeuC.transfer_g X) = (gm, ex) /\ pop_batches (S (length (qc_list gm))) gm [] = (g', popped) /\
S' = set_qglobal g' (set_qthread qc0 X) /\ P = ex ++ popped.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Machine-level names.                                                                                             *)

(* The batch object of [b]: its 8192 bytes in the space. *)
Definition bobj (ly : alayout) (b : batch) (a : Z) : Prop :=
ly_space ly + b_self b <= a < ly_space ly + b_self b + kBatchBytes.
(* The quarantine's words outside the batch objects: the mutex word (inst + o_quar + 152 .. 156) and the global
   header (+ 160 .. 192), the thread cache's header (T + t_qc .. + 32). Bytes + 156 .. 160 are outside it: cgif's ARm
   keeps const cells there (YF0m.v:211-212; h-w6-2 03:14Z), as the released window YFgj.WINF does. *)
Definition qhdr (inst : Z) (ly : alayout) (a : Z) : Prop :=
(inst + o_quar + 152 <= a < inst + o_quar + 156) \/ (inst + o_quar + 160 <= a < inst + o_quar + 192) \/
(ly_T ly + t_qc <= a < ly_T ly + t_qc + 32).

(* (view) The quarantine at Drain's entry. *)
Record qview (B : asyms) (W : world im_segs) (ly : alayout) (inst : Z) (X : astate) (mem : word -> option byte) : Prop := {
  qv_inst : inst = as_inst B;
  qv_ly : layout_ok ly;
  qv_img : im_img_cover ly;
  qv_tsd : ly_tsd ly = im_tsd;
  (* the mutex bytes, both caches' headers and batch cells *)
  qv_cells : Forall (cell_holds B ly (aview im_segs (w_H W) mem)) (quar_cells X);
  (* the Quarantine object's constants (max_size_, min_size_) and the two bytes after the mutexes *)
  qv_const : val_mem im_segs (mrestrict (w_H W) mem) (inst + o_q_max) 8 kQuarantineMax /\
             val_mem im_segs (mrestrict (w_H W) mem) (inst + o_q_min) 8 kQuarantineMin /\
             val_mem im_segs (mrestrict (w_H W) mem) (inst + o_q_cmutex + 2) 2 0;
  (* the thread cache's header (high memory) and the batch objects are present; the instance-side header in the image's
     .bss (inst + o_quar + 152 .. 192) needs no presence: the walks store there by the image's writability (rw_writable,
     as DMdeq.v and the released YFev.v:237 do) *)
  qv_hpres : forall a, ly_T ly + t_qc <= a < ly_T ly + t_qc + 32 -> apresent (w_H W) mem a;
  qv_bpres : forall b a, In b (all_batches X) -> bobj ly b a -> apresent (w_H W) mem a;
  (* every batch object is a class-kBatchClass object of the region's allocated part *)
  qv_geom : rg_alloc_user (reg X kBatchClass) <= kFreeArrayOffset /\
            forall b, In b (all_batches X) ->
            0 <= b_self b - region_off kBatchClass /\ b_self b - region_off kBatchClass + kBatchBytes <= rg_alloc_user (reg X kBatchClass) /\
            (b_self b - region_off kBatchClass) mod kBatchBytes = 0;
  qv_nodup : NoDup (map b_self (all_batches X));
  (* the quarantine's well-formedness: byte counts are the batches' sums, every batch holds 1 .. kBatchSlots
     chunks, chunk sizes are not negative *)
  qv_wf : qc_bytes (st_qthread X) = sum_bytes (qc_list (st_qthread X)) /\
          qc_bytes (st_qglobal X) = sum_bytes (qc_list (st_qglobal X)) /\
          Forall (fun b => (1 <= length (b_items b) <= Z.to_nat kBatchSlots)%nat) (all_batches X) /\
          Forall (fun k => 0 <= ck_n k) (q_items X);
  (* the drain's byte arithmetic: both caches together hold at most 2^31 bytes (cgif: qloose; the shared
     instance: its thread bound plus the global cache's kQuarantineMax) *)
  qv_bytes : qc_bytes (st_qthread X) + qc_bytes (st_qglobal X) <= 2 ^ 31;
  qv_inited : st_cache_inited X = true
}.

(* The batch cells' words of the batches [l]: next, size, count and the live slots. *)
Definition bcellw (ly : alayout) (l : list batch) (a : Z) : Prop :=
exists b, In b l /\ ly_space ly + b_self b <= a < ly_space ly + b_self b + 24 + 8 * Z.of_nat (length (b_items b)).
(* The words a drain cut may have changed: the stack window below Drain's entry sp [sp0], the quarantine headers,
   the batch cells of the entry state's, the cut state's and the temp list's batches. *)
Definition dwin_q (inst : Z) (ly : alayout) (sp0 : Z) (X S' : astate) (P : list batch) (a : Z) : Prop :=
(sp0 - YFeuC.DSTACK <= a < sp0) \/ qhdr inst ly a \/ bcellw ly (all_batches X ++ all_batches S' ++ P) a.
(* The memory [mem'] at a drain cut, relative to the entry memory [mem]; the two bytes after the mutex word stay 0
   (the released at_RETD / at_L0, YFgj.v:302 / :317). *)
Definition dmem_q (B : asyms) (W : world im_segs) (inst : Z) (ly : alayout) (sp0 : Z) (X S' : astate) (P : list batch)
(mem mem' : word -> option byte) : Prop :=
(forall x : word, ~ dwin_q inst ly sp0 X S' P (bv_unsigned x) -> mem' x = mem x) /\
Forall (cell_holds B ly (aview im_segs (w_H W) mem')) (quar_cells S') /\
(* presence is kept off the quarantine's header words; those are in the image's RW segment, where the drain's
   segment frames report no presence, and their visibility after the cut comes from [quar_cells S'] *)
(forall a, ~ qhdr inst ly a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
val_mem im_segs (mrestrict (w_H W) mem') (inst + o_q_cmutex + 2) 2 0.

(* Stack window of the shared instance's QuarantineCallback::Recycle and CacheDealloc calls: the free-array growth arm
   reaches EnsureFreeArraySpace 240 bytes below CacheDealloc's entry sp (frames 48 + 64 + 128: 0x339a0, 0x33d34,
   ReturnToAllocator 0x33ed8), and FGt.efa_pre (FGt.v:56-79) asks 1024 more, so >= 1264; YFeu's KSTACK = 512
   (YFeu.v:235) is too small. *)
Definition KSTACK_CF : Z := 2048.

(* QuarantineCallback::Recycle's call (YFeu.rcc_pre with ARX inst for AR, without its three model conjuncts). *)
Definition rcc_pre_x (B : asyms) (ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop)
(inst : Z) (ly : alayout) (X : astate) (k : chunk) (cbp : Z) (W : world im_segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) : Prop :=
ARX inst ly X W mem md /\ st_cache_inited X = true /\
YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + KSTACK_CF <= spZ regs /\ spZ regs <= cbp /\ cbp + 16 <= ly_stk_hi ly /\ cbp mod 8 = 0 /\
(forall a, spZ regs - KSTACK_CF <= a < spZ regs -> apresent (w_H W) mem a) /\ (forall a, cbp <= a < cbp + 16 -> apresent (w_H W) mem a) /\
val_mem im_segs (mrestrict (w_H W) mem) cbp 8 (ly_T ly + t_cache) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 10 = w64 cbp /\ getr regs 11 = w64 (ck_base B ly k + ck_rz k - kChunkHeaderSize).
(* CacheDealloc's call for a batch object at offset [z] of the space (YFeu.cd_pre with ARX inst for AR, class
   kBatchClass, a1 = inst, without its model conjuncts). *)
Definition cd_pre_x (B : asyms) (ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop)
(inst : Z) (ly : alayout) (X : astate) (z : Z) (W : world im_segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) : Prop :=
ARX inst ly X W mem md /\ st_cache_inited X = true /\
YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + KSTACK_CF <= spZ regs /\ spZ regs <= ly_stk_hi ly /\
(forall a, spZ regs - KSTACK_CF <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 10 = w64 (ly_T ly + t_cache) /\ getr regs 11 = w64 inst /\ getr regs 12 = w64 kBatchClass /\
getr regs 13 = w64 (ly_space ly + z).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The facts' types; DGif0.DIface holds them as fields with these names.                                           *)
Section iface.
Variable B : asyms.
Variable ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
(* the relation at DoRecycle's cuts *)
Variable ARXr : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable L24 : Z.
Variable QB : astate -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.

(* The drain's premises on the model state (DMspec.drain_pre_cf's model part). *)
Definition dprem (X : astate) : Prop :=
kQuarantineCacheMax < qc_bytes (st_qthread X) /\ QB X /\ Z.of_nat (length (all_batches X)) <= L24.

Definition di_qview_t : Prop :=
forall inst ly X W mem md, ARX inst ly X W mem md -> dprem X -> qview B W ly inst X mem.

Definition di_qowned_t : Prop :=
forall inst ly X W mem md a, ARX inst ly X W mem md -> dprem X -> 0 <= a < 2 ^ 64 ->
qhdr inst ly a \/ (exists b, In b (all_batches X) /\ bobj ly b a) -> AOX ly X a.

Definition di_stack_t : Prop :=
forall inst ly S W mem md a, ARX inst ly S W mem md -> ly_stk_lo ly <= a < ly_stk_hi ly -> ~ AOX ly S a.

Definition di_frame_t : Prop :=
forall inst ly S W mem md mem' md',
ARX inst ly S W mem md ->
(forall a, 0 <= a < 2 ^ 64 -> AOX ly S a -> aview im_segs (w_H W) mem' a = aview im_segs (w_H W) mem a) ->
(forall a, aview im_segs (w_H W) mem a <> None -> aview im_segs (w_H W) mem' a <> None) ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
(forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
ARX inst ly S W mem' md'.

(* ARX after the transfer (Drain returns without recycling). *)
Definition di_requar_x_t : Prop :=
forall inst ly X W mem md sp0 S' mem' md',
ARX inst ly X W mem md -> dprem X -> drain_xfer X S' ->
ly_stk_lo ly + YFeuC.DSTACK <= sp0 -> sp0 <= ly_stk_hi ly ->
dmem_q B W inst ly sp0 X S' [] mem mem' ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
ARX inst ly S' W mem' md' /\ (forall a, AOX ly S' a -> AOX ly X a).

(* ARXr and the recycle invariant at Recycle's call of DoRecycle, the temp list [P] at [tmp] (Recycle's sp). *)
Definition di_requar_r_t : Prop :=
forall inst ly X W mem md sp0 tmp S' P mem' md',
ARX inst ly X W mem md -> dprem X -> drain_recyc X S' P ->
ly_stk_lo ly + YFeuC.DSTACK <= sp0 -> sp0 <= ly_stk_hi ly -> sp0 - YFeuC.DSTACK <= tmp -> tmp + 32 <= sp0 ->
dmem_q B W inst ly sp0 X S' P mem mem' ->
Forall (cell_holds B ly (aview im_segs (w_H W) mem')) (YFeuC.plist_cells tmp P) ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
ARXr inst ly S' W mem' md' /\ DRq S' (flat_map b_items P) (map b_self P) /\ (forall a, AOX ly S' a -> AOX ly X a).

(* ARX again when DoRecycle has recycled everything. *)
Definition di_requar_e_t : Prop :=
forall inst ly S W mem md, ARXr inst ly S W mem md -> DRq S [] [] -> ARX inst ly S W mem md.

(* QuarantineCallback::Recycle (0x3359c) over ARXr, with the recycle invariant. *)
Definition di_rchunk_t : Prop :=
forall inst ly X k ks zs cbp W regs mem md,
rcc_pre_x B ARXr inst ly X k cbp W regs mem md -> DRq X (k :: ks) zs ->
amreal im_segs (recycle_chunk k X) W (cfg_at im_segs dg_rchunk regs mem md)
(fun r W' c' => exists regs' mem' md',
  c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
  acall_post_x B ARXr AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  (forall a, 0 <= a < 2 ^ 64 -> YFeuC.puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) ->
   aview im_segs (w_H W') mem' a = aview im_segs (w_H W) mem a) /\
  (forall a, YFeuC.puser ly X a -> YFeuC.puser ly (snd r) a) /\
  DRq (snd r) ks zs /\ st_cache_inited (snd r) = true /\ (forall a, AOX ly (snd r) a -> AOX ly X a)).

(* CacheDealloc (0x339a0) of a batch object over ARXr, with the recycle invariant: [its] are the chunks of the
   later batches, still to recycle. *)
Definition di_cdealloc_t : Prop :=
forall inst ly X its z zs W regs mem md,
cd_pre_x B ARXr inst ly X z W regs mem md -> DRq X its (z :: zs) ->
amreal im_segs (cache_dealloc kBatchClass z X) W (cfg_at im_segs dg_cdealloc regs mem md)
(fun r W' c' => exists regs' mem' md',
  c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
  acall_post_x B ARXr AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  (forall a, 0 <= a < 2 ^ 64 -> YFeuC.puser ly X a -> aview im_segs (w_H W') mem' a = aview im_segs (w_H W) mem a) /\
  (forall a, YFeuC.puser ly X a -> YFeuC.puser ly (snd r) a) /\
  DRq (snd r) its zs /\ st_cache_inited (snd r) = true /\ (forall a, AOX ly (snd r) a -> AOX ly X a)).

(* What DoRecycle reads at every cut (released YFhd / YFhg / YFhl read it from AR's ARm; ARXr and DRq are opaque):
   the space-base word at inst + o_space (read at 0x33534 for the primary / secondary test before CacheDealloc), the
   header range of every chunk still to recycle, and the carved class-24 position of every batch object still to
   free, apart from every chunk still to recycle (di_rchunk's frame is "puser minus chunk k"). *)
Definition di_rview_t : Prop :=
forall inst ly X W mem md its zs, ARXr inst ly X W mem md -> DRq X its zs ->
val_mem im_segs (mrestrict (w_H W) mem) (inst + o_space) 8 (ly_space ly) /\
(forall k, In k its -> aeval B ly (sptr_exp (ck_hdr k)) = ck_base B ly k + ck_rz k - kChunkHeaderSize /\
  4096 <= ck_base B ly k + ck_rz k - kChunkHeaderSize /\ ck_base B ly k + ck_rz k - kChunkHeaderSize + 16 <= ASAN_CEIL /\
  (ck_base B ly k + ck_rz k - kChunkHeaderSize) mod 16 = 0) /\
(forall z, In z zs -> 0 <= z - region_off kBatchClass /\ z - region_off kBatchClass + kBatchBytes <= rg_alloc_user (reg X kBatchClass) /\
  (z - region_off kBatchClass) mod kBatchBytes = 0 /\
  forall k a, In k its -> ly_space ly + z <= a < ly_space ly + z + kBatchBytes -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k)).

End iface.
End d.
