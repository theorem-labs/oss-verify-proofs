(* Modified by a Theorem Labs lane (ReallocPrimary.RealSegA), 2026-10-30: carried BY PATH from commit a3d076d83cd2 (lane F2a's Deallocate instance stack, a working branch), proofs/cgif/cgif_file_fuzzer/lib/DGbigIF.v, sha256 65c8d35def001688. The only change is the module paths: OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib M -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable M, except lib.A for: DMspec DMiface DeallocG ImgBase ImgBaseDG DGif0. No numeral and no statement changed. *)
(* Modified by Theorem Labs, 2026-10: then from plugin-hostd/fuzz_reply lib/A (commit 29bcc0b4b8f) to image B (fuzz_reply.asan-ubsan, pin 10ffb5f9202a, unstripped twin 3389287e1d61) by alreloc 56664a20986eb62e, same unit A -> B. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10 (a Theorem Labs lane, DeallocNmaxA): the interface of Allocator::Deallocate's BIG-BLOCK arm, an additive
   companion of DGif0.DIface (DGif0.v is not edited).

   Quarantine::Put enqueues a chunk only when its user size is at most the quarantine's max_size (the cell
   inst + 0x318 = kQuarantineMax; compiler-rt llvmorg-20.1.8 sanitizer_quarantine.h:96-108; cgif 0x356e8
   `bgeu max_size, size`). Above it, RecyclePassThrough (asan_allocator.cpp:255-263) frees the chunk at once:
   FromPrimary's test on the space base (the instance's primary.space cell, an image constant cell: cgif YF0m.v:26
   `c8 (AInst o_space) (ASp 0)`), FillChunk (vacuous: flags()->max_free_fill_size = 0), then
   QuarantineCallback::Recycle (cgif 0x35764 -> 0x335f4), then Put's cache-size test, which finds the thread cache
   as it was (no drain), and the returns of Put and Deallocate. The model is YG00cf.free_cf's recycle side:
   depot_put, the change to CQuarantined, recycle_chunk, then the thread-cache test [dmd dbody].
   Evidence: the Theorem Labs lane's frame note BIG-ARM.md (sha256 799db2a78636; internal record).

   DIface cannot serve this arm: its di_shape states the enqueue tree, and di_view's dv_zone bounds the block by
   2 ^ 28. So DIfaceBig restates the fields the arm reads, at the arm's own premise (rpre carries the size guard
   kQuarantineMax < req_size n at the cf instance, CfF2a's rpre_big), and adds the three that are new:
   - [dbg_shape]: the free tree's recycle side;
   - [dbg_rq]: the cut relation ARXr and the recycle invariant DRq for the one chunk at Recycle's call, from the
     memory at Put's size test ([dmem_b]: dmem_m without the shadow poison, which only the enqueue side writes);
   - [dbg_rcs]: QuarantineCallback::Recycle on that chunk, which is above kQuarantineMax and so secondary (a primary
     chunk's extent is at most kMaxSize < kQuarantineMax). Its call premise is DMiface.rcc_pre_sec, rcc_pre_x without
     `st_cache_inited X = true`, and its post does not state the flag. The general contract MnRecycle.de_rchunk_m_t
     cannot serve: it needs the flag, and the flag is false at a reachable big-arm state (a first malloc above
     kQuarantineMax goes through sec_alloc, which does not run init_cache_if_needed; CfF2a's measurement,
     YGcfInstFreeMid.v:82 ms_cinit). Recycle's secondary path does not read the flag (H4's measurement).
   The block's size bound is the cf kit's: req_size n + 15 <= 2 ^ 30 (YG08cf.cf_malloc_max_bound with
   n < cf_malloc_max).
   cgif's instance is vacuous (DGbigcgif.v): cgif's blocks and chunks are below MALLOC_MAX = 2 ^ 28.
   Nothing here is a function's proof (rule 24). No address. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseDG DGif0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import DIfaceR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ErrnoG MemnormT YGcfRehidePost.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0dH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {IM : AImg} {DI : DImg}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The view of a big block (dview with the arm's size bound, the chunk's geometry, and no shadow or last-batch cells). *)
Record dview_big (B : asyms) (W : world im_segs) (ly : alayout) (inst : Z) (mem : word -> option byte) (S : astate)
(p : sptr) (n : Z) : Prop := {
  dvb_n : dview_n B W ly inst mem;
  dvb_nonnull : p <> PNull;
  dvb_chunk : exists k, find_user (st_chunks S) p = Some k /\ ck_state k = CAllocated /\ ck_user k = p /\ ck_req k = n /\
              ck_base B ly k + ck_rz k = sptr_addr B ly p;
  (* the chunk header: chunk_state CHUNK_ALLOCATED (2), the second byte [hb1], the user size *)
  dvb_hdr : exists hb1, 0 <= hb1 < 256 /\ Z.land hb1 127 = 17 /\
            val_mem im_segs (mrestrict (w_H W) mem) (sptr_addr B ly p - 16) 4 (2 + 256 * hb1) /\
            val_mem im_segs (mrestrict (w_H W) mem) (sptr_addr B ly p - 12) 4 (req_size n);
  dvb_pres : forall a, sptr_addr B ly p - 16 <= a < sptr_addr B ly p + 8 -> apresent (w_H W) mem a;
  dvb_junk : forall a, ly_T ly + t_stats + 24 <= a < ly_T ly + t_stats + 40 -> apresent (w_H W) mem a;
  (* where the block is: the zone, the static extents it avoids, the alignment, the arm's size range *)
  dvb_zone : dg_zone3 (sptr_addr B ly p - 16) (DGgiC.N8v (req_size n) + 16) /\ DGgiC.PSTATIC ly (sptr_addr B ly p) (req_size n) /\
             sptr_addr B ly p mod 16 = 0 /\ kQuarantineMax < req_size n /\ req_size n + 15 <= 2 ^ 30;
  (* the thread's quarantine cache is within its bound (Put's tail test then finds no drain) *)
  dvb_qb : 0 <= qc_bytes (st_qthread S) <= kQuarantineCacheMax
}.

(* The memory at Put's size test (= at Recycle's call: the pass-through side stores nothing before it), relative to
   the entry memory [mem0]: dmem_m without the shadow poison (PreQuarantine runs only on the enqueue side). *)
Definition dmem_b (W : world im_segs) (ly : alayout) (sp0 : Z) (mem0 : word -> option byte) (pa nn hb1 : Z)
(DP : (word -> option byte) -> Prop) (mem' : word -> option byte) : Prop :=
(exists memD, DP memD /\ (forall a, dg_dzone ly a -> apresent (w_H W) mem0 a -> apresent (w_H W) memD a) /\
 forall x : word, dg_dzone ly (bv_unsigned x) -> mem' x = memD x) /\
(forall x : word, ~ dwin_m ly sp0 pa (bv_unsigned x) -> ~ dg_dzone ly (bv_unsigned x) -> ~ dg_izone (bv_unsigned x) ->
 mem' x = mem0 x) /\
dg_ial_post W mem' /\
(forall a, sp0 - DGbaseC.DFSTACK <= a < sp0 -> apresent (w_H W) mem' a) /\
(forall a, DGgmC.WINT ly a \/ DGgmC.WINB pa a -> apresent (w_H W) mem' a) /\
val_mem im_segs (mrestrict (w_H W) mem') (pa - 16) 4 (3 + 256 * hb1) /\ val_mem im_segs (mrestrict (w_H W) mem') (pa - 12) 4 nn /\
val_mem im_segs (mrestrict (w_H W) mem') (ly_T ly + t_unwinding) 1 0.

(* The addresses the arm writes outside its stack window before Recycle's call: dwrites without the block's shadow
   (only the enqueue side poisons it). *)
Definition dwrites_b (ly : alayout) (pa a : Z) : Prop :=
DGgiC.WINT ly a \/ (pa - 16 <= a < pa - 8) \/ (pa <= a < pa + 8) \/ dg_dzone ly a.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The interface.                                                                                                   *)
Section b.
Variable B : asyms.
Variable U : list Z -> astate -> Prop.
Variable ft : sptr -> list Z -> M unit.
Variable ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
(* the relation at Recycle's call (DMiface's cut relation; the recycle invariant [DRq] holds the chunk) *)
Variable ARXr : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
(* the arm's premise: the instance's rpre with the size guard kQuarantineMax < req_size n *)
Variable rpre : astate -> Z -> Prop.
Variable lpost : astate -> Prop.
Variable fpre : alayout -> astate -> world im_segs -> (word -> option byte) -> sptr -> Z -> Prop.
Variable dpost : Z -> alayout -> astate -> world im_segs -> list Z -> Z -> (word -> option byte) -> Prop.
Variable dbody : astate -> M unit.
Variable DRq : astate -> list chunk -> list Z -> Prop.

(* (recycle) the cut relation and the recycle invariant for the one chunk at Recycle's call, from the memory at
   Put's size test *)
Definition dbg_rq_t : Prop :=
  forall inst ly S W mem0 md0 p n tr k z hb1 sp0 (mem : word -> option byte) mat,
    ARX inst ly S W mem0 md0 -> rpre S n -> fpre ly S W mem0 p n -> In (p, n) (blocks S) -> U tr S ->
    find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
    ly_stk_lo ly + DGbaseC.DFSTACK <= sp0 -> sp0 <= ly_stk_hi ly -> ly_bot ly < sp0 -> sp0 mod 16 = 0 ->
    0 <= hb1 < 256 -> val_mem im_segs (mrestrict (w_H W) mem0) (sptr_addr B ly p - 16) 4 (2 + 256 * hb1) ->
    dmem_b W ly sp0 mem0 (sptr_addr B ly p) (req_size n) hb1 (dpost inst ly S W tr z) mem ->
    ARXr inst ly (qx S k z tr) W mem (with_vm_backing (m_vm_lazy md0) mat md0) /\ DRq (qx S k z tr) [qk k] [] /\
    (forall a, AOX ly (qx S k z tr) a -> AOX ly S a \/ (sptr_addr B ly p <= a < sptr_addr B ly p + req_size n)).

(* (recycle) QuarantineCallback::Recycle (dg_rchunk) on a chunk above kQuarantineMax: over DMiface.rcc_pre_sec, with
   the size guard; the post is DMrcRh.rchunk_sec_rh_nf's, at the interface's im_segs: the walk at amreal' over the zone
   RZ_cf and the call post acall_post_x_rh (the slack walk and the re-hide of the dead slot's shadow interior, done
   inside H4's proof), MnRecycle.de_rchunk_m_t's post without the cache flag otherwise. A cf instance gives it from
   rchunk_sec_rh_nf, the chunk's PSec arm from the size guard. *)
Definition dbg_rcs_t : Prop :=
  forall inst ly X k ks zs cbp W regs mem md,
    rcc_pre_sec B ARXr inst ly X k cbp W regs mem md -> kQuarantineMax < ck_n k -> DRq X (k :: ks) zs ->
    YG0dH.amreal' im_segs YGcfRehidePost.RZ_cf (recycle_chunk k X) W (cfg_at im_segs dg_rchunk regs mem md)
    (fun r0 W' c' => exists regs' mem' md',
      c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
      YGcfRehidePost.acall_post_x_rh B ARXr AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r0) W' regs' mem' md' /\
      acall_raw_x B AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r0) W' regs' mem' md' /\
      ErrnoG.errno_kept B mem mem' /\
      MemnormT.memnorm_keep im_segs mem mem' /\
      (forall a, 0 <= a < 2 ^ 64 -> YFeuC.puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) ->
       aview im_segs (w_H W') mem' a = aview im_segs (w_H W) mem a) /\
      (forall a, YFeuC.puser ly X a -> YFeuC.puser ly (snd r0) a) /\
      DRq (snd r0) ks zs /\ (forall a, AOX ly (snd r0) a -> AOX ly X a)).

Record DIfaceBig : Prop := {
  dbg_inst : forall inst ly S W mem md, ARX inst ly S W mem md -> dg_inst_ok inst;
  (* (view) *)
  dbg_view : forall inst ly S W mem md p n, ARX inst ly S W mem md -> rpre S n -> fpre ly S W mem p n -> In (p, n) (blocks S) ->
    dview_big B W ly inst mem S p n;
  (* (shape) the free tree's recycle side, after its entry step (ARX at the entry: an instance whose model never
     takes this side refutes it from the block's size) *)
  dbg_shape : forall inst ly W mem md p n tr S k, ARX inst ly S W mem md -> p <> PNull -> rpre S n -> In (p, n) (blocks S) ->
    find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
    ft p tr S = (depot_put tr ;; modify (fun s => set_chunks (upd_chunk (st_chunks s) (qk k)) s) ;; recycle_chunk (qk k) ;;
                 dmd dbody) (dtick S);
  (* the depot callee, as DIface's di_depot *)
  dbg_depot : forall inst ly S W mem0 md0 tr (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (buf : Z),
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
  dbg_dpost_aok : forall inst ly S W tr z m, dpost inst ly S W tr z m -> aok S (KDepot tr) z;
  (* (recycle) the cut relation and the recycle invariant at Recycle's call, and Recycle's call on the big chunk *)
  dbg_rq : dbg_rq_t;
  dbg_rcs : dbg_rcs_t;
  (* ARX again when nothing is left to recycle (DMiface's di_requar_e_t) *)
  dbg_requar_e : di_requar_e_t ARX ARXr DRq;
  (* lpost at the end of a granted path of the free tree (the thread cache is as at the entry: no drain) *)
  dbg_post : forall inst ly S W mem0 md0 p n tr (X' : astate) (W' : world im_segs) mem' md',
    ARX inst ly S W mem0 md0 -> rpre S n -> In (p, n) (blocks S) -> U tr S ->
    ARX inst ly X' W' mem' md' ->
    (exists trc, apath (ft p tr S) trc (tt, X') /\ gflag trc = true) -> lpost X';
  (* the thread cache's size word, which Put reads after Recycle returns (cgif 0x35768: c->Size()), at a state the
     walk reaches from an arm entry S *)
  dbg_qsize : forall inst ly S W mem0 md0 p n (X' : astate) (W' : world im_segs) mem' md',
    ARX inst ly S W mem0 md0 -> rpre S n -> In (p, n) (blocks S) -> ARX inst ly X' W' mem' md' ->
    val_mem im_segs (mrestrict (w_H W') mem') (ly_T ly + t_qc + 24) 8 (qc_bytes (st_qthread X'));
  (* (laws) *)
  dbg_frame : di_frame_t ARX AOX;
  dbg_frame_r : di_frame_t ARXr AOX;
  dbg_stack : di_stack_t ARX AOX;
  (* (owned) the addresses the walk writes outside its stack windows before Recycle's call *)
  dbg_owned : forall inst ly S W mem md p n k a,
    ARX inst ly S W mem md -> rpre S n -> In (p, n) (blocks S) -> find_user (st_chunks S) p = Some k ->
    0 <= a < 2 ^ 64 -> dwrites_b ly (sptr_addr B ly p) a ->
    AOX ly S a \/ (sptr_addr B ly p <= a < sptr_addr B ly p + req_size n);
  dbg_owned_i : forall inst ly S W mem md a, ARX inst ly S W mem md -> dg_izone a -> AOX ly S a
}.
End b.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* An instance whose blocks and recycled chunks are all at most kQuarantineMax (cgif_file: MALLOC_MAX = 2 ^ 28) never
   takes the big arm: its DIfaceBig at rpre /\ kQuarantineMax < req_size n holds from its DIface, every size-guarded
   field vacuously. *)
Lemma dibig_of_small : forall B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP,
  DIface B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP ->
  (forall inst ly S W mem md p n, ARX inst ly S W mem md -> In (p, n) (blocks S) -> req_size n <= kQuarantineMax) ->
  (forall inst ly X W mem md k ks zs, ARXr inst ly X W mem md -> DRq X (k :: ks) zs -> ck_n k <= kQuarantineMax) ->
  DIfaceBig B U ft ARX ARXr AOX (fun S n => rpre S n /\ kQuarantineMax < req_size n) lpost fpre dpost dbody DRq.
Proof.
  intros B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF HS HSk.
  constructor.
  - exact (di_inst _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF).
  - intros inst ly S W mem md p n HA (_ & Hb) _ Hin. exfalso. pose proof (HS _ _ _ _ _ _ _ _ HA Hin). lia.
  - intros inst ly W mem md p n tr S k HA _ (_ & Hb) Hin. exfalso. pose proof (HS _ _ _ _ _ _ _ _ HA Hin). lia.
  - exact (di_depot _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF).
  - exact (di_dpost_aok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF).
  - intros inst ly S W mem0 md0 p n tr k z hb1 sp0 mem mat HA (_ & Hb) _ Hin. exfalso.
    pose proof (HS _ _ _ _ _ _ _ _ HA Hin). lia.
  - intros inst ly X k ks zs cbp W regs mem md Hpre Hbig HD. exfalso. destruct Hpre as [HA _].
    pose proof (HSk _ _ _ _ _ _ _ _ _ HA HD). lia.
  - exact (di_requar_e _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF).
  - intros inst ly S W mem0 md0 p n tr X' W' mem' md' HA (_ & Hb) Hin. exfalso.
    pose proof (HS _ _ _ _ _ _ _ _ HA Hin). lia.
  - intros inst ly S W mem0 md0 p n X' W' mem' md' HA (_ & Hb) Hin. exfalso.
    pose proof (HS _ _ _ _ _ _ _ _ HA Hin). lia.
  - exact (di_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF).
  - exact (di_frame_r _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF).
  - exact (di_stack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF).
  - intros inst ly S W mem md p n k a HA (_ & Hb) Hin. exfalso. pose proof (HS _ _ _ _ _ _ _ _ HA Hin). lia.
  - exact (di_owned_i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF).
Qed.
End a.
