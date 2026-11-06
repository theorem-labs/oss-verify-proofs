(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DIfaceR.v (a working branch 30a1993588f, c5 + memnorm; file sha256 1233e7824daa) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* The raw-frame obligations of the frame-generic Deallocate walk, split out of DGif0.DIface.

   DIface's callee contracts (QuarantineCache::Enqueue, Quarantine::Drain and, inside the drain, QuarantineCallback::
   Recycle and CacheDealloc) frame the memory on the view only (DMspec.acall_post_x, as the released acall_post
   YG0d.v:246-254 and the released drain walk state it).  The raw twin of the Deallocate contract
   (DeallocG.adealloc_realizes_raw: the frame also on the raw bytes, which aview hides) needs the same frame on the
   raw memory from the callees.  This file states it:
   - [acall_raw_x]: acall_post_x's raw conjunct (the frame on the raw memory);
   - [drain_leaf_raw_cf] / [drain_spec_raw_cf]: DMspec's drain contract with the raw conjunct in its post;
   - [dr_rchunk_t] / [dr_cdealloc_t]: DMiface's Recycle / CacheDealloc contracts with the raw conjunct (for whoever
     proves [dr_drain]);
   - [DIfaceR]: the record, over DIface's parameters: [dr_enqueue] (di_enqueue's contract with the raw conjunct),
     [dr_drain], [dr_rchunk], [dr_cdealloc].
   No instance of DIfaceR is proved here (cgif's is open: the released drain walk frames the view only).

   The second part gives the arms one proof for both forms: [enq_spec_b] / [drain_spec_b] are the Enqueue and Drain
   contracts whose raw conjunct holds when [rawb = true]; [dealloc_leaf_b] is the Deallocate leaf whose raw frame
   holds when [rawb = true].  DIface gives the [rawb = false] contracts, DIface + DIfaceR the [rawb = true] ones;
   the [false] leaf is DeallocG.dealloc_leaf, the [true] leaf DeallocG.dealloc_leaf_raw. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import DMspec DMiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import DeallocG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseDG DGif0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {IM : AImg} {DI : DImg}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The raw conjunct.                                                                                                *)
Section r.
Variable B : asyms.
Variable AOX : alayout -> astate -> Z -> Prop.
(* DMspec.acall_post_x's frame, on the raw memory (its arguments are acall_post_x's). *)
Definition acall_raw_x (inst stk : Z) (ly : alayout) (S : astate) (W : world im_segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (E : Z -> Prop)
(ly' : alayout) (S' : astate) (W' : world im_segs) (regs' : bvmap 5 word)
(mem' : word -> option byte) (md' : Model) : Prop :=
forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ AOX ly' S' (bv_unsigned x) -> ~ ascratch B stk regs (bv_unsigned x) ->
  ~ E (bv_unsigned x) -> mem' x = mem x.
End r.

(* The shape of an extra conjunct on a callee post (acall_raw_x's arguments). *)
Definition fxrel : Type :=
Z -> Z -> alayout -> astate -> world im_segs -> bvmap 5 word -> (word -> option byte) -> Model -> (Z -> Prop) ->
alayout -> astate -> world im_segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The drain contract with an extra conjunct [XR] on its post; [XR := acall_raw_x] is the raw one.                  *)
Section dr.
Variable B : asyms.
Variable ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable dbody : astate -> M unit.
Variable L24 : Z.
Variable QB : astate -> Prop.
Definition drain_leaf_g (XR : fxrel) (inst : Z) (ly : alayout) (X : astate) (W : world im_segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model)
(r : unit * astate) (W' : world im_segs) (c' : config) : Prop :=
exists regs' mem' md',
c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
acall_post_x B ARX AOX inst YFeuC.DSTACK ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
XR inst YFeuC.DSTACK ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md'.
Definition drain_spec_g (XR : fxrel) : Prop :=
forall inst ly X W regs mem md,
drain_pre_cf B ARX L24 QB inst ly X W regs mem md ->
amreal im_segs (dbody X X) W (cfg_at im_segs dg_drain regs mem md) (drain_leaf_g XR inst ly X W regs mem md).
(* The raw drain contract. *)
Definition drain_leaf_raw_cf := drain_leaf_g (acall_raw_x B AOX).
Definition drain_spec_raw_cf : Prop := drain_spec_g (acall_raw_x B AOX).
End dr.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Recycle / CacheDealloc with the raw conjunct (DMiface.di_rchunk_t / di_cdealloc_t plus acall_raw_x).             *)
Section rc.
Variable B : asyms.
Variable ARXr : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Definition dr_rchunk_t : Prop :=
forall inst ly X k ks zs cbp W regs mem md,
rcc_pre_x B ARXr inst ly X k cbp W regs mem md -> DRq X (k :: ks) zs ->
amreal im_segs (recycle_chunk k X) W (cfg_at im_segs dg_rchunk regs mem md)
(fun r W' c' => exists regs' mem' md',
  c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
  acall_post_x B ARXr AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  acall_raw_x B AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  (forall a, 0 <= a < 2 ^ 64 -> YFeuC.puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) ->
   aview im_segs (w_H W') mem' a = aview im_segs (w_H W) mem a) /\
  (forall a, YFeuC.puser ly X a -> YFeuC.puser ly (snd r) a) /\
  DRq (snd r) ks zs /\ st_cache_inited (snd r) = true /\ (forall a, AOX ly (snd r) a -> AOX ly X a)).
Definition dr_cdealloc_t : Prop :=
forall inst ly X its z zs W regs mem md,
cd_pre_x B ARXr inst ly X z W regs mem md -> DRq X its (z :: zs) ->
amreal im_segs (cache_dealloc kBatchClass z X) W (cfg_at im_segs dg_cdealloc regs mem md)
(fun r W' c' => exists regs' mem' md',
  c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
  acall_post_x B ARXr AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  acall_raw_x B AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  (forall a, 0 <= a < 2 ^ 64 -> YFeuC.puser ly X a -> aview im_segs (w_H W') mem' a = aview im_segs (w_H W) mem a) /\
  (forall a, YFeuC.puser ly X a -> YFeuC.puser ly (snd r) a) /\
  DRq (snd r) its zs /\ st_cache_inited (snd r) = true /\ (forall a, AOX ly (snd r) a -> AOX ly X a)).
End rc.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The record (DIface's parameters).                                                                                *)
Section b.
Variable B : asyms.
Variable U : list Z -> astate -> Prop.
Variable ft : sptr -> list Z -> M unit.
Variable ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variable ARXr : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable lpost : astate -> Prop.
Variable fpre : alayout -> astate -> world im_segs -> (word -> option byte) -> sptr -> Z -> Prop.
Variable dpost : Z -> alayout -> astate -> world im_segs -> list Z -> Z -> (word -> option byte) -> Prop.
Variable dbody : astate -> M unit.
Variable L24 : Z.
Variable QB : astate -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
(* DGif0.DIface's memory predicate at Put's call of Enqueue (di_enqueue's premise). *)
Variable MP : (word -> option byte) -> Prop.

(* DIface.di_enqueue's contract with an extra conjunct [XR] on Enqueue's post. *)
Definition enq_spec_g (XR : fxrel) : Prop :=
forall inst ly S W mem0 md0 p n tr k z hb1 sp0 (regs : bvmap 5 word) (mem : word -> option byte) mat,
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
    XR inst YFewC.QSTACK ly (qx S k z tr) W regs mem (with_vm_backing (m_vm_lazy md0) mat md0) (fun _ => False)
      ly (snd r) W' regs' mem' md' /\
    st_qthread (snd r) = qc_push (st_qthread (qx S k z tr)) (qk k) nb /\
    match nb with None => need_new_batch (st_qthread (qx S k z tr)) = false | Some _ => need_new_batch (st_qthread (qx S k z tr)) = true end /\
    st_chunks (snd r) = st_chunks (qx S k z tr) /\ st_qglobal (snd r) = st_qglobal (qx S k z tr) /\
    (forall a, AOX ly (snd r) a -> AOX ly (qx S k z tr) a) /\
    val_mem im_segs (mrestrict (w_H W') mem') (ly_T ly + t_qc + 24) 8 (qc_bytes (st_qthread (snd r))) /\
    (qc_bytes (st_qthread (snd r)) <= kQuarantineCacheMax -> lpost (snd r)) /\
    (kQuarantineCacheMax < qc_bytes (st_qthread (snd r)) -> QB (snd r) /\ Z.of_nat (length (all_batches (snd r))) <= L24)).

Record DIfaceR : Prop := {
  (* QuarantineCache::Enqueue at Put's call: DIface.di_enqueue with the raw frame *)
  dr_enqueue : enq_spec_g (acall_raw_x B AOX);
  (* Quarantine::Drain at Put's call: DIface.di_drain with the raw frame *)
  dr_drain : drain_spec_raw_cf B ARX AOX dbody L24 QB;
  (* inside the drain: Recycle and CacheDealloc with the raw frame (DIface.di_rchunk / di_cdealloc) *)
  dr_rchunk : dr_rchunk_t B ARXr AOX DRq;
  dr_cdealloc : dr_cdealloc_t B ARXr AOX DRq
}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* For the arms: one proof for both forms.                                                                          *)
Definition rawif (rawb : bool) (XR : fxrel) : fxrel :=
fun inst stk ly S W regs mem md E ly' S' W' regs' mem' md' =>
rawb = true -> XR inst stk ly S W regs mem md E ly' S' W' regs' mem' md'.
Definition enq_spec_b (rawb : bool) : Prop := enq_spec_g (rawif rawb (acall_raw_x B AOX)).
Definition drain_spec_b (rawb : bool) : Prop := drain_spec_g B ARX AOX dbody L24 QB (rawif rawb (acall_raw_x B AOX)).

Lemma enq_spec_b_false : DIface B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP -> enq_spec_b false.
Proof.
intros IF inst ly S W mem0 md0 p n tr k z hb1 sp0 regs mem mat H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17
  H18 H19 H20 H21 H22 H23 H24.
eapply amreal_mono; [| exact (di_enqueue B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF
  inst ly S W mem0 md0 p n tr k z hb1 sp0 regs mem mat H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17
  H18 H19 H20 H21 H22 H23 H24)].
intros r W' c' (regs' & mem' & md' & nb & Hc & HP & HR).
exists regs', mem', md', nb. split; [exact Hc|]. split; [exact HP|]. split; [intros X; discriminate X | exact HR].
Qed.
Lemma enq_spec_b_true : DIfaceR -> enq_spec_b true.
Proof.
intros IR inst ly S W mem0 md0 p n tr k z hb1 sp0 regs mem mat H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17
  H18 H19 H20 H21 H22 H23 H24.
eapply amreal_mono; [| exact (dr_enqueue IR
  inst ly S W mem0 md0 p n tr k z hb1 sp0 regs mem mat H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17
  H18 H19 H20 H21 H22 H23 H24)].
intros r W' c' (regs' & mem' & md' & nb & Hc & HP & HX & HR).
exists regs', mem', md', nb. split; [exact Hc|]. split; [exact HP|]. split; [intros _; exact HX | exact HR].
Qed.
Lemma drain_spec_b_false : DIface B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP -> drain_spec_b false.
Proof.
intros IF inst ly X W regs mem md PRE.
eapply amreal_mono; [| exact (di_drain B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF inst ly X W regs mem md PRE)].
intros r W' c' (regs' & mem' & md' & Hc & HP).
exists regs', mem', md'. split; [exact Hc|]. split; [exact HP | intros X0; discriminate X0].
Qed.
Lemma drain_spec_b_true : DIfaceR -> drain_spec_b true.
Proof.
intros IR inst ly X W regs mem md PRE.
eapply amreal_mono; [| exact (dr_drain IR inst ly X W regs mem md PRE)].
intros r W' c' (regs' & mem' & md' & Hc & HP & HX).
exists regs', mem', md'. split; [exact Hc|]. split; [exact HP | intros _; exact HX].
Qed.

(* The Deallocate leaf whose raw frame holds when [rawb = true]. *)
Definition dealloc_leaf_b (rawb : bool) (inst : Z) (ly : alayout) (S : astate) (W : world im_segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n : Z) (tr : list Z)
(r : unit * astate) (W' : world im_segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
dealloc_post im_segs B ARX AOX inst ly S W regs mem md
  (fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n) ly' (snd r) W' regs' mem' md' /\
(rawb = true -> forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ AOX ly' (snd r) (bv_unsigned x) ->
  ~ ascratch B DFSTACK_G regs (bv_unsigned x) ->
  ~ (p <> PNull /\ sptr_addr B ly p <= bv_unsigned x < sptr_addr B ly p + req_size n) -> mem' x = mem x) /\
lpost (snd r) /\
(exists trc, apath (ft p tr S) trc r /\ gflag trc = true).

Lemma leaf_b_aview : forall rawb inst ly S W regs mem md p n tr r W' c',
dealloc_leaf_b rawb inst ly S W regs mem md p n tr r W' c' ->
dealloc_leaf im_segs B ft ARX AOX lpost inst ly S W regs mem md p n tr r W' c'.
Proof.
intros rawb inst ly S W regs mem md p n tr r W' c' (ly' & regs' & mem' & md' & Hc & HP & _ & HL & HT).
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact HP|]. split; [exact HL | exact HT].
Qed.
Lemma leaf_b_raw : forall inst ly S W regs mem md p n tr r W' c',
dealloc_leaf_b true inst ly S W regs mem md p n tr r W' c' ->
dealloc_leaf_raw im_segs B ft ARX AOX lpost inst ly S W regs mem md p n tr r W' c'.
Proof.
intros inst ly S W regs mem md p n tr r W' c'
  (ly' & regs' & mem' & md' & Hc & (H1 & H2 & H3 & H4 & H5 & H6 & H7) & HR & HL & HT).
exists ly', regs', mem', md'. split; [exact Hc|].
split; [|split; [exact HL | exact HT]].
repeat (split; [assumption|]). split; [exact (HR eq_refl)|]. exact H7.
Qed.
Lemma leaf_raw_b : forall rawb inst ly S W regs mem md p n tr r W' c',
dealloc_leaf_raw im_segs B ft ARX AOX lpost inst ly S W regs mem md p n tr r W' c' ->
dealloc_leaf_b rawb inst ly S W regs mem md p n tr r W' c'.
Proof.
intros rawb inst ly S W regs mem md p n tr r W' c'
  (ly' & regs' & mem' & md' & Hc & (H1 & H2 & H3 & H4 & H5 & H6 & HR & H7) & HL & HT).
exists ly', regs', mem', md'. split; [exact Hc|].
split; [repeat (split; [assumption|]); exact H7|].
split; [intros _; exact HR|]. split; [exact HL | exact HT].
Qed.
End b.
End a.
