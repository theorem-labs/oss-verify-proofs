(* copy of proofs/cgif/cgif_file_fuzzer/lib/CLenq.v@ced28ed2383; do not edit. Only this line is added, and the module prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib is this unit's OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* QuarantineCache::Enqueue's contract over a generic allocator relation [ARX], image-free.

   The released contract (YFew.tfib_enqueue_spec_nb, enq_pre YFew.v:25 with its AR conjunct at :27 and the post
   YG0d.acall_post at :238) is AR-bound: it names the cgif_file relation, and its post frames only the view
   ([aview]), not the raw bytes.  [enqueue_spec_x] below restates it over [ARX] / [AOX] and over
   DMspec.acall_post_x's shape, which frames the view only, as the released post does; the same frame on the raw
   memory is DIfaceR.acall_raw_x, which DIfaceR.dr_enqueue adds for ARX-style relations that read raw bytes.

   What an instance must bring, beside the contract itself:
   - [es_inst]: the relation pins the instance object, so the post can be stated at one [inst];
   - [es_qbytes]: the thread cache's byte count cell, which Put reads after Enqueue returns;
   - [es_owned]: the owned set of a state that differs only in its quarantine cache is the old one's;
   - [es_lpost], [es_qb]: the consumer's post ([lpost]) when no drain follows, and the drain's premises
     ([QB], the class-24 batch bound) when one does, from the caller's facts [EP X k] about the pre-state.
   These are the quarantine-cache facts the Enqueue call site reads and writes; the new batch's allocation goes
   to the internal allocator, whose contract the instance supplies as [enqueue_spec_x true]'s own premise
   (cgif_file: YFl1.tfib_refill_spec with a raw frame; see CLenqcgif.tfib_refill_specR). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0l YG0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.

(* Enqueue's stack need below its entry sp (YFew.QSTACK). *)
Definition QSTACK_G : Z := 1088.

Section b.
Variable segs : list Segment.
Variable B : asyms.
Variable ARX : Z -> alayout -> astate -> world segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
(* Enqueue's entry pc in the image. *)
Variable A_ENQ : Z.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The call post over ARX / AOX (DMspec.acall_post_x, over [segs]).                                                 *)
Definition acall_post_x (inst stk : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (E : Z -> Prop)
(ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
(mem' : word -> option byte) (md' : Model) : Prop :=
ARX inst ly' S' W' mem' md' /\ layout_le (length (st_secs S)) ly ly' /\ wle W W' /\
aregs_preserved regs regs' /\ same_io md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly S a -> ~ AOX ly' S' a -> ~ ascratch B stk regs a -> ~ E a ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ AOX ly' S' (bv_unsigned x) -> ~ ascratch B stk regs (bv_unsigned x) ->
  ~ E (bv_unsigned x) -> mem' x = mem x) /\
(forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W') mem' a).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The contract (YFew.v:25-55 over ARX).                                                                            *)

(* YFew.enq_pre with [ARX inst] for AR. *)
Definition enq_pre_x (inst : Z) (ly : alayout) (X : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (k : chunk) : Prop :=
ARX inst ly X W mem md /\ A_bytes (w_A W) + EV_A <= abudget X /\
Z.of_nat (length (all_batches X)) + 1 <= st_nev X /\ refill_reg X kBatchClass /\
In k (st_chunks X) /\ ck_state k = CQuarantined /\ ~ In (ck_beg k) (map ck_beg (q_items X)) /\
YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + QSTACK_G <= spZ regs /\ spZ regs <= ly_stk_hi ly /\
(forall a, spZ regs - QSTACK_G <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 10 = w64 (ly_T ly + t_qc) /\ getr regs 11 = w64 (ly_T ly + t_cache) /\
getr regs 13 = w64 (sptr_addr B ly (ck_user k) - kChunkHeaderSize) /\ getr regs 14 = w64 (ck_n k) /\
qloosem X.

(* YFew.enq_leaf over [acall_post_x]. *)
Definition enq_leaf_x (inst : Z) (ly : alayout) (X : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (k : chunk)
(r : unit * astate) (W' : world segs) (c' : config) : Prop :=
exists regs' mem' md' nb,
c' = cfg_at segs (raZ regs) regs' mem' md' /\
acall_post_x inst QSTACK_G ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
st_qthread (snd r) = qc_push (st_qthread X) k nb /\
match nb with None => need_new_batch (st_qthread X) = false | Some _ => need_new_batch (st_qthread X) = true end /\
st_chunks (snd r) = st_chunks X /\ st_qglobal (snd r) = st_qglobal X /\
st_fs (snd r) = st_fs X.

Definition enqueue_spec_x (nbq : bool) : Prop :=
forall inst ly X W regs mem md k,
need_new_batch (st_qthread X) = nbq ->
enq_pre_x inst ly X W regs mem md k ->
amreal segs (enqueue k X) W (cfg_at segs A_ENQ regs mem md) (enq_leaf_x inst ly X W regs mem md k).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The sub-interface: the quarantine-cache facts of the call site, over the consumer's [lpost] / [QB] / [L24].      *)
Section c.
Variable lpost : astate -> Prop.
Variable QB : astate -> Prop.
Variable L24 : Z.
(* The caller's facts about the pre-state [X] and the chunk [k] that the enqueue pre does not carry.  Enqueue's
   pre only has qloosem X (the chunk is already marked quarantined but not yet queued, so the tight quarantine
   bound does not hold there); the post's [lpost] needs the caller's tight bounds (cgif_file: kQuarantineMax on the
   global cache, 2^28 < 2^30 of qloose, and quar_n X <= queued_n X + ck_n k), which the caller has from its own
   entry state. *)
Variable EP : astate -> chunk -> Prop.

Record EnqSub : Prop := {
  (* the relation pins the instance object *)
  es_inst : forall inst inst' ly ly' X X' W W' mem mem' md md',
    ARX inst ly X W mem md -> ARX inst' ly' X' W' mem' md' -> inst = inst';
  (* the thread cache's byte count, read by Put after Enqueue returns *)
  es_qbytes : forall inst ly X W mem md, ARX inst ly X W mem md ->
    val_mem segs (mrestrict (w_H W) mem) (ly_T ly + t_qc + 24) 8 (qc_bytes (st_qthread X));
  (* a state that differs only in its quarantine cache owns no more than the old one *)
  es_owned : forall ly X X' a, st_chunks X' = st_chunks X -> st_fs X' = st_fs X -> AOX ly X' a -> AOX ly X a;
  (* the consumer's post, when the thread cache stays below the drain threshold *)
  es_lpost : forall inst ly X W mem md k nb X',
    ARX inst ly X W mem md -> EP X k -> In k (st_chunks X) -> ck_state k = CQuarantined ->
    ~ In (ck_beg k) (map ck_beg (q_items X)) -> qloosem X ->
    match nb with None => need_new_batch (st_qthread X) = false | Some _ => need_new_batch (st_qthread X) = true end ->
    st_qthread X' = qc_push (st_qthread X) k nb -> st_chunks X' = st_chunks X -> st_qglobal X' = st_qglobal X ->
    qc_bytes (st_qthread X') <= kQuarantineCacheMax -> lpost X';
  (* the drain's premises, when it does not *)
  es_qb : forall inst ly X W mem md k nb X',
    ARX inst ly X W mem md -> EP X k -> In k (st_chunks X) -> ck_state k = CQuarantined ->
    ~ In (ck_beg k) (map ck_beg (q_items X)) -> qloosem X ->
    Z.of_nat (length (all_batches X)) + 1 <= st_nev X ->
    match nb with None => need_new_batch (st_qthread X) = false | Some _ => need_new_batch (st_qthread X) = true end ->
    st_qthread X' = qc_push (st_qthread X) k nb -> st_chunks X' = st_chunks X -> st_qglobal X' = st_qglobal X ->
    kQuarantineCacheMax < qc_bytes (st_qthread X') -> QB X' /\ Z.of_nat (length (all_batches X')) <= L24
}.

(* The post DGif0.di_enqueue states at Put's call of Enqueue (its [amreal] leaf), over [segs]. *)
Definition di_enq_post (inst : Z) (ly : alayout) (X : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (k : chunk)
(r : unit * astate) (W' : world segs) (c' : config) : Prop :=
exists regs' mem' md' nb,
c' = cfg_at segs (raZ regs) regs' mem' md' /\
acall_post_x inst QSTACK_G ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
st_qthread (snd r) = qc_push (st_qthread X) k nb /\
match nb with None => need_new_batch (st_qthread X) = false | Some _ => need_new_batch (st_qthread X) = true end /\
st_chunks (snd r) = st_chunks X /\ st_qglobal (snd r) = st_qglobal X /\
(forall a, AOX ly (snd r) a -> AOX ly X a) /\
val_mem segs (mrestrict (w_H W') mem') (ly_T ly + t_qc + 24) 8 (qc_bytes (st_qthread (snd r))) /\
(qc_bytes (st_qthread (snd r)) <= kQuarantineCacheMax -> lpost (snd r)) /\
(kQuarantineCacheMax < qc_bytes (st_qthread (snd r)) -> QB (snd r) /\ Z.of_nat (length (all_batches (snd r))) <= L24).

(* The leaf of the generic contract gives the post the interface field states. *)
Theorem di_enq_post_of_leaf : EnqSub ->
forall inst ly X W regs mem md k r W' c',
EP X k -> enq_pre_x inst ly X W regs mem md k ->
enq_leaf_x inst ly X W regs mem md k r W' c' ->
di_enq_post inst ly X W regs mem md k r W' c'.
Proof.
intros SUB inst ly X W regs mem md k r W' c' HEP PRE LEAF.
destruct PRE as (HARX & Hbud & Hbev & Hrf & Hk & Hst & Hnq & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha3 & Ha4 & HQL).
destruct LEAF as (regs' & mem' & md' & nb & Hc & POST & Hqt & Hnb & Hch & Hqg & Hfs).
pose proof (proj1 POST) as HARX'.
exists regs', mem', md', nb.
split; [exact Hc|]. split; [exact POST|]. split; [exact Hqt|]. split; [exact Hnb|].
split; [exact Hch|]. split; [exact Hqg|].
split; [intros a Ha; exact (es_owned SUB ly X (snd r) a Hch Hfs Ha)|].
split; [exact (es_qbytes SUB inst ly (snd r) W' mem' md' HARX')|].
split.
- intros Hle. exact (es_lpost SUB inst ly X W mem md k nb (snd r) HARX HEP Hk Hst Hnq HQL Hnb Hqt Hch Hqg Hle).
- intros Hgt. exact (es_qb SUB inst ly X W mem md k nb (snd r) HARX HEP Hk Hst Hnq HQL Hbev Hnb Hqt Hch Hqg Hgt).
Qed.
End c.
End b.
End a.
