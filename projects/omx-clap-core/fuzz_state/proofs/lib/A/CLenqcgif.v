(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/CLenqcgif.v (a working branch 84ee52cd012, file sha256 933f12ff32f3) onto omx-clap-core/fuzz_state's asan image (unstripped fuzz_state.asan, sha256 7c4afaee248b); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: relocated to omx-clap-core fuzz_state image A (fs.asan): fs C5 - enq_bridge, di_enqueue_cgif and di_enqueue_ok take the instance's trace premise tr_admit (as_universe B) S tr instead of In tr (as_universe B) (as AFfl.v); the proofs pass it through unchanged. *)
(* cgif_file's instance of the generic Enqueue contract (CLenq.enqueue_spec_x).

   The released contract (AFew.tfib_enqueue_spec_nb) is proved arm by arm in YFg4 (the last batch has room),
   YFg5 (a new batch from a non-empty cache) and YFg6 (a new batch after a refill).  Its post is
   YG0d.acall_post, which frames the view only.  CLenq.acall_post_x asks for the same frame on the raw bytes as
   well, so each arm is re-run here from the same released pieces: the walk's segment lemma, whose [at_RET*]
   post carries the raw frame ([AFgp.MEQ] and its twins), and the released leaf lemma for everything else.  No
   new walk and no new model reasoning: the raw clause is the walk's own frame, read through
   [AFf1.D_owned] (every address the arm writes is owned by the allocator or lies in the call's stack
   scratch).  Each arm ([enq_room_xs] / [enq_hit_xs] / [enq_miss_xs]) states that frame first with only those two
   sets excluded ([enq_leaf_xs]; CLenqcgifE reads errno from it), and the CLenq leaf follows from it. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0l YG0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AFeq AFew AFfq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YFfp YFfj YFfk.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AFft AFf1 AFf2 AFgp AFgq AFgr AFh3 AFh4 AFh5 AFh6 AFg4 AFg5 AFg6.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AllocGcgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import DeallocGcgif DGbase DGgi DGgm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import ImgBase ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AGif2cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DGif0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import CLrefill0 CLrefillR.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require CLdepot.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require CLenq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.

(* The config's memory, read off a config equation (the walk's and the leaf's share one config). *)
Lemma cfg_mem_eq : forall (c1 c2 : config), c1 = c2 -> ms_mem (cfg_ms c1) = ms_mem (cfg_ms c2).
Proof. intros c1 c2 E. rewrite E. reflexivity. Qed.

Section b.
Variable B : asyms.
Hypothesis TB : TfibSyms B.

(* The generic pre at ARX_cgif is the released pre. *)
Lemma enq_pre_of_x : forall inst ly X W regs mem md k,
CLenq.enq_pre_x tfibsegs B (ARX_cgif B) inst ly X W regs mem md k -> enq_pre B ly X W regs mem md k.
Proof. intros inst ly X W regs mem md k (HARX & R). exact (conj (proj2 HARX) R). Qed.

Lemma inst_of_x : forall inst ly X W regs mem md k,
CLenq.enq_pre_x tfibsegs B (ARX_cgif B) inst ly X W regs mem md k -> inst = TFIB_INST.
Proof. intros inst ly X W regs mem md k (HARX & _). exact (proj1 HARX). Qed.

(* CLenq.enq_leaf_x plus the arm's raw frame over the bytes the arm writes: the bytes the pre-state's allocator owns
   and Enqueue's stack window.  CLenq.acall_post_x's raw clause excludes more (the post-state's owned bytes, errno
   through ascratch); each arm's proof below derives this smaller exclusion first, and the released contract from it. *)
Definition enq_leaf_xs (inst : Z) (ly : alayout) (X : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (k : chunk)
(r : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
CLenq.enq_leaf_x tfibsegs B (ARX_cgif B) (aowned B) inst ly X W regs mem md k r W' c' /\
exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
(forall x : word, ~ aowned B ly X (bv_unsigned x) -> ~ (spZ regs - CLenq.QSTACK_G <= bv_unsigned x < spZ regs) ->
   mem' x = mem x).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The arm whose last batch has room (need_new_batch = false): AFh3.segP + AFg4.FINPH, with the raw frame added.    *)
Theorem enq_room_xs : forall inst ly X W regs mem md k,
CLenq.enq_pre_x tfibsegs B (ARX_cgif B) inst ly X W regs mem md k ->
need_new_batch (st_qthread X) = false ->
amreal tfibsegs (enqueue k X) W (cfg_at tfibsegs A_Enqueue regs mem md)
(enq_leaf_xs inst ly X W regs mem md k).
Proof.
intros inst ly X W regs mem md k PREX HNB.
pose proof (enq_pre_of_x inst ly X W regs mem md k PREX) as ENQ.
pose proof (inst_of_x inst ly X W regs mem md k PREX) as Hinst.
assert (HTSD : ly_tsd ly = TFIB_TSD).
{ pose proof (AFg4.M B ly X W regs mem md k ENQ) as M0. rewrite (am_tsd B ly X _ M0). exact (ts_tsd _ TB). }
rewrite (enqueue_room_eq k X HNB). cbn [amreal].
unfold cfg_at, A_Enqueue. rewrite <- (AFg4.wvb_self md) at 1.
eapply SRr_mono.
- exact (AFh3.segP W ly regs mem md (sptr_addr B ly (ck_user k)) (ck_n k) (AFgq.QSZv (st_qthread X))
    (AFg4.QLv ly X) (AFgq.QBv (st_qthread X)) (AFg4.CNTv X) (AFg4.BSZv X) (m_vm_materialized md)
    (AFg4.FH_ok B TB ly X W regs mem md k ENQ HNB)).
- intros W' c' _ HR.
  pose proof (AFg4.FINPH B TB ly X W regs mem md k ENQ HNB HTSD W' c' HR) as LEAF.
  destruct HR as (HWW & regs2 & mem2 & mat2 & Hc2 & CS & MEQ' & PRESW & VALS).
  destruct LEAF as (regs' & mem' & md' & nb & Hc & POST & Hqt & Hnbm & Hch & Hqg & Hfs).
  assert (Em : mem' = mem2).
  { pose proof (cfg_mem_eq _ _ (eq_trans (eq_sym Hc) Hc2)) as E. cbn in E. exact E. }
  assert (FRs : forall x : word, ~ aowned B ly X (bv_unsigned x) ->
    ~ (spZ regs - CLenq.QSTACK_G <= bv_unsigned x < spZ regs) -> mem' x = mem x).
  { intros x NO NS. rewrite Em. apply MEQ'. intros HW.
    assert (HD : AFf1.D ly (AFg4.lb X) (bv_unsigned (getr regs 2)) (bv_unsigned x)).
    { unfold AFf1.D, AFf1.DT, AFf1.DL, AFf1.DS, AFf1.QLv, AFf1.CNTv.
      unfold AFgp.WIN, AFgp.SLv in HW. unfold AFg4.QLv, AFg4.CNTv in HW.
      destruct HW as [HW|[HW|[HW|HW]]];
        [do 2 right; clear - HW; unfold QSTACK in *; lia | left; exact HW | right; left; left; exact HW
        | right; left; right; lia]. }
    destruct (AFf1.D_owned B ly X (aview tfibsegs (w_H W) mem) (AFg4.M B ly X W regs mem md k ENQ)
      (AFg4.lb X) (AFg4.initr X) (AFg4.Hrev X HNB) (AFg4.Hroom B ly X W regs mem md k ENQ HNB)
      (bv_unsigned (getr regs 2)) (AFg4.HSP B ly X W regs mem md k ENQ)
      (AFg4.IMG B ly X W regs mem md k ENQ) (bv_unsigned x) (proj1 (u64_range x)) HD) as [O|O].
    - exact (NO O).
    - apply NS. unfold AFf1.DS in O. unfold spZ, CLenq.QSTACK_G, QSTACK in *. exact O. }
  split; [| exists regs', mem', md'; split; [exact Hc | exact FRs]].
  exists regs', mem', md', nb.
  split; [exact Hc|].
  split.
  { destruct POST as (AR' & LLE & WLE & ARP & SIO & AGV & PRS).
    split; [split; [exact Hinst | exact AR']|].
    split; [exact LLE|]. split; [exact WLE|]. split; [exact ARP|]. split; [exact SIO|].
    split; [exact AGV|]. split; [| exact PRS].
    intros x NO NO' NS NE. apply FRs; [exact NO|]. intros O. apply NS. unfold ascratch. left. exact O. }
  split; [exact Hqt|]. split; [exact Hnbm|]. split; [exact Hch|]. split; [exact Hqg|]. exact Hfs.
Qed.

Theorem enq_room_x : forall inst ly X W regs mem md k,
CLenq.enq_pre_x tfibsegs B (ARX_cgif B) inst ly X W regs mem md k ->
need_new_batch (st_qthread X) = false ->
amreal tfibsegs (enqueue k X) W (cfg_at tfibsegs A_Enqueue regs mem md)
(CLenq.enq_leaf_x tfibsegs B (ARX_cgif B) (aowned B) inst ly X W regs mem md k).
Proof.
intros inst ly X W regs mem md k PREX HNB.
eapply amreal_mono; [| exact (enq_room_xs inst ly X W regs mem md k PREX HNB)].
intros r W' c' [L _]. exact L.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The new-batch arm with a non-empty batch cache: AFh4.segQH + AFg5.FINQH, with the raw frame added.               *)
Theorem enq_hit_xs : forall inst ly X W regs mem md k l,
CLenq.enq_pre_x tfibsegs B (ARX_cgif B) inst ly X W regs mem md k ->
need_new_batch (st_qthread X) = true ->
pc_chunks (cache X kBatchClass) = l -> l <> [] ->
amreal tfibsegs (enqueue k X) W (cfg_at tfibsegs A_Enqueue regs mem md)
(enq_leaf_xs inst ly X W regs mem md k).
Proof.
intros inst ly X W regs mem md k l PREX HNB Hl Hlne.
pose proof (enq_pre_of_x inst ly X W regs mem md k PREX) as ENQ.
pose proof (inst_of_x inst ly X W regs mem md k PREX) as Hinst.
assert (HTSD : ly_tsd ly = TFIB_TSD).
{ pose proof (AFg5.M B ly X W regs mem md k ENQ) as M0. rewrite (am_tsd B ly X _ M0). exact (ts_tsd _ TB). }
rewrite (AFg5.enqueue_hit_eq B ly X W regs mem md k ENQ HNB l Hl Hlne). cbn [amreal].
pose proof (AFg5.cache_vals B ly X W regs mem md k ENQ l Hl Hlne) as (_ & _ & _ & _ & C5).
unfold cfg_at, A_Enqueue. rewrite <- (AFg4.wvb_self md) at 1.
eapply SRr_mono.
- exact (AFh4.segQH W ly regs mem md (sptr_addr B ly (ck_user k)) (ck_n k) (st_qthread X)
    (AFg5.cnt l) (AFg5.coff l) (AFg5.jst ly W mem) (m_vm_materialized md)
    (AFg5.FH_ok B TB ly X W regs mem md k ENQ HNB l Hl Hlne) C5).
- intros W' c' _ HR.
  pose proof (AFg5.FINQH B TB ly X W regs mem md k ENQ HNB l Hl Hlne HTSD W' c' HR) as LEAF.
  destruct HR as (HWW & regs2 & mem2 & mat2 & Hc2 & CS & MEQ' & PRESW & VALS).
  destruct LEAF as (regs' & mem' & md' & nb & Hc & POST & Hqt & Hnbm & Hch & Hqg & Hfs).
  assert (Em : mem' = mem2).
  { pose proof (cfg_mem_eq _ _ (eq_trans (eq_sym Hc) Hc2)) as E. cbn in E. exact E. }
  assert (ENB : AFgq.NBv ly (AFg5.coff l) = ly_space ly + (region_off kBatchClass + last l 0))
    by (unfold AFgq.NBv, AFg5.coff; lia).
  assert (FRs : forall x : word, ~ aowned B ly X (bv_unsigned x) ->
    ~ (spZ regs - CLenq.QSTACK_G <= bv_unsigned x < spZ regs) -> mem' x = mem x).
  { intros x NO NS. rewrite Em. apply MEQ'. intros HW.
    assert (HD : AFf2.D ly X l (bv_unsigned (getr regs 2)) (bv_unsigned x)).
    { unfold AFf2.D, AFf2.DT, AFf2.DN, AFf2.DL, AFf2.DS.
      unfold AFgq.WIN, AFgq.WINT, AFgq.WINA in HW. rewrite ENB in HW.
      destruct HW as [HW|[HW|[[_ HW]|[Hq HW]]]].
      - do 3 right. clear - HW. unfold QSTACK. lia.
      - left. exact HW.
      - right; left. exact HW.
      - right; right; left. split; [exact Hq|]. unfold AFf2.QLv. unfold AFgq.QLv in HW. exact HW. }
    destruct (AFf2.D_owned B ly X (aview tfibsegs (w_H W) mem) (AFg5.M B ly X W regs mem md k ENQ) k
      (AFg5.Hci B ly X W regs mem md k ENQ l Hl Hlne) l Hl Hlne (bv_unsigned (getr regs 2))
      (AFg5.HSP B ly X W regs mem md k ENQ) (bv_unsigned x) (proj1 (u64_range x)) HD) as [O|O].
    - exact (NO O).
    - apply NS. unfold AFf2.DS in O. unfold spZ, CLenq.QSTACK_G, QSTACK in *. exact O. }
  split; [| exists regs', mem', md'; split; [exact Hc | exact FRs]].
  exists regs', mem', md', nb.
  split; [exact Hc|].
  split.
  { destruct POST as (AR' & LLE & WLE & ARP & SIO & AGV & PRS).
    split; [split; [exact Hinst | exact AR']|].
    split; [exact LLE|]. split; [exact WLE|]. split; [exact ARP|]. split; [exact SIO|].
    split; [exact AGV|]. split; [| exact PRS].
    intros x NO NO' NS NE. apply FRs; [exact NO|]. intros O. apply NS. unfold ascratch. left. exact O. }
  split; [exact Hqt|]. split; [exact Hnbm|]. split; [exact Hch|]. split; [exact Hqg|]. exact Hfs.
Qed.

Theorem enq_hit_x : forall inst ly X W regs mem md k l,
CLenq.enq_pre_x tfibsegs B (ARX_cgif B) inst ly X W regs mem md k ->
need_new_batch (st_qthread X) = true ->
pc_chunks (cache X kBatchClass) = l -> l <> [] ->
amreal tfibsegs (enqueue k X) W (cfg_at tfibsegs A_Enqueue regs mem md)
(CLenq.enq_leaf_x tfibsegs B (ARX_cgif B) (aowned B) inst ly X W regs mem md k).
Proof.
intros inst ly X W regs mem md k l PREX HNB Hl Hlne.
eapply amreal_mono; [| exact (enq_hit_xs inst ly X W regs mem md k l PREX HNB Hl Hlne)].
intros r W' c' [L _]. exact L.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The internal allocator's contract, with the raw frame the caller must pass on: CLrefill0.tfib_refill_specR
   (a Theorem Labs lane's CLrefillR proves it for cgif_file).  The released AFl1.tfib_refill_spec frames the view only
   (YG0d.acall_post), so Enqueue's new-batch miss arm, which calls Refill in the middle of its walk, needs the
   stronger form. *)

(* The new-batch arm with an empty batch cache: AFh5.segR1, the internal allocator, AFh6.segT + AFg6.FINR. *)
Theorem enq_miss_xs : CLrefill0.tfib_refill_specR B -> forall inst ly X W regs mem md k,
CLenq.enq_pre_x tfibsegs B (ARX_cgif B) inst ly X W regs mem md k ->
need_new_batch (st_qthread X) = true ->
pc_chunks (cache X kBatchClass) = [] ->
amreal tfibsegs (enqueue k X) W (cfg_at tfibsegs A_Enqueue regs mem md)
(enq_leaf_xs inst ly X W regs mem md k).
Proof.
intros R1R inst ly X W regs mem md k PREX HNB Hl0.
pose proof (enq_pre_of_x inst ly X W regs mem md k PREX) as ENQ.
pose proof (inst_of_x inst ly X W regs mem md k PREX) as Hinst.
assert (HTSD : ly_tsd ly = TFIB_TSD).
{ pose proof (AFg6.M B ly X W regs mem md k ENQ) as M0. rewrite (am_tsd B ly X _ M0). exact (ts_tsd _ TB). }
apply (amreal_enqueue_nb k X W _ _ HNB).
unfold cfg_at, A_Enqueue. rewrite <- (AFg4.wvb_self md) at 1.
apply amreal_after_SRr. eapply SRr_mono;
[exact (AFh5.segR1 W ly regs mem md (sptr_addr B ly (ck_user k)) (ck_n k) (st_qthread X) 0 0
   (AFfq.jst ly W mem) (m_vm_materialized md)
   (AFg6.FH0_ok B TB ly X W regs mem md k ENQ HNB Hl0) eq_refl)|].
intros W' c' _ HC.
destruct HC as (-> & regs1 & mem1 & mat & -> & R_ra & R_sp & R_gp & R_tp & R_a0 & R_a1 & R_a2 & R_a3 &
  R_s0 & R_s1 & R_s2 & R_s3 & R_s4 & R_s5 & R_hi & MQ1 & PR1 & VALS).
cbv zeta in VALS. destruct VALS as (V1 & V2 & V3 & V4 & V5 & V6 & F1 & F2 & F3 & F4 & F5 & F6 & F7).
pose proof (R1R ly X W regs1 mem1 (with_vm_backing (m_vm_lazy md) mat md) kBatchClass
  (AFg6.REFILL_PRE B ly X W regs mem md k ENQ Hl0 regs1 mem1 mat R_ra R_sp R_gp R_tp R_a0 R_a1 R_a2 R_a3
     MQ1 PR1 V1 V2 V3 V4 V5 V6)) as RR.
unfold cfg_at, A_Refill in RR.
pose proof (AFg6.refill_tree_apostg (as_universe B) 1 0 0 X kBatchClass
  (AFg6.WfX1 B ly X W regs mem md k ENQ) ltac:(unfold kBatchClass; lia) ltac:(lia)
  (proj1 (proj2 (proj1 (proj2 (proj2 (proj2 ENQ))))))) as APOST.
pose proof (amreal_apostg tfibsegs (refill_tree kBatchClass X) _ W _ _ APOST RR) as RR2. clear RR.
eapply amreal_mono; [|exact RR2]. cbv beta.
intros [[] X1] W5 c5 [(WX1 & RO & CI & NE1) [HL HRAW]]. cbn [fst snd] in WX1, RO, CI, NE1, HL, HRAW.
destruct HL as (regs' & mem' & md' & -> & POST & HA0).
destruct HRAW as (regsR & memR & mdR & HcR & FRraw).
assert (EmR : memR = mem').
{ pose proof (cfg_mem_eq _ _ HcR) as E. cbn in E. symmetry. exact E. }
rewrite EmR in FRraw.
pose proof RO as RO'. destruct RO' as (Rck & _ & _ & _ & Rqt & Rqg & Rfs & _).
unfold enq_after_refill. cbn [snd].
destruct (pc_chunks (cache X1 kBatchClass)) as [|o1 l1'] eqn:El1.
- exfalso. apply NE1. first [reflexivity | exact El1].
- unfold cfg_at, raZ. rewrite R_ra. unfold w64 at 1.
  rewrite unsigned_lit_small by (pose proof (u64_range (getr regs 1)); lia).
  rewrite <- (AFg4.wvb_self md') at 1.
  assert (HA0' : getr regs' 10 = w64 1) by (rewrite HA0; cbn [snd]; rewrite El1; reflexivity).
  eapply SRr_mono;
  [exact (AFh6.segT W5 ly regs' mem' md' (sptr_addr B ly (ck_user k)) (ck_n k) (st_qthread X1)
     (AFg6.cnt1 o1 l1') (AFg6.coff1 o1 l1') (AFfq.jst ly W5 mem')
     (bv_unsigned (getr regs 1)) (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9))
     (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)) (bv_unsigned (getr regs 20))
     (bv_unsigned (getr regs 21)) (m_vm_materialized md')
     (AFg6.FHR_ok B TB ly X W regs mem md k ENQ HNB regs1 mem1 mat R_sp R_tp R_s0 R_s1 R_s2 R_s3 R_s5
        PR1 F1 F2 F3 F4 F5 F6 F7 W5 regs' mem' md' X1 POST RO HA0' o1 l1' El1))|].
  intros W6 c6 _ HR6.
  pose proof (AFg6.FINR B TB ly X W regs mem md k ENQ HNB Hl0 HTSD regs1 mem1 mat R_sp R_gp R_tp R_hi
    MQ1 PR1 V1 V2 V3 V4 V5 V6 W5 regs' mem' md' X1 POST RO CI o1 l1' El1 W6 c6 HR6) as LEAF.
  destruct HR6 as (HWW6 & regs6 & mem6 & mat6 & Hc6 & Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & QCS & MEQ6 & PRESW6 & VALS6).
  destruct LEAF as (regsL & memL & mdL & nb & HcL & POSTL & HqtL & HnbmL & HchL & HqgL & HfsL).
  assert (Em : memL = mem6).
  { pose proof (cfg_mem_eq _ _ (eq_trans (eq_sym HcL) Hc6)) as E. cbn in E. exact E. }
  assert (FRs : forall x : word, ~ aowned B ly X (bv_unsigned x) ->
    ~ (spZ regs - CLenq.QSTACK_G <= bv_unsigned x < spZ regs) -> memL x = mem x).
  { intros x NO NS.
    assert (Ha : 0 <= bv_unsigned x < 2 ^ 64) by (apply u64_range).
    assert (NO1 : ~ aowned B ly X1 (bv_unsigned x))
      by (intros O; apply NO; exact (AFg6.aowned_same B ly X X1 (bv_unsigned x) Rck Rfs O)).
    assert (NDS : ~ AFf2.DS (bv_unsigned (getr regs 2)) (bv_unsigned x))
      by (intros O; apply NS; unfold spZ, CLenq.QSTACK_G, AFf2.DS, QSTACK in *; exact O).
    assert (NDX : ~ AFf2.D ly X1 (o1 :: l1') (bv_unsigned (getr regs 2)) (bv_unsigned x)).
    { intros HD. destruct (AFf2.D_owned B ly X1 (aview tfibsegs (w_H W5) mem') (proj1 (proj1 POST)) k CI
        (o1 :: l1') El1 ltac:(discriminate) (bv_unsigned (getr regs 2))
        (AFg6.HSP B ly X W regs mem md k ENQ) (bv_unsigned x) (proj1 Ha) HD) as [O|O];
        [exact (NO1 O) | exact (NDS O)]. }
    rewrite Em.
    (* the tail segment: its window is inside D *)
    rewrite (MEQ6 x ltac:(intros HW; apply NDX; unfold AFf2.D, AFf2.DT, AFf2.DN, AFf2.DL, AFf2.DS;
      unfold AFgr.WIN, AFgr.WINT, AFgr.WINA, AFgr.NBv, AFgr.QLv, AFg6.cnt1, AFg6.coff1 in HW;
      unfold AFf2.QLv;
      destruct HW as [HW|[[_ HW]|[Hq HW]]];
      [left; exact HW | right; left; lia | right; right; left; split; [exact Hq | first [exact HW | lia]]])).
    (* the internal allocator's call *)
    assert (SP1 : spZ regs1 = bv_unsigned (getr regs 2) - 64).
    { unfold spZ. rewrite R_sp. unfold w64. apply unsigned_lit_small.
      pose proof (u64_range (getr regs 2)) as U.
      pose proof (AFg6.HSP B ly X W regs mem md k ENQ) as HSP0.
      pose proof (AFg6.HI0 B ly X W regs mem md k ENQ) as HI0.
      destruct HI0 as (_ & _ & _ & _ & hS1 & _).
      clear - U HSP0 hS1. unfold QSTACK, kHighMemBeg in *. lia. }
    assert (NSC : ~ (spZ regs1 - RSTACK <= bv_unsigned x < spZ regs1)).
    { rewrite SP1. intros O. apply NS. unfold spZ, CLenq.QSTACK_G, QSTACK, RSTACK in *.
      clear - O. lia. }
    rewrite (FRraw x NO NO1 NSC).
    (* the first segment *)
    apply MQ1. intros HW0. unfold AFgq.WIN0 in HW0. destruct HW0 as [HW0|HW0].
    - apply NS. unfold spZ, CLenq.QSTACK_G, QSTACK in *. clear - HW0. lia.
    - apply NDX. unfold AFf2.D. left. unfold AFf2.DT. unfold AFgq.WINT in HW0.
      first [exact HW0 | unfold t_qc, t_cache, t_cache_stats in *; clear - HW0; lia]. }
  split; [| exists regsL, memL, mdL; split; [exact HcL | exact FRs]].
  exists regsL, memL, mdL, nb.
  split; [exact HcL|].
  split.
  { destruct POSTL as (AR' & LLE & WLE & ARP & SIO & AGV & PRS).
    split; [split; [exact Hinst | exact AR']|].
    split; [exact LLE|]. split; [exact WLE|]. split; [exact ARP|]. split; [exact SIO|].
    split; [exact AGV|]. split; [| exact PRS].
    intros x NO NO' NS NE. apply FRs; [exact NO|]. intros O. apply NS. unfold ascratch. left. exact O. }
  split; [exact HqtL|]. split; [exact HnbmL|]. split; [exact HchL|]. split; [exact HqgL|]. exact HfsL.
Qed.

Theorem enq_miss_x : CLrefill0.tfib_refill_specR B -> forall inst ly X W regs mem md k,
CLenq.enq_pre_x tfibsegs B (ARX_cgif B) inst ly X W regs mem md k ->
need_new_batch (st_qthread X) = true ->
pc_chunks (cache X kBatchClass) = [] ->
amreal tfibsegs (enqueue k X) W (cfg_at tfibsegs A_Enqueue regs mem md)
(CLenq.enq_leaf_x tfibsegs B (ARX_cgif B) (aowned B) inst ly X W regs mem md k).
Proof.
intros R1R inst ly X W regs mem md k PREX HNB Hl0.
eapply amreal_mono; [| exact (enq_miss_xs R1R inst ly X W regs mem md k PREX HNB Hl0)].
intros r W' c' [L _]. exact L.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The generic contract at cgif_file, both values of need_new_batch.                                                *)
Theorem enqueue_spec_x_room : CLenq.enqueue_spec_x tfibsegs B (ARX_cgif B) (aowned B) A_Enqueue false.
Proof. intros inst ly X W regs mem md k HNB PREX. exact (enq_room_x inst ly X W regs mem md k PREX HNB). Qed.

Theorem enqueue_spec_x_new : CLrefill0.tfib_refill_specR B ->
CLenq.enqueue_spec_x tfibsegs B (ARX_cgif B) (aowned B) A_Enqueue true.
Proof.
intros R1R inst ly X W regs mem md k HNB PREX.
destruct (pc_chunks (cache X kBatchClass)) as [|o l0] eqn:E.
- exact (enq_miss_x R1R inst ly X W regs mem md k PREX HNB E).
- exact (enq_hit_x inst ly X W regs mem md k (o :: l0) PREX HNB E ltac:(discriminate)).
Qed.

Theorem enqueue_spec_x_cgif : CLrefill0.tfib_refill_specR B ->
forall nbq, CLenq.enqueue_spec_x tfibsegs B (ARX_cgif B) (aowned B) A_Enqueue nbq.
Proof. intros R1R [|]; [exact (enqueue_spec_x_new R1R) | exact enqueue_spec_x_room]. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The sub-interface fields that do not depend on the consumer's lpost / QB / L24 / EP.                             *)
Lemma es_inst_cgif : forall inst inst' ly ly' X X' W W' mem mem' md md',
ARX_cgif B inst ly X W mem md -> ARX_cgif B inst' ly' X' W' mem' md' -> inst = inst'.
Proof. intros inst inst' ly ly' X X' W W' mem mem' md md' [E1 _] [E2 _]. congruence. Qed.

Lemma es_qbytes_cgif : forall inst ly X W mem md, ARX_cgif B inst ly X W mem md ->
val_mem tfibsegs (mrestrict (w_H W) mem) (ly_T ly + t_qc + 24) 8 (qc_bytes (st_qthread X)).
Proof.
intros inst ly X W mem md [_ HAR].
exact (proj2 (proj2 (proj2 (AFfq.root_vals B ly X W mem (proj1 HAR))))).
Qed.

Lemma es_owned_cgif : forall ly X X' a, st_chunks X' = st_chunks X -> st_fs X' = st_fs X ->
aowned B ly X' a -> aowned B ly X a.
Proof. intros ly X X' a H1 H2 H3. exact (AFg6.aowned_same B ly X X' a H1 H2 H3). Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The model step of Enqueue's push, for the consumer's post.                                                       *)

(* What the push does to the thread cache's bytes, to the queued bytes and to the batch count. *)
Lemma push_facts : forall q k nb,
match nb with None => need_new_batch q = false | Some _ => need_new_batch q = true end ->
qc_bytes (qc_push q k nb) = qc_bytes q + ck_n k + (match nb with None => 0 | Some _ => kBatchBytes end) /\
items_n (flat_map b_items (qc_list (qc_push q k nb))) = items_n (flat_map b_items (qc_list q)) + ck_n k /\
(length (qc_list (qc_push q k nb)) <= S (length (qc_list q)))%nat.
Proof.
intros q k [b|] HNB.
- cbn [qc_push qc_bytes qc_list]. rewrite flat_map_app, items_n_app. cbn [flat_map b_items items_n fold_right app].
  rewrite length_app. cbn [length]. split; [lia|]. split; [lia | lia].
- unfold need_new_batch in HNB. destruct (rev (qc_list q)) as [|lastb initr] eqn:ER; [discriminate|].
  assert (EQ : qc_list q = rev initr ++ [lastb])
    by (rewrite <- (rev_involutive (qc_list q)), ER; reflexivity).
  unfold qc_push. rewrite ER. cbn [qc_bytes qc_list].
  rewrite EQ. rewrite ?flat_map_app, ?items_n_app, ?length_app.
  cbn [flat_map b_items items_n fold_right app length].
  rewrite ?items_n_app, ?app_nil_r.
  cbn [items_n fold_right app length].
  split; [lia|]. split; [lia | lia].
Qed.

(* The caller's facts about the pre-state that the enqueue pre does not carry (CLenq's [EP]), for cgif_file: the
   tight global bound, the quarantine debt of the chunk being queued, the room for one more batch and the batch
   count below the drain contract's bound [L24]. *)
Definition EPc (L24 : Z) (X : astate) (k : chunk) : Prop :=
qc_bytes (st_qglobal X) <= kQuarantineMax /\ quar_n X <= queued_n X + ck_n k /\
qc_bytes (st_qthread X) + ck_n k + kBatchBytes <= 2 ^ 29 /\
Z.of_nat (length (all_batches X)) + 1 <= L24.

Lemma es_lpost_cgif : forall L24 inst ly X W mem md k nb X',
ARX_cgif B inst ly X W mem md -> EPc L24 X k -> In k (st_chunks X) -> ck_state k = CQuarantined ->
~ In (ck_beg k) (map ck_beg (q_items X)) -> qloosem X ->
match nb with None => need_new_batch (st_qthread X) = false | Some _ => need_new_batch (st_qthread X) = true end ->
st_qthread X' = qc_push (st_qthread X) k nb -> st_chunks X' = st_chunks X -> st_qglobal X' = st_qglobal X ->
qc_bytes (st_qthread X') <= kQuarantineCacheMax -> qtight X'.
Proof.
intros L24 inst ly X W mem md k nb X' _ (EG & EQ & _ & _) _ _ _ _ HNB Hqt Hch Hqg Hle.
destruct (push_facts (st_qthread X) k nb HNB) as (_ & PI & _).
split; [exact Hle|]. split; [rewrite Hqg; exact EG|].
unfold quar_n in *. rewrite Hch. rewrite queued_n_eq in EQ |- *.
rewrite Hqt, Hqg, PI. lia.
Qed.

Lemma es_qb_cgif : forall L24 inst ly X W mem md k nb X',
ARX_cgif B inst ly X W mem md -> EPc L24 X k -> In k (st_chunks X) -> ck_state k = CQuarantined ->
~ In (ck_beg k) (map ck_beg (q_items X)) -> qloosem X ->
Z.of_nat (length (all_batches X)) + 1 <= st_nev X ->
match nb with None => need_new_batch (st_qthread X) = false | Some _ => need_new_batch (st_qthread X) = true end ->
st_qthread X' = qc_push (st_qthread X) k nb -> st_chunks X' = st_chunks X -> st_qglobal X' = st_qglobal X ->
kQuarantineCacheMax < qc_bytes (st_qthread X') ->
qloose X' /\ Z.of_nat (length (all_batches X')) <= L24.
Proof.
intros L24 inst ly X W mem md k nb X' _ (EG & EQ & ET & EL) _ _ _ _ _ HNB Hqt Hch Hqg _.
destruct (push_facts (st_qthread X) k nb HNB) as (PB & PI & PL).
split.
- split; [rewrite Hqt, PB; destruct nb; unfold kBatchBytes in *; lia|].
  split; [rewrite Hqg; unfold kQuarantineMax in *; lia|].
  unfold quar_n in *. rewrite Hch. rewrite queued_n_eq in EQ |- *.
  rewrite Hqt, Hqg, PI. lia.
- unfold all_batches in *. rewrite Hqt, Hqg. rewrite length_app in *.
  clear - PL EL. lia.
Qed.

(* The sub-interface at cgif_file: ARX_cgif, aowned, lpost = qtight, QB = qloose, the batch bound [L24] and the
   caller's facts [EPc L24]. *)
Theorem EnqSub_cgif : forall L24,
CLenq.EnqSub tfibsegs (ARX_cgif B) (aowned B) qtight qloose L24 (EPc L24).
Proof.
intros L24. constructor.
- exact es_inst_cgif.
- exact es_qbytes_cgif.
- exact es_owned_cgif.
- exact (es_lpost_cgif L24).
- exact (es_qb_cgif L24).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* DGif0.DIface's [di_enqueue] for cgif_file.                                                                        *)

(* The one walk-side obligation the callee contract cannot carry: at Put's call of Enqueue the relation must hold
   again, at the quarantined state [qx S k z tr] and at the memory [dmem_m] describes (the released walk does the
   same step in YFg1.ENQ_PRE, from YFfl.free_mid_ARm).  It belongs to the Deallocate instance, which owns the
   walk's geometry; everything else of di_enqueue is below. *)
Definition enq_bridge (L24 : Z) : Prop :=
forall inst ly S W mem0 md0 p n tr k z hb1 sp0 (regs : bvmap 5 word) (mem : word -> option byte) mat,
ARX_cgif B inst ly S W mem0 md0 -> rpre_dealloc_cgif S n -> fpre_cgif ly S W mem0 p n -> In (p, n) (blocks S) ->
tr_admit (as_universe B) S tr ->
find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
ly_stk_lo ly + DFSTACK <= sp0 -> sp0 <= ly_stk_hi ly -> ly_bot ly < sp0 -> sp0 mod 16 = 0 ->
0 <= hb1 < 256 -> val_mem tfibsegs (mrestrict (w_H W) mem0) (sptr_addr B ly p - 16) 4 (2 + 256 * hb1) ->
dmem_m W ly sp0 mem0 (sptr_addr B ly p) (req_size n) hb1 (CLdepot.dpost_x tfibsegs B inst ly S W tr z) mem ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs -> spZ regs = sp0 - 80 ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 (ly_T ly + t_qc) -> getr regs 11 = w64 (ly_T ly + t_cache) ->
getr regs 13 = w64 (sptr_addr B ly p - kChunkHeaderSize) -> getr regs 14 = w64 (req_size n) ->
CLenq.enq_pre_x tfibsegs B (ARX_cgif B) inst ly (qx S k z tr) W regs mem
  (with_vm_backing (m_vm_lazy md0) mat md0) (qk k) /\ EPc L24 (qx S k z tr) (qk k).

Theorem di_enqueue_cgif : forall L24, enq_bridge L24 -> CLrefill0.tfib_refill_specR B ->
forall inst ly S W mem0 md0 p n tr k z hb1 sp0 (regs : bvmap 5 word) (mem : word -> option byte) mat,
ARX_cgif B inst ly S W mem0 md0 -> rpre_dealloc_cgif S n -> fpre_cgif ly S W mem0 p n -> In (p, n) (blocks S) ->
tr_admit (as_universe B) S tr ->
find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
ly_stk_lo ly + DFSTACK <= sp0 -> sp0 <= ly_stk_hi ly -> ly_bot ly < sp0 -> sp0 mod 16 = 0 ->
0 <= hb1 < 256 -> val_mem tfibsegs (mrestrict (w_H W) mem0) (sptr_addr B ly p - 16) 4 (2 + 256 * hb1) ->
dmem_m W ly sp0 mem0 (sptr_addr B ly p) (req_size n) hb1 (CLdepot.dpost_x tfibsegs B inst ly S W tr z) mem ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs -> spZ regs = sp0 - 80 ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 (ly_T ly + t_qc) -> getr regs 11 = w64 (ly_T ly + t_cache) ->
getr regs 13 = w64 (sptr_addr B ly p - kChunkHeaderSize) -> getr regs 14 = w64 (req_size n) ->
amreal tfibsegs (enqueue (qk k) (qx S k z tr)) W
  (cfg_at tfibsegs A_Enqueue regs mem (with_vm_backing (m_vm_lazy md0) mat md0))
  (CLenq.di_enq_post tfibsegs B (ARX_cgif B) (aowned B) qtight qloose L24 inst ly (qx S k z tr) W regs mem
     (with_vm_backing (m_vm_lazy md0) mat md0) (qk k)).
Proof.
intros L24 BR R1R inst ly S W mem0 md0 p n tr k z hb1 sp0 regs mem mat
  HARX HRP HFP HBLK HU HFU HCK HS1 HS2 HS3 HS4 HHB HHDR HMEM HRA HRA4 HSP HGP HTP HA0 HA1 HA3 HA4.
destruct (BR inst ly S W mem0 md0 p n tr k z hb1 sp0 regs mem mat
  HARX HRP HFP HBLK HU HFU HCK HS1 HS2 HS3 HS4 HHB HHDR HMEM HRA HRA4 HSP HGP HTP HA0 HA1 HA3 HA4) as [PREX HEP].
eapply amreal_mono;
[| exact (enqueue_spec_x_cgif R1R (need_new_batch (st_qthread (qx S k z tr))) inst ly (qx S k z tr) W regs mem
     (with_vm_backing (m_vm_lazy md0) mat md0) (qk k) eq_refl PREX)].
cbv beta. intros r W' c' LEAF.
exact (CLenq.di_enq_post_of_leaf tfibsegs B (ARX_cgif B) (aowned B) qtight qloose L24 (EPc L24)
  (EnqSub_cgif L24) inst ly (qx S k z tr) W regs mem (with_vm_backing (m_vm_lazy md0) mat md0) (qk k)
  r W' c' HEP PREX LEAF).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The internal allocator's premise discharged (CLrefillR, a Theorem Labs lane): the contract and the interface field with no
   callee premise left. *)
Theorem refill_specR_cgif : CLrefill0.tfib_refill_specR B.
Proof. exact (CLrefillR.tfib_refill_okR B TB). Qed.

Theorem enqueue_spec_x_ok : forall nbq, CLenq.enqueue_spec_x tfibsegs B (ARX_cgif B) (aowned B) A_Enqueue nbq.
Proof. exact (enqueue_spec_x_cgif refill_specR_cgif). Qed.

Theorem di_enqueue_ok : forall L24, enq_bridge L24 ->
forall inst ly S W mem0 md0 p n tr k z hb1 sp0 (regs : bvmap 5 word) (mem : word -> option byte) mat,
ARX_cgif B inst ly S W mem0 md0 -> rpre_dealloc_cgif S n -> fpre_cgif ly S W mem0 p n -> In (p, n) (blocks S) ->
tr_admit (as_universe B) S tr ->
find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
ly_stk_lo ly + DFSTACK <= sp0 -> sp0 <= ly_stk_hi ly -> ly_bot ly < sp0 -> sp0 mod 16 = 0 ->
0 <= hb1 < 256 -> val_mem tfibsegs (mrestrict (w_H W) mem0) (sptr_addr B ly p - 16) 4 (2 + 256 * hb1) ->
dmem_m W ly sp0 mem0 (sptr_addr B ly p) (req_size n) hb1 (CLdepot.dpost_x tfibsegs B inst ly S W tr z) mem ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs -> spZ regs = sp0 - 80 ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 (ly_T ly + t_qc) -> getr regs 11 = w64 (ly_T ly + t_cache) ->
getr regs 13 = w64 (sptr_addr B ly p - kChunkHeaderSize) -> getr regs 14 = w64 (req_size n) ->
amreal tfibsegs (enqueue (qk k) (qx S k z tr)) W
  (cfg_at tfibsegs A_Enqueue regs mem (with_vm_backing (m_vm_lazy md0) mat md0))
  (CLenq.di_enq_post tfibsegs B (ARX_cgif B) (aowned B) qtight qloose L24 inst ly (qx S k z tr) W regs mem
     (with_vm_backing (m_vm_lazy md0) mat md0) (qk k)).
Proof. intros L24 BR. exact (di_enqueue_cgif L24 BR refill_specR_cgif). Qed.
End b.
End a.
