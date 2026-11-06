(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/YGcfInstEnqTrcgif.v (commit 1223f55a2a51, CfF1 round-2 re-fit; file sha256 769598b6107a) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/YGcfInstEnqTrreply.v at commit f303438be5b, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), taken by path: no numeral of it names an image address that differs in fuzz_reply.asan-ubsan. *)
(* Theorem Labs, 2026-10-30 (lane F1 of the generic cf instance layer; integrator ReallocPrimary).
   cgif_file's image: the TRANSPORT fields of lane B2's frame-generic Enqueue interface (EnqGbase.v, taken by path)
   at the cf instance, i.e. at the layer's walk relation YGcfInstBase.ARX_cf B IOK Hp, owned set aowned B and call
   premise YGcfInstEnq.enq_pre_cf, with cgif's walk posts and windows (the same texts as B2's EnqGcgif.v).
   rule 24: no function proved (kind: interface-instance discharge: the relation at an Enqueue arm's post).

   ROOM arm (EnqIfaceRoom):
   - [ir_post_cf]: the relation at the post state, from the walk's post (YFg4cf.FINPH_cf, through
     YFf1cf.enq_finp_ARmcf; Wf_cf of the end state from YGcfInstEnqG.enq_room_wf_cf);
   - [ir_owned_cf]: every byte of the walk's window is allocator-owned or Enqueue's stack scratch (YFf1cf.D_owned_cf);
   - [ir_safe_cf]: every byte of the walk's window is memnorm-safe (MemnormLoc.YFf1_D_safe's script over ARmcf);
   - [ir_frame_cf]: the walk's post returns to the caller and keeps every byte outside its window (at_RETP);
   - [iface_room_cf_cgif]: the whole record, at B2's strict block-size parameter := YGcfInstEnqG.ENQ_NMAX_STRICT
     (the layer's NMAXD is the inclusive guard `ck_n k <= kQuarantineMax`), from the unit's walk field [ir_walk] (the
     walk at the inclusive bound is the unit's relocated walk, not this file: YFgp.v:96 bounds cgif's at < 2 ^ 28).
   HIT arm (EnqIfaceHit): [ih_post_cf] (YFg5cf.FINQH_cf through YFf2cf.enq_fin_ARmcf; Wf_cf of the end state from
   YGcfInstEnqG.enq_hit_wf_cf), [ih_owned_cf] (YFf2cf.D_owned_cf), [ih_safe_cf] (MemnormLoc.YFf2_D_safe's script over
   ARmcf), [ih_frame_cf] (at_RETQ), and [iface_hit_cf_cgif] at ENQ_NMAX_STRICT, RMAXD := kFreeArrayOffset and
   Shit := YGcfInstEnqG.Shit_cf (ih_nmax / ih_rmaxd_ok / ih_rmax / ih_shape from YGcfInstEnqG), from the unit's walk
   field [ih_walk].
   IMAGE-SPECIFIC (cgif's image): each unit writes its own twin over its own walk posts (preset A' / B': A11; reply
   A / B: lane W), with its relocations of YFf1cf.v / YFg4cf.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
(* The cgif image instances first, as DGif1.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif2reply ImgBaseAG ImgBaseDG DGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YFeq YFew YFex YFfu YFfq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YFfp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YFgp YFgq YFh3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0qcf YG0scf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfInstBase YGcfInstEnq YGcfInstEnqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YFf1cf YFg4cf YFf2cf YFg5cf YFh4 EnqGbase CLenq MemnormT MemnormLoc MemnormHitG.
From Stdlib Require Import List.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Local Open Scope am_scope.

(* MemnormLoc.YFf1_D_safe (MemnormLoc.v:104-118) over ARmcf. *)
Lemma YFf1cf_D_safe : forall (B : asyms) (ly : alayout) (X : astate) (rd : reader) (Hp : list Z) (M : ARmcf B ly X Hp rd)
  (lb : batch) (initr : list batch),
  rev (qc_list (st_qthread X)) = lb :: initr -> Z.of_nat (length (b_items lb)) < kBatchSlots ->
  forall sp : Z, ly_stk_lo ly + YFew.QSTACK <= sp <= ly_stk_hi ly -> img_cover ly ->
  forall x : word, YFf1cf.D ly lb sp (bv_unsigned x) -> MemnormT.mn_safe tfibsegs x.
Proof.
intros B ly X rd Hp M lb initr Hrev Hroom sp Hsp IMG x Hd.
pose proof (YFf1cf.HIGH B ly X rd Hp M lb initr Hrev Hroom sp Hsp IMG)
  as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12).
pose proof ASAN_CEIL_range as [CR _].
destruct (YFf1cf.D_cases B ly X rd Hp M lb initr Hrev Hroom sp Hsp IMG _ Hd) as [C|[C|C]].
- destruct C as [C _]. exact (MemnormLoc.mn_safe_zone3 _ _ x H3 C H4).
- destruct C as [C _]. apply MemnormLoc.mn_safe_ceil. unfold kHighMemBeg, kImgEnd in *. lia.
- apply MemnormHitG.mn_safe_high. unfold kHighMemBeg, kHighMemEnd, kImgEnd, TASK_SIZE in *. lia.
Qed.

(* MemnormLoc.YFf2_D_safe (MemnormLoc.v:134-149) over ARmcf. *)
Lemma YFf2cf_D_safe : forall (B : asyms) (ly : alayout) (X : astate) (rd : reader) (Hp : list Z) (M : ARmcf B ly X Hp rd),
  st_cache_inited X = true -> forall l : list Z, pc_chunks (cache X kBatchClass) = l -> l <> [] ->
  forall sp : Z, ly_stk_lo ly + YFew.QSTACK <= sp <= ly_stk_hi ly -> img_cover ly ->
  forall x : word, YFf2cf.D ly X l sp (bv_unsigned x) -> MemnormT.mn_safe tfibsegs x.
Proof.
intros B ly X rd Hp M Hci l Hl Hlne sp Hsp IMG x Hd.
pose proof (YFf2cf.HIGH B ly X rd Hp M Hci l Hl Hlne sp Hsp IMG)
  as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
pose proof ASAN_CEIL_range as [CR _].
destruct (YFf2cf.D_cases B ly X rd Hp M Hci l Hl Hlne sp Hsp IMG _ Hd) as [C|[C|[C|C]]].
- destruct C as [C _]. exact (MemnormLoc.mn_safe_zone3 _ _ x H3 C H4).
- destruct C as [C _]. apply MemnormLoc.mn_safe_ceil. unfold kHighMemBeg, kImgEnd in *. lia.
- destruct C as (lb & initr & Hr & C). destruct (H11 lb initr Hr) as [Q1 Q2]. apply MemnormLoc.mn_safe_ceil.
  unfold kBatchBytes, kHighMemBeg, kImgEnd in *. lia.
- apply MemnormHitG.mn_safe_high. unfold kHighMemBeg, kHighMemEnd, kImgEnd, TASK_SIZE in *. lia.
Qed.

Section b.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (IOK : Z -> Prop) (Hp : list Z).
Local Notation ARX := (ARX_cf B IOK Hp).
Local Notation EP := (enq_pre_cf B ARX).

(* cgif's walk post and window of the room arm (B2's EnqGcgif.v ARETr_cgif / WINr_cgif, the same texts). *)
Definition ARETr_cf (ly : alayout) (X : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (k : chunk) : world tfibsegs -> config -> Prop :=
YFgp.at_RETP W ly regs mem md (sptr_addr B ly (ck_user k)) (ck_n k)
  (YFg4cf.QLv ly X) (YFgq.QBv (st_qthread X)) (YFg4cf.CNTv X) (YFg4cf.BSZv X).

Definition WINr_cf (ly : alayout) (regs : bvmap 5 word) (X : astate) (a : Z) : Prop :=
YFgp.WIN ly regs (YFg4cf.QLv ly X) (YFg4cf.CNTv X) a.

(* The room arm's window lies in YFf1cf.D (B2's win_D_room, EnqGcgif.v:121-130). *)
Lemma win_D_room_cf : forall ly X regs a,
WINr_cf ly regs X a -> YFf1cf.D ly (YFg4cf.lb X) (bv_unsigned (getr regs 2)) a.
Proof.
intros ly X regs a HW.
unfold YFf1cf.D, YFf1cf.DT, YFf1cf.DL, YFf1cf.DS, YFf1cf.QLv, YFf1cf.CNTv.
unfold WINr_cf, YFgp.WIN, YFgp.SLv in HW. unfold YFg4cf.QLv, YFg4cf.CNTv in HW.
destruct HW as [HW|[HW|[HW|HW]]];
  [do 2 right; clear - HW; unfold QSTACK in *; lia | left; exact HW | right; left; left; exact HW
  | right; left; right; lia].
Qed.

(* The return configuration, in the shape the interface asks for (B2's cfg_ret). *)
Lemma cfg_ret_cf : forall (regs regs' : bvmap 5 word) (mem' : word -> option byte) (mdx : Model),
mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) mdx = cfg_at tfibsegs (raZ regs) regs' mem' mdx.
Proof. intros regs regs' mem' mdx. unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.

(* ir_post *)
Theorem ir_post_cf : forall inst ly X W regs mem md k W' c',
EP inst ly X W regs mem md k -> need_new_batch (st_qthread X) = false ->
ARETr_cf ly X W regs mem md k W' c' ->
EnqGbase.enq_leaf_g0 tfibsegs B ARX (aowned B) inst ly X W regs mem md k (tt, EnqGbase.Sroom X k) W' c'.
Proof.
intros inst ly X W regs mem md k W' c' PRE HNB HR.
exact (YFg4cf.FINPH_cf B TB IOK Hp inst ly X W regs mem md k PRE HNB W' c' HR).
Qed.

(* ir_frame *)
Theorem ir_frame_cf : forall ly X W regs mem md k W' c',
ARETr_cf ly X W regs mem md k W' c' ->
exists regs' mem' md', c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
  (forall x : word, ~ WINr_cf ly regs X (bv_unsigned x) -> mem' x = mem x).
Proof.
intros ly X W regs mem md k W' c' HR.
destruct HR as (HWW & regs2 & mem2 & mat2 & Hc2 & CS & MEQ' & PRESW & VALS).
exists regs2, mem2, (with_vm_backing (m_vm_lazy md) mat2 md).
split; [rewrite Hc2; apply cfg_ret_cf | exact MEQ'].
Qed.

(* ir_owned *)
Theorem ir_owned_cf : forall inst ly X W regs mem md k a,
EP inst ly X W regs mem md k -> need_new_batch (st_qthread X) = false -> 0 <= a < 2 ^ 64 ->
WINr_cf ly regs X a -> aowned B ly X a \/ (spZ regs - CLenq.QSTACK_G <= a < spZ regs).
Proof.
intros inst ly X W regs mem md k a PRE HNB Ha HW.
pose proof (win_D_room_cf ly X regs a HW) as HD.
destruct (YFf1cf.D_owned_cf B ly X (aview tfibsegs (w_H W) mem) Hp (YFg4cf.M B IOK Hp inst ly X W regs mem md k PRE)
  (YFg4cf.lb X) (YFg4cf.initr X) (YFg4cf.Hrev X HNB) (YFg4cf.Hroom B IOK Hp inst ly X W regs mem md k PRE HNB)
  (bv_unsigned (getr regs 2)) (YFg4cf.HSP B IOK Hp inst ly X W regs mem md k PRE)
  (YFg4cf.IMG B IOK Hp inst ly X W regs mem md k PRE) a (proj1 Ha) HD) as [O|O].
- left. exact O.
- right. unfold YFf1cf.DS in O. unfold spZ, CLenq.QSTACK_G, QSTACK in *. exact O.
Qed.

(* ir_safe *)
Theorem ir_safe_cf : forall inst ly X W regs mem md k (x : word),
EP inst ly X W regs mem md k -> need_new_batch (st_qthread X) = false ->
WINr_cf ly regs X (bv_unsigned x) -> MemnormT.mn_safe tfibsegs x.
Proof.
intros inst ly X W regs mem md k x PRE HNB HW.
pose proof (win_D_room_cf ly X regs (bv_unsigned x) HW) as HD.
exact (YFf1cf_D_safe B ly X (aview tfibsegs (w_H W) mem) Hp (YFg4cf.M B IOK Hp inst ly X W regs mem md k PRE)
  (YFg4cf.lb X) (YFg4cf.initr X) (YFg4cf.Hrev X HNB) (YFg4cf.Hroom B IOK Hp inst ly X W regs mem md k PRE HNB)
  (bv_unsigned (getr regs 2)) (YFg4cf.HSP B IOK Hp inst ly X W regs mem md k PRE)
  (YFg4cf.IMG B IOK Hp inst ly X W regs mem md k PRE) x HD).
Qed.

(* The room record at the cf instance, from the unit's walk at B2's strict parameter ENQ_NMAX_STRICT. *)
Theorem iface_room_cf_reply :
(forall inst ly X W regs mem md k,
  EP inst ly X W regs mem md k -> need_new_batch (st_qthread X) = false -> 1 <= ck_n k < ENQ_NMAX_STRICT ->
  SRr tfibsegs W (cfg_at tfibsegs dg_enqueue regs mem md) (ARETr_cf ly X W regs mem md k)) ->
EnqGbase.EnqIfaceRoom tfibsegs dg_enqueue B ARX (aowned B) EP ENQ_NMAX_STRICT ARETr_cf WINr_cf.
Proof.
intros WALK. constructor.
- exact (enq_nmax_cf B Hp ARX (ARX_cf_ARcf B IOK Hp)).
- exact WALK.
- exact ir_frame_cf.
- exact ir_post_cf.
- exact ir_owned_cf.
- exact ir_safe_cf.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* HIT arm.                                                                                                          *)

(* cgif's walk post and window of the hit arm (B2's EnqGcgif.v ARETh_cgif / WINh_cgif, the same texts). *)
Definition ARETh_cf (ly : alayout) (X : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (k : chunk) (l : list Z) : world tfibsegs -> config -> Prop :=
YFh4.at_RETQ W ly regs mem md (sptr_addr B ly (ck_user k)) (ck_n k) (st_qthread X)
  (Z.of_nat (length l)) (last l 0).

Definition WINh_cf (ly : alayout) (regs : bvmap 5 word) (X : astate) (l : list Z) (a : Z) : Prop :=
YFgq.WIN ly regs (st_qthread X) (Z.of_nat (length l)) (last l 0) a.

(* The hit arm's window lies in YFf2cf.D (B2's win_D_hit, EnqGcgif.v:133-146). *)
Lemma win_D_hit_cf : forall ly X regs l a,
WINh_cf ly regs X l a -> YFf2cf.D ly X l (bv_unsigned (getr regs 2)) a.
Proof.
intros ly X regs l a HW.
assert (ENB : YFgq.NBv ly (last l 0) = ly_space ly + (region_off kBatchClass + last l 0))
  by (unfold YFgq.NBv; lia).
unfold YFf2cf.D, YFf2cf.DT, YFf2cf.DN, YFf2cf.DL, YFf2cf.DS.
unfold WINh_cf, YFgq.WIN, YFgq.WINT, YFgq.WINA in HW. rewrite ENB in HW.
destruct HW as [HW|[HW|[[_ HW]|[Hq HW]]]].
- do 3 right. clear - HW. unfold QSTACK. lia.
- left. exact HW.
- right; left. exact HW.
- right; right; left. split; [exact Hq|]. unfold YFf2cf.QLv. unfold YFgq.QLv in HW. exact HW.
Qed.

(* ih_post *)
Theorem ih_post_cf : forall inst ly X W regs mem md k l W' c',
EP inst ly X W regs mem md k -> need_new_batch (st_qthread X) = true ->
pc_chunks (cache X kBatchClass) = l -> l <> [] ->
ARETh_cf ly X W regs mem md k l W' c' ->
EnqGbase.enq_leaf_g0 tfibsegs B ARX (aowned B) inst ly X W regs mem md k (tt, Shit_cf X k l) W' c'.
Proof.
intros inst ly X W regs mem md k l W' c' PRE HNB Hl Hlne HR.
exact (YFg5cf.FINQH_cf B TB IOK Hp inst ly X W regs mem md k PRE HNB l Hl Hlne W' c' HR).
Qed.

(* ih_frame *)
Theorem ih_frame_cf : forall ly X W regs mem md k l W' c',
ARETh_cf ly X W regs mem md k l W' c' ->
exists regs' mem' md', c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
  (forall x : word, ~ WINh_cf ly regs X l (bv_unsigned x) -> mem' x = mem x).
Proof.
intros ly X W regs mem md k l W' c' HR.
destruct HR as (HWW & regs2 & mem2 & mat2 & Hc2 & CS & MEQ' & PRESW & VALS).
exists regs2, mem2, (with_vm_backing (m_vm_lazy md) mat2 md).
split; [rewrite Hc2; apply cfg_ret_cf | exact MEQ'].
Qed.

(* ih_owned *)
Theorem ih_owned_cf : forall inst ly X W regs mem md k l a,
EP inst ly X W regs mem md k -> need_new_batch (st_qthread X) = true ->
pc_chunks (cache X kBatchClass) = l -> l <> [] -> 0 <= a < 2 ^ 64 ->
WINh_cf ly regs X l a -> aowned B ly X a \/ (spZ regs - CLenq.QSTACK_G <= a < spZ regs).
Proof.
intros inst ly X W regs mem md k l a PRE HNB Hl Hlne Ha HW.
pose proof (win_D_hit_cf ly X regs l a HW) as HD.
destruct (YFf2cf.D_owned_cf B ly X (aview tfibsegs (w_H W) mem) Hp (YFg5cf.M B IOK Hp inst ly X W regs mem md k PRE) k
  (YFg5cf.Hci B IOK Hp inst ly X W regs mem md k PRE l Hl Hlne) l Hl Hlne (bv_unsigned (getr regs 2))
  (YFg5cf.HSP B IOK Hp inst ly X W regs mem md k PRE) a (proj1 Ha) HD) as [O|O].
- left. exact O.
- right. unfold YFf2cf.DS in O. unfold spZ, CLenq.QSTACK_G, QSTACK in *. exact O.
Qed.

(* ih_safe *)
Theorem ih_safe_cf : forall inst ly X W regs mem md k l (x : word),
EP inst ly X W regs mem md k -> need_new_batch (st_qthread X) = true ->
pc_chunks (cache X kBatchClass) = l -> l <> [] ->
WINh_cf ly regs X l (bv_unsigned x) -> MemnormT.mn_safe tfibsegs x.
Proof.
intros inst ly X W regs mem md k l x PRE HNB Hl Hlne HW.
pose proof (win_D_hit_cf ly X regs l (bv_unsigned x) HW) as HD.
exact (YFf2cf_D_safe B ly X (aview tfibsegs (w_H W) mem) Hp (YFg5cf.M B IOK Hp inst ly X W regs mem md k PRE)
  (YFg5cf.Hci B IOK Hp inst ly X W regs mem md k PRE l Hl Hlne) l Hl Hlne (bv_unsigned (getr regs 2))
  (YFg5cf.HSP B IOK Hp inst ly X W regs mem md k PRE) (YFg5cf.IMG B IOK Hp inst ly X W regs mem md k PRE) x HD).
Qed.

(* The hit record at the cf instance, from the unit's walk at ENQ_NMAX_STRICT, RMAXD := kFreeArrayOffset. *)
Theorem iface_hit_cf_reply :
(forall inst ly X W regs mem md k l,
  EP inst ly X W regs mem md k -> need_new_batch (st_qthread X) = true ->
  pc_chunks (cache X kBatchClass) = l -> l <> [] ->
  1 <= ck_n k < ENQ_NMAX_STRICT -> rg_mapped_user (reg X kBatchClass) <= kFreeArrayOffset ->
  SRr tfibsegs W (cfg_at tfibsegs dg_enqueue regs mem md) (ARETh_cf ly X W regs mem md k l)) ->
EnqGbase.EnqIfaceHit tfibsegs dg_enqueue B ARX (aowned B) EP ENQ_NMAX_STRICT kFreeArrayOffset ARETh_cf WINh_cf Shit_cf.
Proof.
intros WALK. constructor.
- exact (enq_nmax_cf B Hp ARX (ARX_cf_ARcf B IOK Hp)).
- exact rmaxd_ok_cf.
- intros inst ly X W regs mem md k l PRE _ _ _. exact (enq_rmax_cf B ARX inst ly X W regs mem md k PRE).
- exact WALK.
- exact ih_frame_cf.
- intros inst ly X W regs mem md k l PRE HNB Hl Hlne. exact (ih_shape_cf B Hp ARX (ARX_cf_ARcf B IOK Hp) inst ly X W regs mem md k l PRE HNB Hl Hlne).
- exact ih_post_cf.
- exact ih_owned_cf.
- exact ih_safe_cf.
Qed.
End b.
End a.
