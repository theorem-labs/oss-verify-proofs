(* CARRIED from commit 22b5f48d62482965b4b9d8e93b991b173af3cc04,
   proofs/cgif/cgif_file_fuzzer/lib/YGcfInstEnq.v, sha256 8151fa74fd269170ddc9bc7407443c7f596ac3dac6749f4ddcf36fff5095470e (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The changes made here are in the
   module paths only: OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib M -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable M, except lib.A for: DMspec DMiface DeallocG ImgBaseAG ImgBaseDG DGif0 DIfaceR CLenq ErrnoG MemnormT MnEnq YGcfDIface YGcfInstBase RGtop YGcfInstErrno. *)
(* Copyright 2026 Anthropic PBC *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/YGcfInstEnq.v of this commit (its text CARRIED from cf-f1 22b5f48d6248, blob 4874eeab0ac3), with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), taken by path: no numeral of it names an image address that differs in fuzz_reply.asan-ubsan. *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10 (lane F1 of the generic cf instance layer; integrator ReallocPrimary).
   The cf twins of proofs/cgif/cgif_file_fuzzer/lib/CLenqcgif.v, CLenqcgifE.v, MnEnqcgif.v and MnEnqArms.v at c5
   30a1993588f: QuarantineCache::Enqueue at Put's call, at the cf relation, in every form the Deallocate interfaces
   take it.
   rule 24: no function proved (kind: interface-instance discharge over the unit's Enqueue arms).

   THE SEAM (OPEN).  cgif's arms (CLenqcgif.enq_room_xs / enq_hit_xs / enq_miss_xs, :76 / :139 / :213, and their
   memnorm twins MnEnqArms.enq_room_xsm / enq_hit_xsm / enq_miss_xsm, :51 / :115 / :186) run Enqueue's code at cgif's
   image over cgif's ARm and Wf.  No unit has them at the cf relation yet.  They are the three fields of [EnqArmsCf],
   stated over [enq_pre_cf] at the walk relation [ARX]; lane B2 ports them per unit.  Nothing below proves them.

   The pre [enq_pre_cf] is CLenq.enq_pre_x (CLenq.v:68-79) with its event terms removed (CF-LAYER-LANES.md's gate,
   Main 23:2xZ / 23:4xZ):
   - dropped: CLenq.v:70's cgif-budget clause; refill_reg's two ceiling conjuncts (YG0m.v:63-64, over YG01.v:163-164
     and :202-203); qloosem's cgif-meter room half (YG0n.v:545-547).  The room for the miss arm's class-24 map comes
     from bytes: [batch_room_cf] (YG00cf.v:349-350, map_more_user_ok_cf's premise, YG03cf.v:440) and the walk
     relation's byte budget.  The miss arm's refill reads its own refill contract (lane B2's ei_refill), not this pre;
   - replaced (ReallocPrimary / Main 00:3xZ): CLenq.v:71's batch-count clause and refill_reg's prim clause (YG0m.v:64),
     both LOWER bounds on the event count, are not premises: the pre says instead that X is Put's Enqueue call state
     [qx S0 k0 z tr] (DGif0.v:77-78: Deallocate's tick, the depot answer, the chunk's flip) of a Wf_cf state S0, and
     [enq_tick_bounds_cf] / [enq_pre_tick_cf] derive both bounds from it (Wf_cf's wfc_batches_ev / wfc_prim_ev,
     YG01cf.v:145 / :142, one tick ahead).  The one credit covers Enqueue's single class-24 map (map_post_y3,
     YG03cf.v:436): depot_put maps nothing between the tick and Enqueue;
   - kept: qloose (bytes), the call registers and the chunk facts, verbatim;
   - added (ReallocPrimary 02:3xZ, decision (a)): `ck_n k <= kQuarantineMax`, the text of free_cf's quarantine guard
     (Put's `size > max_size` test: a block of exactly max_size bytes is enqueued); lane B2's strict NMAXD is
     kQuarantineMax + 1 at the cf instance (YGcfInstEnqG.enq_nmax_cf);
   - the stack window stays CLenq.QSTACK_G = 1088 (route 2): the miss arm's Refill call at the entry sp - 64 fits it,
     because the refill contract's window at kBatchClass is RSTACK (YGcfInstRefill.REP_W_enq, commit d94d29d53c8).

   What this file proves from the seam, the call-site bridge [enq_bridge_cf] and the drain bound [enq_qb_t]:
   - [enqueue_spec_xsm_cf]: the three arms as one contract (MnEnqcgif.enqueue_spec_xsm_cgif's case split);
   - [di_enq_post_cf_of_leaf]: CLenq.di_enq_post from the leaf (CLenq.di_enq_post_of_leaf's script without its
     instance-uniqueness field, which the cf relation does not give: the unit's instance predicate IOK);
   - [de_enqueue_g_cf]: DIfaceR.enq_spec_g for every extra conjunct the post, the arm's raw frame and the memnorm keep
     give (MnEnqcgif.de_enqueue_g_m_cgif, CLenqcgifE.de_enqueue_g_cgif);
   - the interface fields: [di_enqueue_cf] (DGif0.v:301-324), [dr_enqueue_cf] (DIfaceR.dr_enqueue),
     [de_enqueue_v_cf] / [de_enqueue_cf] (ErrnoG.de_enqueue_v_t / de_enqueue_t), [enq_m_cf] (MnEnq.de_enqueue_m_t,
     MemnormDtop.v:69's ENQm).
   [enq_bridge_cf] is CLenqcgif.enq_bridge (:455-468) at the cf relation: the Deallocate instance proves it (lane F2a,
   DGif1.enq_bridge_cgif's twin).  [enq_qb_t] is CLenq's es_qb at the consumer's drain bound QB; [enq_qb_w] proves it
   at [QB_w], a byte bound in cf terms only.  The walk relation is any [ARX] that gives ARcf at the caller's ghost set Hp: the layer's
   YGcfInstBase.ARX_cf B IOK Hp, through ARX_cf_ARcf.  No image constant; no cgif instance file is required. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import DMspec DMiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import DeallocG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseAG ImgBaseDG DGif0 DIfaceR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require CLenq ErrnoG MemnormT MnEnq YGcfDIface YGcfInstBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require RGtop.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfAmx YGcfSecsStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfInstErrno.
(* stdpp, through the LPS modules, shadows several list names; NoDup / In here are Stdlib's, as YGcfMallocComposeE.v's. *)
From Stdlib Require Import List.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {IM : AImg} {AG : AGImg} {DI : DImg}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 0. Model facts of the push (CLenqcgif.v:46-47, :373-391, copied).                                                *)
Lemma cfg_mem_eq_cf : forall (c1 c2 : config), c1 = c2 -> ms_mem (cfg_ms c1) = ms_mem (cfg_ms c2).
Proof. intros c1 c2 E. rewrite E. reflexivity. Qed.

Lemma push_facts_cf : forall q k nb,
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

(* The owned set of a state that differs only in its quarantine cache (YFg6.aowned_same, YFg6.v:720-721). *)
Lemma es_owned_cf : forall B ly X X' a, st_chunks X' = st_chunks X -> st_fs X' = st_fs X ->
aowned B ly X' a -> aowned B ly X a.
Proof. intros B ly X X' a E1 E2 H. unfold aowned, aclient_byte, sec_extents, frames in *. rewrite E1, E2 in H. exact H. Qed.

(* The batch-count and prim-mapped lower bounds at Put's Enqueue call state qx S k z tr (DGif0.v:77-78: the depot
   answer and the chunk's change after Deallocate's +1 tick), from Wf_cf at Deallocate's entry state S: they are
   Wf_cf's own wfc_batches_ev / wfc_prim_ev (YG01cf.v:145, :142) moved by the tick, nothing more. *)
Lemma enq_tick_bounds_cf : forall U S k z tr, Wf_cf U S ->
Z.of_nat (length (all_batches (qx S k z tr))) + 1 <= st_nev (qx S k z tr) /\
prim_user_mapped (qx S k z tr) + kUserMapSize <= kUserMapSize * st_nev (qx S k z tr).
Proof.
intros U S k z tr W.
pose proof (wfc_batches_ev _ _ _ _ _ W) as E1. pose proof (wfc_prim_ev _ _ _ _ _ W) as E2.
assert (Eb : all_batches (qx S k z tr) = all_batches S)
  by (unfold qx, YFl0C.depot_after; destruct (z =? 0); reflexivity).
assert (Ep : prim_user_mapped (qx S k z tr) = prim_user_mapped S)
  by (unfold qx, YFl0C.depot_after; destruct (z =? 0); reflexivity).
assert (En : st_nev (qx S k z tr) = st_nev S + 1)
  by (unfold qx, YFl0C.depot_after; destruct (z =? 0); reflexivity).
rewrite Eb, Ep, En. unfold kUserMapSize in *. lia.
Qed.

Section b.
Variable B : asyms.
Hypothesis TS : im_syms B.
(* The caller's ghost set and the walk relation: any relation that gives ARcf at Hp (YGcfInstBase.ARX_cf B IOK Hp,
   with HAR := YGcfInstBase.ARX_cf_ARcf B IOK Hp). *)
Variable Hp : list Z.
Variable ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Hypothesis HAR : forall inst ly S W mem md, ARX inst ly S W mem md -> ARcf im_segs B ly S Hp W mem md.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. The pre, the leaf and the seam.                                                                               *)

(* CLenq.enq_pre_x (CLenq.v:68-79) at the cf relation, its event terms removed (header): the state is Put's call
   state of a Wf_cf state (the two lower bounds follow, enq_pre_tick_cf).  The last three conjuncts are
   acall_pre_cf's last three (field round 3, Main's call-boundary route): cf_hull_ok X, which the drain entry reads
   (Enqueue changes neither st_secs nor the secondary chunks, so the law cf_hull_counts carries it), and the overlay
   normal form and the read-only RELRO bytes at Put's call memory, which the MISS arm moves to the Refill call
   (refill_spec_cf takes all three there). *)
Definition enq_pre_cf (inst : Z) (ly : alayout) (X : astate) (W : world im_segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (k : chunk) : Prop :=
ARX inst ly X W mem md /\ batch_room_cf X /\
(exists S0 k0 z tr, X = qx S0 k0 z tr /\ Wf_cf (as_universe B) S0) /\
In k (st_chunks X) /\ ck_state k = CQuarantined /\ ~ In (ck_beg k) (map ck_beg (q_items X)) /\
YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + CLenq.QSTACK_G <= spZ regs /\ spZ regs <= ly_stk_hi ly /\
(forall a, spZ regs - CLenq.QSTACK_G <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 10 = w64 (ly_T ly + t_qc) /\ getr regs 11 = w64 (ly_T ly + t_cache) /\
getr regs 13 = w64 (sptr_addr B ly (ck_user k) - kChunkHeaderSize) /\ getr regs 14 = w64 (ck_n k) /\
qloose X /\ ck_n k <= kQuarantineMax /\ cf_hull_ok X /\ YG0dcf.arodata_ok_cf im_segs B mem.

(* The two lower bounds the transport re-establishes Wf_cf's fields from, at the pre's state. *)
Lemma enq_pre_tick_cf : forall inst ly X W regs mem md k, enq_pre_cf inst ly X W regs mem md k ->
Z.of_nat (length (all_batches X)) + 1 <= st_nev X /\
prim_user_mapped X + kUserMapSize <= kUserMapSize * st_nev X.
Proof.
intros inst ly X W regs mem md k (_ & _ & (S0 & k0 & z & tr & -> & W0) & _).
exact (enq_tick_bounds_cf _ S0 k0 z tr W0).
Qed.

(* The pre's last two conjuncts (acall_pre_cf's), by name. *)
Lemma enq_pre_mp_cf : forall inst ly X W regs mem md k, enq_pre_cf inst ly X W regs mem md k ->
cf_hull_ok X /\ YG0dcf.arodata_ok_cf im_segs B mem.
Proof.
intros inst ly X W regs mem md k (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H).
exact H.
Qed.

(* CLenqcgif.enq_leaf_xs (CLenqcgif.v:65-72) at the cf relation: CLenq's leaf plus the arm's raw frame, every byte
   outside the pre-state's owned set and Enqueue's stack window kept. *)
Definition enq_leaf_xs_cf (inst : Z) (ly : alayout) (X : astate) (W : world im_segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (k : chunk)
(r : unit * astate) (W' : world im_segs) (c' : config) : Prop :=
CLenq.enq_leaf_x im_segs B ARX (aowned B) inst ly X W regs mem md k r W' c' /\
exists regs' mem' md',
c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
(forall x : word, ~ aowned B ly X (bv_unsigned x) -> ~ (spZ regs - CLenq.QSTACK_G <= bv_unsigned x < spZ regs) ->
   mem' x = mem x).

(* An arm's post: the leaf and the memnorm keep at the return configuration (MnEnqArms.v:55-56). *)
Definition enq_arm_post_cf (inst : Z) (ly : alayout) (X : astate) (W : world im_segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (k : chunk)
(r : unit * astate) (W' : world im_segs) (c' : config) : Prop :=
enq_leaf_xs_cf inst ly X W regs mem md k r W' c' /\
exists regs' mem' md', c' = cfg_at im_segs (raZ regs) regs' mem' md' /\ MemnormT.memnorm_keep im_segs mem mem'.

(* THE SEAM (OPEN): the unit's three Enqueue arms at the cf relation (MnEnqArms.v:51, :115, :186 there). *)
Record EnqArmsCf : Prop := {
  (* the last batch has room *)
  ea_room : forall inst ly X W regs mem md k,
    enq_pre_cf inst ly X W regs mem md k -> need_new_batch (st_qthread X) = false ->
    amreal im_segs (enqueue k X) W (cfg_at im_segs dg_enqueue regs mem md) (enq_arm_post_cf inst ly X W regs mem md k);
  (* a new batch from a non-empty class-24 cache *)
  ea_hit : forall inst ly X W regs mem md k l,
    enq_pre_cf inst ly X W regs mem md k -> need_new_batch (st_qthread X) = true ->
    pc_chunks (cache X kBatchClass) = l -> l <> [] ->
    amreal im_segs (enqueue k X) W (cfg_at im_segs dg_enqueue regs mem md) (enq_arm_post_cf inst ly X W regs mem md k);
  (* a new batch after the class-24 refill *)
  ea_miss : forall inst ly X W regs mem md k,
    enq_pre_cf inst ly X W regs mem md k -> need_new_batch (st_qthread X) = true ->
    pc_chunks (cache X kBatchClass) = [] ->
    amreal im_segs (enqueue k X) W (cfg_at im_segs dg_enqueue regs mem md) (enq_arm_post_cf inst ly X W regs mem md k)
}.

(* The three arms as one contract (MnEnqcgif.v:46-58). *)
Theorem enqueue_spec_xsm_cf : EnqArmsCf -> forall inst ly X W regs mem md k,
enq_pre_cf inst ly X W regs mem md k ->
amreal im_segs (enqueue k X) W (cfg_at im_segs dg_enqueue regs mem md) (enq_arm_post_cf inst ly X W regs mem md k).
Proof.
intros ARMS inst ly X W regs mem md k PREX.
destruct (need_new_batch (st_qthread X)) eqn:HNB.
- destruct (pc_chunks (cache X kBatchClass)) as [|o l0] eqn:E.
  + exact (ea_miss ARMS inst ly X W regs mem md k PREX HNB E).
  + exact (ea_hit ARMS inst ly X W regs mem md k (o :: l0) PREX HNB E ltac:(discriminate)).
- exact (ea_room ARMS inst ly X W regs mem md k PREX HNB).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. The quarantine-cache facts of the call site (CLenq.EnqSub's fields at the cf relation).                       *)

(* The thread cache's byte count, read by Put after Enqueue returns (YFfq.root_vals' fourth cell, over ARmcf). *)
Lemma es_qbytes_cf : forall inst ly X W mem md, ARX inst ly X W mem md ->
val_mem im_segs (mrestrict (w_H W) mem) (ly_T ly + t_qc + 24) 8 (qc_bytes (st_qthread X)).
Proof.
intros inst ly X W mem md H. destruct (HAR inst ly X W mem md H) as (M & _).
assert (IN : In (z8 (aoff (AT t_qc) 24) (qc_bytes (st_qthread X))) (acells_cf B ly X)).
{ unfold acells_cf. rewrite !in_app_iff. do 4 right; left. unfold quar_cells. right; right. apply in_app_iff. left.
  unfold qc_cells. do 3 right; left. reflexivity. }
pose proof (proj1 (Forall_forall _ _) (amc_cells _ _ _ _ _ M) _ IN) as C.
replace (ly_T ly + t_qc + 24) with (aeval B ly (aoff (AT t_qc) 24)) by (cbn; lia).
exact (cell_holds_val_mem im_segs B ly (w_H W) mem (aoff (AT t_qc) 24) 8%nat (ANum (qc_bytes (st_qthread X))) C).
Qed.

Section c.
(* The consumer's parameters: DIface's rpre / fpre / dpost (the Deallocate instance's), the drain bound L24 and the
   drain entry's byte premise QB. *)
Variable rpre : astate -> Z -> Prop.
Variable fpre : alayout -> astate -> world im_segs -> (word -> option byte) -> sptr -> Z -> Prop.
Variable dpost : Z -> alayout -> astate -> world im_segs -> list Z -> Z -> (word -> option byte) -> Prop.
Variable L24 : Z.
Variable QB : astate -> Prop.

(* CLenqcgif.EPc (CLenqcgif.v:396-399): the caller's facts about the pre-state that Enqueue's pre does not carry.
   EPc's third conjunct (CLenqcgif.v:398, a cgif byte cap on the thread cache plus the chunk) is false at reply, where
   one chunk alone reaches that cap; it is RESTATED as its two cf sources: the thread cache's tight bound (qtight at
   Deallocate's entry; the depot answer and the chunk's change keep the quarantine) and free_cf's quarantine guard. *)
Definition EP_cf (X : astate) (k : chunk) : Prop :=
qc_bytes (st_qglobal X) <= kQuarantineMax /\ quar_n X <= queued_n X + ck_n k /\
(qc_bytes (st_qthread X) <= kQuarantineCacheMax /\ ck_n k <= kQuarantineMax) /\
Z.of_nat (length (all_batches X)) + 1 <= L24.

(* lpost := qtight when the thread cache stays below the drain threshold (CLenqcgif.es_lpost_cgif, :401-413). *)
Lemma es_lpost_cf : forall X k nb X', EP_cf X k ->
match nb with None => need_new_batch (st_qthread X) = false | Some _ => need_new_batch (st_qthread X) = true end ->
st_qthread X' = qc_push (st_qthread X) k nb -> st_chunks X' = st_chunks X -> st_qglobal X' = st_qglobal X ->
qc_bytes (st_qthread X') <= kQuarantineCacheMax -> qtight X'.
Proof.
intros X k nb X' (EG & EQ & _ & _) HNB Hqt Hch Hqg Hle.
destruct (push_facts_cf (st_qthread X) k nb HNB) as (_ & PI & _).
split; [exact Hle|]. split; [rewrite Hqg; exact EG|].
unfold quar_n in *. rewrite Hch. rewrite queued_n_eq in EQ |- *.
rewrite Hqt, Hqg, PI. lia.
Qed.

(* CLenq.EnqSub's es_qb at the consumer's QB (CLenq.v:129-135), its event term dropped (CLenqcgif.es_qb_cgif does
   not use it, :424).  Since round 3 the consumer's QB (lane F2b's QB_cf) ends with the hull admission cf_hull_ok X';
   so the pre-state's admission (enq_pre_cf's own cf_hull_ok conjunct) and Enqueue's st_secs frame
   (YGcfSecsStep.ss_enqueue: Enqueue touches no st_secs entry) are premises here, from which cf_hull_counts gives it. *)
Definition enq_qb_t : Prop :=
forall inst ly X W mem md k nb X',
ARX inst ly X W mem md -> EP_cf X k -> In k (st_chunks X) -> ck_state k = CQuarantined ->
~ In (ck_beg k) (map ck_beg (q_items X)) -> qloose X -> cf_hull_ok X ->
match nb with None => need_new_batch (st_qthread X) = false | Some _ => need_new_batch (st_qthread X) = true end ->
st_qthread X' = qc_push (st_qthread X) k nb -> st_chunks X' = st_chunks X -> st_qglobal X' = st_qglobal X ->
st_secs X' = st_secs X ->
kQuarantineCacheMax < qc_bytes (st_qthread X') -> QB X' /\ Z.of_nat (length (all_batches X')) <= L24.

(* The memory predicate at Put's call of Enqueue (DGif0.DIface's MP, field round 3 part 3c): the read-only bytes
   (RELRO and the report reads), acall_pre_cf's last conjunct (YG0dcf.arodata_ok_cf; DGmpcf.MPcf at cgif). *)
Definition MP_enq_cf (m : word -> option byte) : Prop := YG0dcf.arodata_ok_cf im_segs B m.

(* The call-site bridge (CLenqcgif.enq_bridge, :455-468, at the cf relation): at Put's call of Enqueue the walk
   relation holds again at the quarantined state and the call memory [dmem_m], which meets MP_enq_cf (the walk's
   MP_keep).  The Deallocate instance proves it. *)
Definition enq_bridge_cf : Prop :=
forall inst ly S W mem0 md0 p n tr k z hb1 sp0 (regs : bvmap 5 word) (mem : word -> option byte) mat,
ARX inst ly S W mem0 md0 -> rpre S n -> fpre ly S W mem0 p n -> In (p, n) (blocks S) ->
YGcfInstBase.cf_tr_ok B tr S ->
find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
ly_stk_lo ly + DGbaseC.DFSTACK <= sp0 -> sp0 <= ly_stk_hi ly -> ly_bot ly < sp0 -> sp0 mod 16 = 0 ->
0 <= hb1 < 256 -> val_mem im_segs (mrestrict (w_H W) mem0) (sptr_addr B ly p - 16) 4 (2 + 256 * hb1) ->
dmem_m W ly sp0 mem0 (sptr_addr B ly p) (req_size n) hb1 (dpost inst ly S W tr z) mem ->
YG0dcf.arodata_ok_cf im_segs B mem ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs -> spZ regs = sp0 - 80 ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 (ly_T ly + t_qc) -> getr regs 11 = w64 (ly_T ly + t_cache) ->
getr regs 13 = w64 (sptr_addr B ly p - kChunkHeaderSize) -> getr regs 14 = w64 (req_size n) ->
enq_pre_cf inst ly (qx S k z tr) W regs mem (with_vm_backing (m_vm_lazy md0) mat md0) (qk k) /\
EP_cf (qx S k z tr) (qk k).

(* CLenq.di_enq_post_of_leaf (CLenq.v:154-172) at the cf relation, without EnqSub's instance-uniqueness field; the
   result's st_secs frame (Enqueue's model, on every granted path) feeds enq_qb_t. *)
Theorem di_enq_post_cf_of_leaf : enq_qb_t ->
forall inst ly X W regs mem md k r W' c',
EP_cf X k -> enq_pre_cf inst ly X W regs mem md k -> st_secs (snd r) = st_secs X ->
CLenq.enq_leaf_x im_segs B ARX (aowned B) inst ly X W regs mem md k r W' c' ->
CLenq.di_enq_post im_segs B ARX (aowned B) qtight QB L24 inst ly X W regs mem md k r W' c'.
Proof.
intros HQB inst ly X W regs mem md k r W' c' HEP PRE HSE LEAF.
destruct PRE as (HARX & _ & _ & Hk & Hst & Hnq & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQL & _ & HHULL & _).
destruct LEAF as (regs' & mem' & md' & nb & Hc & POST & Hqt & Hnb & Hch & Hqg & Hfs).
pose proof (proj1 POST) as HARX'.
exists regs', mem', md', nb.
split; [exact Hc|]. split; [exact POST|]. split; [exact Hqt|]. split; [exact Hnb|].
split; [exact Hch|]. split; [exact Hqg|].
split; [intros a Ha; exact (es_owned_cf B ly X (snd r) a Hch Hfs Ha)|].
split; [exact (es_qbytes_cf inst ly (snd r) W' mem' md' HARX')|].
split.
- intros Hle. exact (es_lpost_cf X k nb (snd r) HEP Hnb Hqt Hch Hqg Hle).
- intros Hgt. exact (HQB inst ly X W mem md k nb (snd r) HARX HEP Hk Hst Hnq HQL HHULL Hnb Hqt Hch Hqg HSE Hgt).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. Enqueue at Put's call (DIfaceR.enq_spec_g) for every extra conjunct [XR] that the call post, the arm's raw     *)
(*    frame and the memnorm keep give (MnEnqcgif.v:65-95; CLenqcgifE.v:101-128).                                    *)
Theorem de_enqueue_g_cf : EnqArmsCf -> enq_bridge_cf -> enq_qb_t ->
forall XR : fxrel,
(forall inst stk ly X W regs mem md E ly' X' W' regs' mem' md',
  ARX inst ly X W mem md -> ly_stk_lo ly + CLenq.QSTACK_G <= spZ regs ->
  CLenq.acall_post_x im_segs B ARX (aowned B) inst stk ly X W regs mem md E ly' X' W' regs' mem' md' ->
  (forall x : word, ~ aowned B ly X (bv_unsigned x) -> ~ (spZ regs - CLenq.QSTACK_G <= bv_unsigned x < spZ regs) ->
     mem' x = mem x) ->
  MemnormT.memnorm_keep im_segs mem mem' ->
  XR inst stk ly X W regs mem md E ly' X' W' regs' mem' md') ->
enq_spec_g B (YGcfInstBase.cf_tr_ok B) ARX (aowned B) rpre qtight fpre dpost L24 QB MP_enq_cf XR.
Proof.
intros ARMS BR HQB XR HXR inst ly S W mem0 md0 p n tr k z hb1 sp0 regs mem mat
  HARX HRP HFP HBLK HU HFU HCK HS1 HS2 HS3 HS4 HHB HHDR HMEM HMP HRA HRA4 HSP HGP HTP HA0 HA1 HA3 HA4.
destruct (BR inst ly S W mem0 md0 p n tr k z hb1 sp0 regs mem mat
  HARX HRP HFP HBLK HU HFU HCK HS1 HS2 HS3 HS4 HHB HHDR HMEM HMP
  HRA HRA4 HSP HGP HTP HA0 HA1 HA3 HA4) as [PREX HEP].
pose proof PREX as (HARXq & _ & _ & _ & _ & _ & _ & _ & _ & Hlo & _).
eapply amreal_mono;
[| exact (RGtop.rg_amreal_apostg im_segs (enqueue (qk k) (qx S k z tr)) (fun r => st_secs (snd r) = st_secs (qx S k z tr))
     W _ _ (fun trc r Hp _ => YGcfAmx.ipost_apath_amx _ _ trc r (YGcfSecsStep.ss_enqueue (qk k) (qx S k z tr)) Hp)
     (enqueue_spec_xsm_cf ARMS inst ly (qx S k z tr) W regs mem (with_vm_backing (m_vm_lazy md0) mat md0) (qk k) PREX))].
cbv beta. intros r W' c' [HSE [[LEAF (regsR & memR & mdR & HcR & FR)] (regsM & memM & mdM & HcM & MNK)]].
destruct (di_enq_post_cf_of_leaf HQB inst ly (qx S k z tr) W regs mem (with_vm_backing (m_vm_lazy md0) mat md0) (qk k)
  r W' c' HEP PREX HSE LEAF) as (regs' & mem' & md' & nb & Hc & POST & R).
assert (Em : memR = mem').
{ pose proof (cfg_mem_eq_cf _ _ (eq_trans (eq_sym HcR) Hc)) as E. cbn in E. exact E. }
assert (EmM : memM = mem').
{ pose proof (cfg_mem_eq_cf _ _ (eq_trans (eq_sym HcM) Hc)) as E. cbn in E. exact E. }
rewrite Em in FR. rewrite EmM in MNK.
exists regs', mem', md', nb. split; [exact Hc|].
split.
{ destruct POST as (P1 & P2 & P3 & P4 & P5 & P6 & _ & P8).
  exact (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 (conj P6 P8)))))). }
split; [exact (HXR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARXq Hlo POST FR MNK)|].
exact R.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. The interface fields at the cf relation.                                                                      *)

(* DGif0.DIface's di_enqueue (DGif0.v:301-324). *)
Theorem di_enqueue_cf : EnqArmsCf -> enq_bridge_cf -> enq_qb_t ->
forall inst ly S W mem0 md0 p n tr k z hb1 sp0 (regs : bvmap 5 word) (mem : word -> option byte) mat,
ARX inst ly S W mem0 md0 -> rpre S n -> fpre ly S W mem0 p n -> In (p, n) (blocks S) ->
(YGcfInstBase.cf_tr_ok B) tr S ->
find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
ly_stk_lo ly + DGbaseC.DFSTACK <= sp0 -> sp0 <= ly_stk_hi ly -> ly_bot ly < sp0 -> sp0 mod 16 = 0 ->
0 <= hb1 < 256 -> val_mem im_segs (mrestrict (w_H W) mem0) (sptr_addr B ly p - 16) 4 (2 + 256 * hb1) ->
dmem_m W ly sp0 mem0 (sptr_addr B ly p) (req_size n) hb1 (dpost inst ly S W tr z) mem ->
YG0dcf.arodata_ok_cf im_segs B mem ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs -> spZ regs = sp0 - 80 ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 (ly_T ly + t_qc) -> getr regs 11 = w64 (ly_T ly + t_cache) ->
getr regs 13 = w64 (sptr_addr B ly p - kChunkHeaderSize) -> getr regs 14 = w64 (req_size n) ->
amreal im_segs (enqueue (qk k) (qx S k z tr)) W
  (cfg_at im_segs dg_enqueue regs mem (with_vm_backing (m_vm_lazy md0) mat md0))
  (fun r W' c' => exists regs' mem' md' nb,
    c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
    acall_post_x B ARX (aowned B) inst YFewC.QSTACK ly (qx S k z tr) W regs mem (with_vm_backing (m_vm_lazy md0) mat md0) (fun _ => False)
      ly (snd r) W' regs' mem' md' /\
    st_qthread (snd r) = qc_push (st_qthread (qx S k z tr)) (qk k) nb /\
    match nb with None => need_new_batch (st_qthread (qx S k z tr)) = false | Some _ => need_new_batch (st_qthread (qx S k z tr)) = true end /\
    st_chunks (snd r) = st_chunks (qx S k z tr) /\ st_qglobal (snd r) = st_qglobal (qx S k z tr) /\
    (forall a, aowned B ly (snd r) a -> aowned B ly (qx S k z tr) a) /\
    val_mem im_segs (mrestrict (w_H W') mem') (ly_T ly + t_qc + 24) 8 (qc_bytes (st_qthread (snd r))) /\
    (qc_bytes (st_qthread (snd r)) <= kQuarantineCacheMax -> qtight (snd r)) /\
    (kQuarantineCacheMax < qc_bytes (st_qthread (snd r)) -> QB (snd r) /\ Z.of_nat (length (all_batches (snd r))) <= L24)).
Proof.
intros ARMS BR HQB inst ly S W mem0 md0 p n tr k z hb1 sp0 regs mem mat
  H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 HRO H15 H16 H17 H18 H19 H20 H21 H22 H23.
eapply amreal_mono; [| exact (de_enqueue_g_cf ARMS BR HQB (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True)
  (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => I)
  inst ly S W mem0 md0 p n tr k z hb1 sp0 regs mem mat
  H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 HRO H15 H16 H17 H18 H19 H20 H21 H22 H23)].
intros r W' c' (regs' & mem' & md' & nb & Hc & HP & _ & HT).
exists regs', mem', md', nb. split; [exact Hc|]. split; [exact HP | exact HT].
Qed.

(* DIfaceR.DIfaceR's dr_enqueue: the post's raw frame. *)
Theorem dr_enqueue_cf : EnqArmsCf -> enq_bridge_cf -> enq_qb_t ->
enq_spec_g B (YGcfInstBase.cf_tr_ok B) ARX (aowned B) rpre qtight fpre dpost L24 QB MP_enq_cf
  (acall_raw_x B (aowned B)).
Proof.
intros ARMS BR HQB. refine (de_enqueue_g_cf ARMS BR HQB (acall_raw_x B (aowned B)) _).
intros inst stk ly X W regs mem md E ly' X' W' regs' mem' md' _ _ (_ & _ & _ & _ & _ & _ & FR & _) _ _. exact FR.
Qed.

Section e.
(* errno: the image facts and the two image premises of YGcfInstErrno.v. *)
Hypothesis EI : ErrnoImgCf.
Hypothesis HSEG : errno_seg_t B.
Hypothesis HNS : errno_nstatic_t B.
Hypothesis HC : YGcfDIface.IMG_COVER.

(* errno kept on the raw memory by the arm's raw frame (CLenqcgifE.enq_errno_kept, :60-77). *)
Lemma enq_errno_kept_cf : forall inst ly X W regs mem md (mem' : word -> option byte),
ARX inst ly X W mem md -> ly_stk_lo ly + CLenq.QSTACK_G <= spZ regs ->
(forall x : word, ~ aowned B ly X (bv_unsigned x) -> ~ (spZ regs - CLenq.QSTACK_G <= bv_unsigned x < spZ regs) ->
   mem' x = mem x) ->
ErrnoG.errno_kept B mem mem'.
Proof.
intros inst ly X W regs mem md mem' HARX Hlo FR.
exact (errno_kept_of_frame_cf B TS EI HSEG HNS HC ly X Hp W mem md (spZ regs - CLenq.QSTACK_G) (spZ regs) mem'
  (HAR inst ly X W mem md HARX) ltac:(lia) FR).
Qed.

(* ErrnoG.de_enqueue_t: the raw frame and errno kept on the raw memory (CLenqcgifE.de_enqueue_cgif, :139-145). *)
Theorem de_enqueue_cf : EnqArmsCf -> enq_bridge_cf -> enq_qb_t ->
ErrnoG.de_enqueue_t B (YGcfInstBase.cf_tr_ok B) ARX (aowned B) rpre qtight fpre dpost L24 QB MP_enq_cf.
Proof.
intros ARMS BR HQB. refine (de_enqueue_g_cf ARMS BR HQB (ErrnoG.acall_raw_e_x B (aowned B)) _).
intros inst stk ly X W regs mem md E ly' X' W' regs' mem' md' HARX Hlo (_ & _ & _ & _ & _ & _ & FR & _) FRa _.
exact (conj FR (enq_errno_kept_cf inst ly X W regs mem md mem' HARX Hlo FRa)).
Qed.

(* ErrnoG.de_enqueue_v_t: errno kept on the view (CLenqcgifE.de_enqueue_v_cgif, :131-136). *)
Theorem de_enqueue_v_cf : EnqArmsCf -> enq_bridge_cf -> enq_qb_t ->
ErrnoG.de_enqueue_v_t B (YGcfInstBase.cf_tr_ok B) ARX (aowned B) rpre qtight fpre dpost L24 QB MP_enq_cf.
Proof.
intros ARMS BR HQB. refine (de_enqueue_g_cf ARMS BR HQB (ErrnoG.acall_errno_v_x B) _).
intros inst stk ly X W regs mem md E ly' X' W' regs' mem' md' HARX Hlo _ FRa _.
exact (errno_kept_view_cf B TS EI W W' mem mem' (enq_errno_kept_cf inst ly X W regs mem md mem' HARX Hlo FRa)).
Qed.

(* MnEnq.de_enqueue_m_t: the raw frame, errno and the memnorm keep (MnEnqcgif.enq_m_cgif, :98-104). *)
Theorem enq_m_cf : EnqArmsCf -> enq_bridge_cf -> enq_qb_t ->
MnEnq.de_enqueue_m_t B (YGcfInstBase.cf_tr_ok B) ARX (aowned B) rpre qtight fpre dpost L24 QB MP_enq_cf.
Proof.
intros ARMS BR HQB. refine (de_enqueue_g_cf ARMS BR HQB (MnEnq.acall_raw_em_x B (aowned B)) _).
intros inst stk ly X W regs mem md E ly' X' W' regs' mem' md' HARX Hlo (_ & _ & _ & _ & _ & _ & FR & _) FRa MNK.
exact (conj FR (conj (enq_errno_kept_cf inst ly X W regs mem md mem' HARX Hlo FRa) MNK)).
Qed.
End e.
End c.

(* A drain-entry byte premise that every post-push state meets from EP_cf alone, in cf terms (the thread cache's
   tight bound, the quarantine guard and one batch): [enq_qb_t] is satisfiable (CLenqcgif.es_qb_cgif's script,
   :415-433).  A consumer's QB that follows from it (lane F2b's QB_cf kQuarantineMax, by QB_cf_intro) gets
   [enq_qb_t] the same way. *)
Definition QB_w (X' : astate) : Prop :=
qc_bytes (st_qthread X') <= kQuarantineCacheMax + kQuarantineMax + kBatchBytes /\
qc_bytes (st_qglobal X') <= kQuarantineMax /\ quar_n X' <= queued_n X'.

Lemma enq_qb_w : forall L24, enq_qb_t L24 QB_w.
Proof.
intros L24 inst ly X W mem md k nb X' _ (EG & EQ & [ET EN] & EL) _ _ _ _ _ HNB Hqt Hch Hqg _ _.
destruct (push_facts_cf (st_qthread X) k nb HNB) as (PB & PI & PL).
split.
- split; [rewrite Hqt, PB; destruct nb; unfold kBatchBytes in *; lia|].
  split; [rewrite Hqg; exact EG|].
  unfold quar_n in *. rewrite Hch. rewrite queued_n_eq in EQ |- *.
  rewrite Hqt, Hqg, PI. lia.
- unfold all_batches in *. rewrite Hqt, Hqg. rewrite length_app in *.
  clear - PL EL. lia.
Qed.

(* The hull admission after the push, from enq_qb_t's two premises (a consumer's QB that ends with cf_hull_ok X',
   lane F2b's QB_cf, gets that conjunct from here): equal st_secs give equal meters, and cf_hull_counts. *)
Lemma enq_qb_hull_cf : forall X X', cf_hull_ok X -> st_secs X' = st_secs X -> cf_hull_ok X'.
Proof.
intros X X' H E. apply (cf_hull_counts X' X); [unfold nsec_cf | unfold sec_T_cf | exact H]; rewrite E; reflexivity.
Qed.

(* qloose after the push, for any per-chunk enqueue cap [QM] with room under qloose's thread bound (prepared for the
   quarantine's max_size branch of Put: chunks above max_size are not enqueued, so EP_cf will carry ck_n k <= the
   max_size cell's value; then enq_qb_t holds at QB := qloose by this lemma, CLenqcgif.es_qb_cgif's script). *)
Lemma qloose_after_push_cf : forall (QM : Z) X k nb X',
QM + kQuarantineCacheMax + kBatchBytes <= 2 ^ 29 -> ck_n k <= QM ->
qc_bytes (st_qthread X) <= kQuarantineCacheMax -> qc_bytes (st_qglobal X) <= kQuarantineMax ->
quar_n X <= queued_n X + ck_n k ->
match nb with None => need_new_batch (st_qthread X) = false | Some _ => need_new_batch (st_qthread X) = true end ->
st_qthread X' = qc_push (st_qthread X) k nb -> st_chunks X' = st_chunks X -> st_qglobal X' = st_qglobal X ->
qloose X'.
Proof.
intros QM X k nb X' HQM HK ET EG EQ HNB Hqt Hch Hqg.
destruct (push_facts_cf (st_qthread X) k nb HNB) as (PB & PI & _).
split; [rewrite Hqt, PB; destruct nb; unfold kBatchBytes in *; lia|].
split; [rewrite Hqg; unfold kQuarantineMax in *; lia|].
unfold quar_n in *. rewrite Hch. rewrite queued_n_eq in EQ |- *.
rewrite Hqt, Hqg, PI. lia.
Qed.
End b.
End a.
