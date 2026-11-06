(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: taken by path from proofs/cgif/cgif_file_fuzzer/lib/YGcfInstRefill.v at commit d0377850faab (the cf layer of record, field round 3 + the hull round + pf_ial_apart_t), module paths changed; the preset-side hunks kept on top are listed in the round6g report. *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* The cf layer's REFILL walk premise, one shared text for every cf unit (lane M, the cf layer).

   [refill_walk_cf] is what a unit's refill walk proves (cgif: CLrefillR.tfib_refill_okR / MnRefillR.tfib_refill_okR_em,
   re-based on the cf model): Allocate's refill subroutine, entered at AGImg's [ag_refill] with AIfaceM.if_refill's
   registers and stack (AGif0n.v:286-298), runs the cf refill tree from the TICKED entry state and ends in
   [rwalk_leaf_cf].  Text by CfInstMiss (commit 5ab4f0658bd, YGcfInstMiss.v:270-295), stated through the
   interface's own premises: ARXq_cf and rpre_cf at the ENTRY state S0, at the call-time memory and model.

   It REPLACES the earlier refill_pre_cf / refill_leaf_cf / tfib_refill_spec_cf (commits ad082add249, 381bf57c5b3), which
   CORRECTS those commits' messages on three points:
   - the old leaf's frame was acall_post_cf with exception (fun _ => False) over aowned, which is FALSE on the class-full
     path: a non-batch class-full report inside the refill writes the errbuf (errb_report_cf / errb_map_cf,
     YG00cf.v:122-178), an xs_cf extent and not aowned.  The new leaf frames outside AOX_cf (= aowned plus the errbuf,
     AOXm_cf) and restates xs_mapped_cf at the result;
   - the old leaf had no raw frame, no memnorm_keep, errno inside ascratch and the layout fixed, so it could not give
     MnRefill.rleaf_em; the new one has all four;
   - E2 (`prim_user_mapped S + kUserMapSize <= kUserMapSize * st_nev S`) is DROPPED, not kept: the tree runs from
     set_nev (st_nev S0 + 1) S0, and WfP_cf_tick' (YG02cf.v:153, `Wf_cf U s -> WfP_cf U 1 1 1 (set_nev (st_nev s + 1)
     s)`) gives wfc_prim_ev one user map ahead from S0's Wf_cf alone.
   The old text's own source, commit 5ab58d26200, lib/A/AFl1cf.v:35-57, carried event regime clauses (refill_reg,
   YG0m.v:63-64) and cgif's non-cf meter (qloosem, YG0n.v:545-547) at tfibsegs; none of that is here.
   EVENT-FREE: no st_nev bound, EV_A, EV_MAX, EV_BIG, mtr_ok, aregime or non-cf abudget; st_nev appears only in the
   tick `set_nev (st_nev S0 + 1) S0`.

   The CALL-SITE-GENERIC refill contract [refill_spec_cf] (a Theorem Labs lane RefillSpec, 2026-10-30, lane M second hand): the cf
   twin of cgif's MnRefillLoc.tfib_refill_specR_em (MnRefillLoc.v:52-55) over cgif's refill_pre registers (YFl1.v:27-38).
   The tree runs UNTICKED at the CALL state; any caller (its own return address, a0 = the cache, a1 = the class's cache,
   a2 = the instance, a3 = the class, its own stack); ARX_cf by name, NOT ARXq_cf (qtight is false at Enqueue's call,
   chunk CQuarantined but not queued); the leaf is a Theorem Labs lane's LEAF_B2 form (commit 5aba6f8274ea,
   YFkzcf.v:999-1005) over the window REP_STACK and the class-full exception refill_exc_cf, plus the fields
   rwalk_leaf_cf needs, plus the model clause refill_q_cf (chunks and quarantine unchanged, caches inited).
   Callers: Allocate's primary miss arm (AGif0n.v:293, via refill_walk_cf) and Enqueue's miss arm inside Deallocate
   (cgif YFg6.v:272-279; Enqueue enters at Deallocate's sp0 - 80, DGfz.v:269, and calls the refill at its sp - 64).
   The refill window: the class-full report path writes 224 + 1232 = 1456 bytes below the refill's sp (commit
   5af9fe91f6d: APP_STK 512, PR_STK 1232, refusal head removed), more than RSTACK = 1024; the batch class has no report
   path (refill_batch_secs), so the contract's window is REP_W c: RSTACK for kBatchClass (Enqueue's call fits its
   QSTACK_G = 64 + RSTACK, REP_W_enq), REP_STACK otherwise; rwalk_leaf_cf frames and presents
   [spZ regs - REP_STACK, spZ regs).  Every proof uses the names and REP_STACK_le / REP_W_le only. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YP09 YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf YGcfImgRows.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG02cf YGcfRoomPre YGcfRmodel YGcfNilInit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import AllocG ImgBase ImgBaseAG AGif0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ImgBaseDG DGif0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require CLenq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfMallocCompose YGcfXs YGcfInstBase.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg} {AG : AGImg}.
Local Open Scope am_scope.

(* The cf refill tree, as malloc_cf's primary miss arm runs it (YGcfInstMiss.shape_miss_cf). *)
Definition refill_tree_cf (c : Z) : M unit := init_cache_if_needed ;; refill_if_empty_cf c.

(* The refill's stack window: 2048 >= the report path's 1456 bytes (commit 5af9fe91f6d), and >= RSTACK, the window
   cgif's B2 walk runs in (YFkw.segB2 / YFkzcf.LEAF_B2 except [sp - RSTACK, sp)), so a walk entered with the REP_STACK
   window may step into the RSTACK one; [0 <= RSTACK] keeps REP_STACK's sign for the consumers' lia (CfInstMiss's
   REP_STACK_af).  Proofs use the NAME and [REP_STACK_le] only.  Room at both callers: Allocate 176 + 3840 = 4016 <=
   AFSTACK 4096 (ImgBaseAG.v:58, AGif0n.v:293); Enqueue via Deallocate 80 + 64 + 3840 = 3984 <= DFSTACK 8192
   (DGfz.v:269 / :188). *)
Definition REP_STACK : Z := 2048.
Lemma REP_STACK_le : 0 <= RSTACK /\ RSTACK <= REP_STACK <= 3840.
Proof. unfold RSTACK, REP_STACK. lia. Qed.

(* The CALL-SITE-GENERIC contract's window, per class: the batch class never takes the report path (its tree is
   cgif's, refill_tree_cf_batch, and keeps the secondary table, refill_batch_secs: no errbuf map, no print), so its
   writes stay in cgif's RSTACK window; every other class may print, so REP_STACK.  Consumers use REP_W_le /
   REP_W_batch / REP_W_other / REP_W_enq, never its body. *)
Definition REP_W (c : Z) : Z := if c =? kBatchClass then RSTACK else REP_STACK.
Lemma REP_W_le : forall c, RSTACK <= REP_W c <= REP_STACK.
Proof. intros c. pose proof REP_STACK_le as (R0 & R1 & R2). unfold REP_W. destruct (c =? kBatchClass); lia. Qed.
Lemma REP_W_batch : REP_W kBatchClass = RSTACK.
Proof. unfold REP_W. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma REP_W_other : forall c, c <> kBatchClass -> REP_W c = REP_STACK.
Proof. intros c H. unfold REP_W. apply Z.eqb_neq in H. rewrite H. reflexivity. Qed.
(* Enqueue's call fits its own window: it calls the refill at its entry sp - 64 (YFg6.v:273), and CLenq's window
   QSTACK_G = 1088 = 64 + RSTACK. *)
Lemma REP_W_enq : 64 + REP_W kBatchClass = CLenq.QSTACK_G.
Proof. rewrite REP_W_batch. unfold RSTACK, CLenq.QSTACK_G. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The batch class's refill tree is cgif's: Enqueue's model (YG00.enqueue, :442-445) runs cgif's cache_alloc         *)
(* kBatchClass, whose refill part is init_cache_if_needed ;; refill_if_empty kBatchClass; populate_cf kBatchClass is  *)
(* cgif's populate (YG00cf.v:181-182), so the two trees are the same term.                                           *)
Lemma refill_tree_cf_batch : forall s, refill_tree_cf kBatchClass s = (init_cache_if_needed ;; refill_if_empty kBatchClass) s.
Proof. intros s. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The model clause, PROVED from the model: on every returning path the refill tree keeps the chunks, both          *)
(* quarantine caches and the fakestack, and leaves the caches inited (an all-paths walk, YGcfXs.cfx_ipost).  The rq_*  *)
(* family is the miss step's (cgif/cgif_file_fuzzer lib/YGcfInstMiss.v, file sha256 fc3248a0e299; donor not released), with st_fs added (secondary-link step). *)
Definition rq_same (s s' : astate) : Prop :=
st_chunks s' = st_chunks s /\ st_qthread s' = st_qthread s /\ st_qglobal s' = st_qglobal s /\
st_fs s' = st_fs s /\ st_cache_inited s' = st_cache_inited s.

Create HintDb rqdb.

Ltac rq_unf :=
progress (unfold YG00.get_region, YG00.set_region, YG00.get_pc, YG00.set_pc, YG00.init_cache_if_needed,
YG00.bind, YG00.get, YG00.put, YG00.modify, YG00.askz, YG00.ret, YG00.mcheck, YG00.fail, YG00.spin, rq_same in *).

Ltac rq_cbn :=
cbn [ibind cfx_ipost fst snd st_secs st_chunks st_regions st_cache st_cache_inited st_sec_arr st_sec_reserved
st_qthread st_qglobal st_fs st_depot st_internal_inited set_regions set_cache set_chunks set_secs set_sec_arr
set_sec_reserved set_depot set_cache_inited set_qglobal set_qthread set_internal_inited] in *.

Ltac rq_hint :=
first
[ match goal with |- cfx_ipost (ibind _ _) _ =>
  apply cfx_ipost_ibind; eapply cfx_ipost_mono; [|solve [eauto with rqdb]];
  let x := fresh "x" in let sx := fresh "sx" in let H1 := fresh "Hq" in
  intros [x sx] H1; cbn [fst snd] in H1; unfold rq_same in H1; destruct H1 as (? & ? & ? & ? & ?) end
| match goal with |- cfx_ipost _ _ =>
  eapply cfx_ipost_mono; [|solve [eauto with rqdb]];
  let x := fresh "x" in let sx := fresh "sx" in let H1 := fresh "Hq" in
  intros [x sx] H1; cbn [fst snd] in H1; unfold rq_same in H1; destruct H1 as (? & ? & ? & ? & ?) end ].

Ltac rq_step :=
first
[ progress rq_cbn
| rq_unf
| progress intros
| match goal with |- cfx_ipost (ibind (ibind _ _) _) _ => apply cfx_ipost_ibind_assoc end
| rq_hint
| match goal with |- context [match ?x with _ => _ end] => destruct x eqn:? end
| exact I
| (repeat split; congruence) ].

Lemma rq_tick : forall s, cfx_ipost (tick s) (fun r => rq_same s (snd r)).
Proof. intros s. unfold tick, modify. cbn. repeat split. Qed.
#[local] Hint Resolve rq_tick : rqdb.
Lemma rq_ensure : forall c need sof s, cfx_ipost (ensure_free_array c need sof s) (fun r => rq_same s (snd r)).
Proof. intros c need sof s. unfold ensure_free_array. repeat rq_step. Qed.
#[local] Hint Resolve rq_ensure : rqdb.
Lemma rq_mmu : forall c need s, cfx_ipost (map_more_user c need s) (fun r => rq_same s (snd r)).
Proof. intros c need s. unfold map_more_user. repeat rq_step. Qed.
#[local] Hint Resolve rq_mmu : rqdb.
Lemma rq_populate : forall c need s, cfx_ipost (populate c need s) (fun r => rq_same s (snd r)).
Proof. intros c need s. unfold populate. repeat rq_step. Qed.
#[local] Hint Resolve rq_populate : rqdb.
Lemma rq_set_exh : forall c s, cfx_ipost (set_exh_cf c s) (fun r => rq_same s (snd r)).
Proof. intros c s. unfold set_exh_cf. repeat rq_step. Qed.
#[local] Hint Resolve rq_set_exh : rqdb.
Lemma rq_clear_exh : forall c s, cfx_ipost (clear_exh_cf c s) (fun r => rq_same s (snd r)).
Proof. intros c s. unfold clear_exh_cf. repeat rq_step. Qed.
#[local] Hint Resolve rq_clear_exh : rqdb.
Lemma rq_errb_set_size : forall ns s, cfx_ipost (errb_set_size ns s) (fun r => rq_same s (snd r)).
Proof. intros ns s. unfold errb_set_size. repeat rq_step. Qed.
#[local] Hint Resolve rq_errb_set_size : rqdb.
Lemma rq_errb_retire : forall s, cfx_ipost (errb_retire s) (fun r => rq_same s (snd r)).
Proof. intros s. unfold errb_retire. repeat rq_step. Qed.
#[local] Hint Resolve rq_errb_retire : rqdb.
Lemma rq_errb_map : forall w s, cfx_ipost (errb_map_cf w s) (fun r => rq_same s (snd r)).
Proof. intros w s. unfold errb_map_cf. repeat rq_step. Qed.
#[local] Hint Resolve rq_errb_map : rqdb.
Lemma rq_errb_append : forall len s, cfx_ipost (errb_append_cf len s) (fun r => rq_same s (snd r)).
Proof. intros len s. unfold errb_append_cf. repeat rq_step. Qed.
#[local] Hint Resolve rq_errb_append : rqdb.
Lemma rq_errb_report : forall c s, cfx_ipost (errb_report_cf c s) (fun r => rq_same s (snd r)).
Proof. intros c s. unfold errb_report_cf. repeat rq_step. Qed.
#[local] Hint Resolve rq_errb_report : rqdb.
Lemma rq_mmu_cf : forall c need s, cfx_ipost (map_more_user_cf c need s) (fun r => rq_same s (snd r)).
Proof. intros c need s. unfold map_more_user_cf. repeat rq_step. Qed.
#[local] Hint Resolve rq_mmu_cf : rqdb.
Lemma rq_populate_cf : forall c need s, cfx_ipost (populate_cf c need s) (fun r => rq_same s (snd r)).
Proof. intros c need s. unfold populate_cf. repeat rq_step. Qed.
#[local] Hint Resolve rq_populate_cf : rqdb.
Lemma rq_gfa_cf : forall c n s, cfx_ipost (get_from_allocator_cf c n s) (fun r => rq_same s (snd r)).
Proof. intros c n s. unfold get_from_allocator_cf. repeat rq_step. Qed.
#[local] Hint Resolve rq_gfa_cf : rqdb.
Lemma rq_refill_cf : forall c s, cfx_ipost (refill_if_empty_cf c s) (fun r => rq_same s (snd r)).
Proof. intros c s. unfold refill_if_empty_cf. repeat rq_step. Qed.
#[local] Hint Resolve rq_refill_cf : rqdb.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* THE SOUNDNESS OF REP_W at kBatchClass, from the model: the batch class's tree is cgif's (refill_tree_cf_batch:    *)
(* map_more_user_cf / populate_cf call cgif's map_more_user / populate for it, YG00cf.v:159-182, whose class-full    *)
(* arm is cgif's vacuous mcheck, under batch_room_cf), and on every returning path it keeps the secondary table      *)
(* st_secs, so no errbuf map, retire or print (errb_map_cf / errb_retire / errb_set_size all change st_secs): the  *)
(* report path, the only one deeper than RSTACK, is not in the tree.                                                *)
Definition rs_same (s s' : astate) : Prop := st_secs s' = st_secs s.

Create HintDb rsdb.

Ltac rs_unf :=
progress (unfold YG00.get_region, YG00.set_region, YG00.get_pc, YG00.set_pc, YG00.init_cache_if_needed,
YG00.bind, YG00.get, YG00.put, YG00.modify, YG00.askz, YG00.ret, YG00.mcheck, YG00.fail, YG00.spin, rs_same in *).

Ltac rs_hint :=
first
[ match goal with |- cfx_ipost (ibind _ _) _ =>
  apply cfx_ipost_ibind; eapply cfx_ipost_mono; [|solve [eauto with rsdb]];
  let x := fresh "x" in let sx := fresh "sx" in let H1 := fresh "Hs" in
  intros [x sx] H1; cbn [fst snd] in H1; unfold rs_same in H1 end
| match goal with |- cfx_ipost _ _ =>
  eapply cfx_ipost_mono; [|solve [eauto with rsdb]];
  let x := fresh "x" in let sx := fresh "sx" in let H1 := fresh "Hs" in
  intros [x sx] H1; cbn [fst snd] in H1; unfold rs_same in H1 end ].

Ltac rs_step :=
first
[ progress rq_cbn
| rs_unf
| progress intros
| match goal with |- cfx_ipost (ibind (ibind _ _) _) _ => apply cfx_ipost_ibind_assoc end
| rs_hint
| match goal with |- context [match ?x with _ => _ end] => destruct x eqn:? end
| exact I
| congruence ].

Lemma rs_tick : forall s, cfx_ipost (tick s) (fun r => rs_same s (snd r)).
Proof. intros s. unfold tick, modify. cbn. reflexivity. Qed.
#[local] Hint Resolve rs_tick : rsdb.
Lemma rs_ensure : forall c need sof s, cfx_ipost (ensure_free_array c need sof s) (fun r => rs_same s (snd r)).
Proof. intros c need sof s. unfold ensure_free_array. repeat rs_step. Qed.
#[local] Hint Resolve rs_ensure : rsdb.
Lemma rs_mmu : forall c need s, cfx_ipost (map_more_user c need s) (fun r => rs_same s (snd r)).
Proof. intros c need s. unfold map_more_user. repeat rs_step. Qed.
#[local] Hint Resolve rs_mmu : rsdb.
Lemma rs_populate : forall c need s, cfx_ipost (populate c need s) (fun r => rs_same s (snd r)).
Proof. intros c need s. unfold populate. repeat rs_step. Qed.
#[local] Hint Resolve rs_populate : rsdb.
Lemma rs_gfa : forall c n s, cfx_ipost (get_from_allocator c n s) (fun r => rs_same s (snd r)).
Proof. intros c n s. unfold get_from_allocator. repeat rs_step. Qed.
#[local] Hint Resolve rs_gfa : rsdb.
Lemma rs_refill : forall c s, cfx_ipost (refill_if_empty c s) (fun r => rs_same s (snd r)).
Proof. intros c s. unfold refill_if_empty. repeat rs_step. Qed.
#[local] Hint Resolve rs_refill : rsdb.

Lemma refill_batch_secs : forall s, cfx_ipost (refill_tree_cf kBatchClass s) (fun r => st_secs (snd r) = st_secs s).
Proof. intros s. rewrite refill_tree_cf_batch. repeat rs_step. Qed.

(* The exhausted bytes at the batch class: the tree's hole operations (cgif's map_more_user / ensure_free_array,
   YG00.v:270 / :275 / :288 / :292) act at offsets rg_mapped_user >= 0 and kFreeArrayOffset + rg_mapped_fa >= 0, never
   at the EXH_HOLE sentinel (-1, YG00cf.v:35-37), and the mapped sizes only grow; so on every returning path every
   class's exh_mem_cf is unchanged (refill_batch_exh).  With refill_batch_secs this is the batch class's FRAME of the
   leaf's exh_cell_cf / errb_cells_cf: the model values of both cell families are those of the call state. *)
Definition hsent (r : region) : bool := existsb (fun h => fst h =? EXH_HOLE) (rg_holes r).
Definition nn24 (s : astate) : Prop :=
length (st_regions s) = 32%nat /\ 0 <= rg_mapped_user (reg s kBatchClass) /\ 0 <= rg_mapped_fa (reg s kBatchClass).
Definition rx_same (s s' : astate) : Prop := map hsent (st_regions s') = map hsent (st_regions s) /\ nn24 s'.

Lemma exh_mem_hsent : forall s c, exh_mem_cf s c = nth (Z.to_nat c) (map hsent (st_regions s)) (hsent region0).
Proof. intros s c. unfold exh_mem_cf, reg, znth. rewrite map_nth. reflexivity. Qed.

Lemma sent_del : forall o l, o <> EXH_HOLE ->
  existsb (fun h => fst h =? EXH_HOLE) (del_hole o l) = existsb (fun h => fst h =? EXH_HOLE) l.
Proof.
intros o l Ho. unfold del_hole. induction l as [|[a b] t IH]; [reflexivity|].
cbn [List.filter existsb fst]. destruct (a =? o) eqn:E1; cbn [negb existsb fst].
- apply Z.eqb_eq in E1. subst a. rewrite IH. replace (o =? EXH_HOLE) with false by (symmetry; apply Z.eqb_neq; exact Ho).
  reflexivity.
- rewrite IH. reflexivity.
Qed.

Lemma sent_add : forall o n l, o <> EXH_HOLE ->
  existsb (fun h => fst h =? EXH_HOLE) (add_hole (o, n) l) = existsb (fun h => fst h =? EXH_HOLE) l.
Proof.
intros o n l Ho. unfold add_hole. cbn [existsb fst].
replace (o =? EXH_HOLE) with false by (symmetry; apply Z.eqb_neq; exact Ho). exact (sent_del o l Ho).
Qed.

Lemma map_lupd_same {X Y : Type} : forall (f : X -> Y) (l : list X) n v d, f v = f (nth n l d) -> map f (lupd l n v) = map f l.
Proof.
intros f l. induction l as [|x t IH]; intros n v d H; [reflexivity|].
destruct n as [|n']; cbn [lupd map nth] in *; [rewrite H; reflexivity | rewrite (IH n' v d H); reflexivity].
Qed.
Lemma length_lupd {X : Type} : forall (l : list X) n v, length (lupd l n v) = length l.
Proof. intros l. induction l as [|x t IH]; intros n v; [reflexivity|]. destruct n; cbn [lupd length]; [reflexivity | rewrite IH; reflexivity]. Qed.
Lemma nth_lupd_same {X : Type} : forall (l : list X) n v d, (n < length l)%nat -> nth n (lupd l n v) d = v.
Proof.
intros l. induction l as [|x t IH]; intros n v d H; cbn [length] in H; [lia|].
destruct n as [|n']; cbn [lupd nth]; [reflexivity | apply IH; lia].
Qed.

(* a set_region at the batch class that keeps the sentinel and the two mapped sizes non-negative *)
Lemma rx_set24 : forall s0 s r', map hsent (st_regions s) = map hsent (st_regions s0) -> nn24 s ->
  hsent r' = hsent (znth region0 kBatchClass (st_regions s)) -> 0 <= rg_mapped_user r' -> 0 <= rg_mapped_fa r' ->
  map hsent (zupd kBatchClass r' (st_regions s)) = map hsent (st_regions s0) /\
  nn24 (set_regions (zupd kBatchClass r' (st_regions s)) s).
Proof.
intros s0 s r' E (L & U & F) H U' F'. unfold nn24, reg, znth, zupd in *. cbn [st_regions set_regions].
assert (LT : (Z.to_nat kBatchClass < length (st_regions s))%nat) by (rewrite L; unfold kBatchClass; cbn; lia).
split; [rewrite (map_lupd_same hsent _ _ _ region0 H); exact E|].
split; [rewrite length_lupd; exact L|]. rewrite (nth_lupd_same _ _ _ _ LT). split; assumption.
Qed.

Lemma round_up_nonneg : forall x a, 0 <= x -> 0 < a -> 0 <= round_up x a.
Proof. intros x a Hx Ha. pose proof (round_up_ge x a Ha) as [[H _] _]. lia. Qed.

Create HintDb rxdb.

Ltac rx_unf :=
progress (unfold YG00.get_region, YG00.set_region, YG00.get_pc, YG00.set_pc, YG00.init_cache_if_needed,
YG00.bind, YG00.get, YG00.put, YG00.modify, YG00.askz, YG00.ret, YG00.mcheck, YG00.fail, YG00.spin, rx_same in *).

Ltac rx_hint :=
first
[ match goal with |- cfx_ipost (ibind _ _) _ =>
  apply cfx_ipost_ibind; eapply cfx_ipost_mono; [|solve [eauto with rxdb]];
  let x := fresh "x" in let sx := fresh "sx" in let H1 := fresh "Hx" in
  intros [x sx] H1; cbn [fst snd] in H1; unfold rx_same in H1; destruct H1 as (? & ?) end
| match goal with |- cfx_ipost _ _ =>
  eapply cfx_ipost_mono; [|solve [eauto with rxdb]];
  let x := fresh "x" in let sx := fresh "sx" in let H1 := fresh "Hx" in
  intros [x sx] H1; cbn [fst snd] in H1; unfold rx_same in H1; destruct H1 as (? & ?) end ].

Ltac rx_arith :=
repeat match goal with
| H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
| H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
| H : (_ <=? _) = true |- _ => apply Z.leb_le in H
| H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
| H : nn24 _ |- _ => let L := fresh "L" in let U := fresh "U" in let F := fresh "F" in destruct H as (L & U & F)
end;
unfold reg, znth in *;
try match goal with |- context [round_up ?x ?a] =>
  assert (0 <= round_up x a) by (apply round_up_nonneg; unfold kUserMapSize, kFreeArrayMapSize, kFreeArrayOffset in *; lia) end;
unfold EXH_HOLE, kUserMapSize, kFreeArrayMapSize, kFreeArrayOffset in *; lia.

Ltac rx_close :=
first
[ (split; [first [reflexivity | congruence] | assumption])
| (eapply rx_set24; [first [reflexivity | congruence] | assumption
   | unfold hsent; cbn [rg_holes];
     first [ reflexivity | apply sent_del; rx_arith | apply sent_add; rx_arith ]
   | cbn [rg_mapped_user]; rx_arith
   | cbn [rg_mapped_fa]; rx_arith ]) ].

Ltac rx_step :=
first
[ progress rq_cbn
| rx_unf
| progress intros
| match goal with |- cfx_ipost (ibind (ibind _ _) _) _ => apply cfx_ipost_ibind_assoc end
| rx_hint
| match goal with |- context [match ?x with _ => _ end] => destruct x eqn:? end
| exact I
| rx_close ].

Lemma rx_ensure : forall need sof s, nn24 s -> cfx_ipost (ensure_free_array kBatchClass need sof s) (fun r => rx_same s (snd r)).
Proof. intros need sof s N. unfold ensure_free_array. repeat rx_step. Qed.
#[local] Hint Resolve rx_ensure : rxdb.
Lemma rx_mmu : forall need s, nn24 s -> cfx_ipost (map_more_user kBatchClass need s) (fun r => rx_same s (snd r)).
Proof. intros need s N. unfold map_more_user. repeat rx_step. Qed.
#[local] Hint Resolve rx_mmu : rxdb.
Lemma rx_populate : forall need s, nn24 s -> cfx_ipost (populate kBatchClass need s) (fun r => rx_same s (snd r)).
Proof. intros need s N. unfold populate. repeat rx_step. Qed.
#[local] Hint Resolve rx_populate : rxdb.
Lemma rx_gfa : forall n s, nn24 s -> cfx_ipost (get_from_allocator kBatchClass n s) (fun r => rx_same s (snd r)).
Proof. intros n s N. unfold get_from_allocator. repeat rx_step. Qed.
#[local] Hint Resolve rx_gfa : rxdb.
Lemma rx_refill : forall s, nn24 s -> cfx_ipost (refill_if_empty kBatchClass s) (fun r => rx_same s (snd r)).
Proof. intros s N. unfold refill_if_empty. repeat rx_step. Qed.
#[local] Hint Resolve rx_refill : rxdb.

(* THE BATCH CLASS'S EXH FRAME: from a call state whose region table has 32 entries and whose batch-class mapped sizes
   are non-negative (Wf_cf's facts), every returning path of the batch tree keeps every class's exh_mem_cf. *)
Lemma refill_batch_exh : forall s, nn24 s ->
  cfx_ipost (refill_tree_cf kBatchClass s) (fun r => forall c, exh_mem_cf (snd r) c = exh_mem_cf s c).
Proof.
intros s N. rewrite refill_tree_cf_batch.
assert (P : cfx_ipost ((init_cache_if_needed ;; refill_if_empty kBatchClass) s) (fun r => rx_same s (snd r)))
  by (repeat rx_step).
eapply cfx_ipost_mono; [| exact P]. intros r (E & _) c. rewrite !exh_mem_hsent, E. reflexivity.
Qed.
Lemma cfx_ipost_conj {A : Type} : forall (t : itree astate A) (P Q : A -> Prop),
cfx_ipost t P -> cfx_ipost t Q -> cfx_ipost t (fun a => P a /\ Q a).
Proof.
induction t as [a | q sn k IH | pc | f]; cbn [cfx_ipost]; intros P Q HP HQ;
[exact (conj HP HQ) | intros z; exact (IH z P Q (HP z) (HQ z)) | exact I | exact I].
Qed.

(* Any all-paths model fact joins any amreal leaf (the induction of YG0d.amreal_mono). *)
Lemma amreal_ipost {R : Type} : forall (segs : list Segment) (t : itree astate R) (W : world segs) c
(Q : R -> world segs -> config -> Prop) (P : R -> Prop),
cfx_ipost t P -> amreal segs t W c Q -> amreal segs t W c (fun r W' c' => Q r W' c' /\ P r).
Proof.
intros segs t. induction t as [r | q s k IH | pc | f]; intros W c Q P HP H; cbn [amreal cfx_ipost] in *.
- eapply SRr_mono; [exact H | intros W' c' _ H'; exact (conj H' HP)].
- eapply SRr_mono; [exact H |]. intros W1 c1 _ Hk. destruct q;
  try (destruct Hk as (J & nx & bit & sp & i0 & Hn & Ht & Ha & Hs & Hb & Hr & Hz & Hc); exists J, nx, bit, sp, i0;
  split; [exact Hn|]; split; [exact Ht|]; split; [exact Ha|]; split; [exact Hs|]; split; [exact Hb|]; split; [exact Hr|];
  split; [exact Hz|]; intros i Hi; exact (IH (bit i) W1 (nx i) Q P (HP (bit i)) (Hc i Hi))).
  destruct Hk as (z & Hz & Hc). exists z. split; [exact Hz|]. exact (IH z W1 c1 Q P (HP z) Hc).
- exact H.
- exact I.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The tick transport (a Theorem Labs lane's YGcfRefillTick.v:36-49, commit 9031d3b24a79): the tick changes                  *)
(* st_nev only, and of the cf relation only amc_wf reads it, which YG02cf.WfP_cf_tick keeps.  The layer's one copy.  *)
Section tick.
Variable segs : list Segment.
Variable B : asyms.
Local Abbreviation tick S := (set_nev (st_nev S + 1) S).

Lemma ARmcf_tick : forall ly S Hp rd, ARmcf B ly S Hp rd -> ARmcf B ly (tick S) Hp rd.
Proof.
intros ly S Hp rd M.
destruct M as [Mwf Mun Msy Mly Mpl Mco Mcow Mce Mfa Mfl Mde Msh Mzs Mju Mar Mcl Mze Mts Msi Mhp Mxs Mex Mer Mow Mpf Mpo].
constructor; try assumption; try (destruct S; assumption).
exact (WfP_cf_tick _ 0 0 0 S Mwf).
Qed.

Lemma ARcf_tick : forall ly S Hp W mem md, ARcf segs B ly S Hp W mem md -> ARcf segs B ly (tick S) Hp W mem md.
Proof.
intros ly S Hp W mem md (M & L & BU & MW & HS).
refine (conj (ARmcf_tick ly S Hp _ M) _).
split; [destruct S; destruct L; constructor; assumption|].
split; [exact (abudget_ok_cf_frame segs ly S (tick S) W eq_refl eq_refl eq_refl eq_refl BU)|].
split; [exact MW|]. destruct S; exact HS.
Qed.
End tick.

(* Wf_cf with one user map of credit at Enqueue's call state: X = qx S0 k z tr is Deallocate's entry state S0 after
   its tick, the depot answer and the chunk's change (DGif0.v:72-78), none of which maps user memory, so the credit
   WfP_cf_tick' gives at the ticked state is X's (the proof of CfF1's enq_tick_bounds_cf, as a WfP_cf field). *)
Lemma WfP_cf_qx : forall U S0 k z tr, Wf_cf U S0 -> Wf_cf U (DGif0.qx S0 k z tr) -> WfP_cf U 1 0 0 (DGif0.qx S0 k z tr).
Proof.
intros U S0 k z tr W0 WX. pose proof (WfP_cf_tick' U S0 W0) as WT.
wfc_fields WX. constructor; try assumption.
- unfold DGif0.qx, ImgBaseDG.YFl0C.depot_after, DGif0.dtick. destruct (z =? 0); exact (wfc_prim_ev _ _ _ _ _ WT).
- lia.
Qed.

Section b.
Variable B : asyms.
(* the unit's instance object (YGcfInstBase's IOK) *)
Variable IOK : Z -> Prop.

(* The walk's leaf: ARcf, the errbuf mapped and the two machine cells, ARmcf's fields since field round 2 (the per-class
   exhausted bytes and the error-message buffer's object, YG0ncf.exh_cell_cf / errb_cells_cf) at the result over a grown
   layout and world, the view and the raw frames outside the allocator's owned set at S0 and at the result and the
   refill's stack window, the memnorm keep, the window present, and a0 = 1 iff the class's cache is non-empty.  The
   model facts of the result (qtight, the caches inited, the blocks) and errno are the interface instance's
   (YGcfInstMiss). *)
Definition rwalk_leaf_cf (Hp : list Z) (ly : alayout) (S0 : astate) (cl : Z) (W : world im_segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (r : unit * astate) (W' : world im_segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
ARcf im_segs B ly' (snd r) Hp W' mem' md' /\ xs_mapped_cf ly' (snd r) md' /\
exh_cell_cf B ly' (snd r) (aview im_segs (w_H W') mem') /\ errb_cells_cf B ly' (snd r) (aview im_segs (w_H W') mem') /\
layout_le (length (st_secs S0)) ly ly' /\ wle W W' /\ aregs_preserved regs regs' /\ same_io md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ AOX_cf B ly S0 a -> ~ AOX_cf B ly' (snd r) a -> ~ (spZ regs - REP_STACK <= a < spZ regs) ->
   aview im_segs (w_H W') mem' a = aview im_segs (w_H W) mem a) /\
(forall x : word, ~ AOX_cf B ly S0 (bv_unsigned x) -> ~ AOX_cf B ly' (snd r) (bv_unsigned x) ->
   ~ (spZ regs - REP_STACK <= bv_unsigned x < spZ regs) -> mem' x = mem x) /\
MemnormT.memnorm_keep im_segs mem mem' /\
(forall a, spZ regs - REP_STACK <= a < spZ regs -> apresent (w_H W') mem' a) /\
getr regs' 10 = w64 (match pc_chunks (cache (snd r) cl) with [] => 0 | _ => 1 end).

(* What the unit's refill walk proves.  Field round 3 (Main 2026-10-30): at the call state the walk also has the
   overlay normal form, arodata_ok_cf (YG0dcf.v; the class-full report reads the image's read-only bytes and the
   silent word through ro_byte_read_cf / arodata_byte_cf) and the driver's hull admission (for the class-full B3
   case); the leaf keeps memnorm (:458) and arodata (YGcfRodata.rwalk_leaf_arodata_cf). *)
Definition refill_walk_cf : Prop :=
forall Hp inst ly S0 W mem md n (sp0 : Z) (regs : bvmap 5 word),
ARXq_cf B IOK Hp inst ly S0 W mem md -> rpre_cf B S0 n -> 0 <= n -> from_primary n = true ->
pc_chunks (cache S0 (chunk_class n)) = [] ->
arodata_ok_cf im_segs B mem -> cf_hull_ok S0 ->
ly_stk_lo ly + AFSTACK <= sp0 -> ly_bot ly < sp0 -> sp0 <= ly_stk_hi ly -> sp0 mod 16 = 0 ->
(forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem a) ->
spZ regs = sp0 - 176 -> getr regs 1 = w64 ag_refill_ret -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 im_tp ->
getr regs 10 = w64 (ly_T ly + t_cache) -> getr regs 11 = w64 (ly_T ly + t_cache + 80 * chunk_class n) ->
getr regs 12 = w64 inst -> getr regs 13 = w64 (chunk_class n) ->
amreal im_segs (refill_tree_cf (chunk_class n) (set_nev (st_nev S0 + 1) S0)) W
  (cfg_at im_segs ag_refill regs mem md)
  (rwalk_leaf_cf Hp ly S0 (chunk_class n) W regs mem md).

(* ================================================================================================================ *)
(* THE CALL-SITE-GENERIC REFILL CONTRACT.                                                                           *)

(* The state the refill needs, at the CALL state S: the relation (by name), Wf_cf with one user map of credit (the
   tree maps at most one kUserMapSize with no tick of its own; Allocate's entry tick gives it by WfP_cf_tick',
   Enqueue's by its call-state bound, YGcfInstEnq.enq_pre_tick_cf), the loose quarantine (mroom_cf from it,
   YGcfInstBase.ARX_cf_mroom), the class room as the model branches (map_more_user_cf, YG00cf.v:159-179: the batch
   class keeps cgif's vacuous class-full arm, so it needs batch_room_cf; every other class takes the class-full report
   path, which writes the errbuf, so it needs ERRB_ROOM and one spare event for the report's first append,
   errb_append_cf_ok's premise, YG06bcf.v:321-323: WfP_cf .. 1 1 0), the class, and the empty cache.  NO qtight.
   The spare event sits with ERRB_ROOM, not in the second conjunct: Enqueue's site (the batch class, no report path)
   cannot carry cc = 1 at its state qx S0 k z tr, whose chunks are upd_chunk .. (qk k) (DGif0.v:73-74) and upd_chunk
   appends k when its ck_beg is absent (YG00.v:224-227), a fact the site's premise does not exclude. *)
Definition refill_state_gen_cf (Hp : list Z) (inst : Z) (ly : alayout) (S : astate) (W : world im_segs)
(mem : word -> option byte) (md : Model) (c : Z) : Prop :=
ARX_cf B IOK Hp inst ly S W mem md /\ WfP_cf (as_universe B) 1 0 0 S /\ qloose S /\
(c = kBatchClass -> batch_room_cf S) /\ (c <> kBatchClass -> ERRB_ROOM S /\ WfP_cf (as_universe B) 1 1 0 S) /\
1 <= c <= 31 /\ pc_chunks (cache S c) = [].

(* The call: cgif's refill_pre registers (YFl1.v:31-37), the allocator object as the walk's [inst], the window
   REP_W c. *)
Definition refill_call_gen_cf (inst : Z) (ly : alayout) (W : world im_segs) (regs : bvmap 5 word)
(mem : word -> option byte) (c : Z) : Prop :=
YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + REP_W c <= spZ regs /\ spZ regs <= ly_stk_hi ly /\
(forall a, spZ regs - REP_W c <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 im_tp /\
getr regs 10 = w64 (ly_T ly + t_cache) /\ getr regs 11 = w64 (ly_T ly + t_cache + 80 * c) /\
getr regs 12 = w64 inst /\ getr regs 13 = w64 c.

(* The class-full exception of the frames: for a class other than the batch class the report path writes the errbuf
   (its vector cells and its buffer), inside AOX_cf at one end or the other; the batch class has no such path, so its
   exception is empty, exactly LEAF_B2's (fun _ => False). *)
Definition refill_exc_cf (c : Z) (ly : alayout) (S : astate) (ly' : alayout) (S' : astate) (a : Z) : Prop :=
c <> kBatchClass /\ (AOX_cf B ly S a \/ AOX_cf B ly' S' a).

(* The machine leaf, what the unit's walk proves: LEAF_B2's acall_post_cf over REP_W c and refill_exc_cf at a
   grown layout (the errbuf map adds a secondary entry), the a0 cache bit, the layout unchanged when the cache was
   filled (EnqGbase.enq_leaf_g0 states its post at the entry layout), the errbuf mapped and the two machine cells
   (ARmcf's fields exh_cell_cf / errb_cells_cf) at the result, errno's view kept (acall_post_cf excepts errno as scratch),
   the raw frame, the stack below the window kept present where it was (so a caller with the wider REP_STACK window,
   Allocate's, keeps it; vacuous unless c = kBatchClass), and the memnorm keep. *)
Definition refill_leaf_core_cf (Hp : list Z) (ly : alayout) (S : astate) (c : Z) (W : world im_segs)
(regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (r : unit * astate) (W' : world im_segs)
(c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
acall_post_cf im_segs B (REP_W c) ly S Hp W regs mem md (refill_exc_cf c ly S ly' (snd r)) ly' (snd r) W' regs' mem' md' /\
getr regs' 10 = w64 (match pc_chunks (cache (snd r) c) with [] => 0 | _ => 1 end) /\
(getr regs' 10 = w64 1 -> ly' = ly) /\
xs_mapped_cf ly' (snd r) md' /\
exh_cell_cf B ly' (snd r) (aview im_segs (w_H W') mem') /\ errb_cells_cf B ly' (snd r) (aview im_segs (w_H W') mem') /\
(forall a, 0 <= a < 2 ^ 64 -> as_errno B <= a < as_errno B + 4 -> ~ aowned B ly S a -> ~ aowned B ly' (snd r) a ->
   ~ (spZ regs - REP_W c <= a < spZ regs) -> ~ refill_exc_cf c ly S ly' (snd r) a ->
   aview im_segs (w_H W') mem' a = aview im_segs (w_H W) mem a) /\
(forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ aowned B ly' (snd r) (bv_unsigned x) ->
   ~ (spZ regs - REP_W c <= bv_unsigned x < spZ regs) -> ~ refill_exc_cf c ly S ly' (snd r) (bv_unsigned x) ->
   mem' x = mem x) /\
(forall a, ly_stk_lo ly <= a -> spZ regs - REP_STACK <= a < spZ regs - REP_W c -> apresent (w_H W) mem a ->
   apresent (w_H W') mem' a) /\
MemnormT.memnorm_keep im_segs mem mem'.

(* The model clause: the refill keeps the chunks and both quarantine caches (so quar_n, queued_n, all_batches and
   qtight / EP_cf of the caller carry over) and leaves the caches inited.  A MODEL fact of refill_tree_cf. *)
Definition refill_q_cf (S S' : astate) : Prop :=
st_chunks S' = st_chunks S /\ st_qthread S' = st_qthread S /\ st_qglobal S' = st_qglobal S /\
st_cache_inited S' = true.

(* The batch clause: at kBatchClass the refill keeps the secondary table (refill_batch_secs), so the errbuf and the
   caller's xs_cf are unchanged. *)
Definition refill_batch_cf (c : Z) (S S' : astate) : Prop := c = kBatchClass -> st_secs S' = st_secs S.

Definition refill_leaf_gen_cf (Hp : list Z) (ly : alayout) (S : astate) (c : Z) (W : world im_segs)
(regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (r : unit * astate) (W' : world im_segs)
(c' : config) : Prop :=
refill_leaf_core_cf Hp ly S c W regs mem md r W' c' /\ refill_q_cf S (snd r) /\ refill_batch_cf c S (snd r).

(* What the unit's refill walk proves (the machine leaf only).  The three call-state facts of field round 3 as in
   refill_walk_cf. *)
Definition refill_spec_core_cf : Prop :=
forall Hp inst ly S W regs mem md c,
refill_state_gen_cf Hp inst ly S W mem md c ->
arodata_ok_cf im_segs B mem -> cf_hull_ok S ->
refill_call_gen_cf inst ly W regs mem c ->
amreal im_segs (refill_tree_cf c S) W (cfg_at im_segs ag_refill regs mem md) (refill_leaf_core_cf Hp ly S c W regs mem md).

(* THE CONTRACT every caller cites (the model clauses added from the model, refill_spec_cf_of_core). *)
Definition refill_spec_cf : Prop :=
forall Hp inst ly S W regs mem md c,
refill_state_gen_cf Hp inst ly S W mem md c ->
arodata_ok_cf im_segs B mem -> cf_hull_ok S ->
refill_call_gen_cf inst ly W regs mem c ->
amreal im_segs (refill_tree_cf c S) W (cfg_at im_segs ag_refill regs mem md) (refill_leaf_gen_cf Hp ly S c W regs mem md).

(* The unit's image obligation for Allocate's site: the return address into Allocate is a valid return target. *)
Definition ag_refill_ret_ok : Prop := YK0s.ret_ok (w64 ag_refill_ret) /\ 4096 <= bv_unsigned (w64 ag_refill_ret).

(* ================================================================================================================ *)
(* The model clause, from the model, and the contract from the walk.                                                *)

(* THE QUARANTINE CLAUSE of [refill_spec_cf]: every returning path of the tree satisfies refill_q_cf. *)
Lemma refill_tree_cf_q : forall c s, cfx_ipost (refill_tree_cf c s) (fun r => refill_q_cf s (snd r)).
Proof. intros c s. unfold refill_tree_cf, refill_q_cf. repeat rq_step. Qed.

(* What a caller gets from the clause: its quarantine counts, its batches and its qtight carry over. *)
Lemma refill_q_cf_keep : forall S S', refill_q_cf S S' ->
quar_n S' = quar_n S /\ queued_n S' = queued_n S /\ all_batches S' = all_batches S /\ (qtight S -> qtight S').
Proof.
intros S S' (E1 & E2 & E3 & _).
assert (Q : qtight S -> qtight S') by exact (qtight_ext S S' E1 E2 E3).
unfold quar_n, queued_n, q_items, all_batches. rewrite E1, E2, E3. auto.
Qed.

(* The batch clause on every returning path (refill_batch_secs at kBatchClass; vacuous otherwise). *)
Lemma refill_tree_cf_batch_cl : forall c s, cfx_ipost (refill_tree_cf c s) (fun r => refill_batch_cf c s (snd r)).
Proof.
intros c s. destruct (Z.eq_dec c kBatchClass) as [->|N].
- eapply cfx_ipost_mono; [| exact (refill_batch_secs s)]. intros r E _. exact E.
- eapply cfx_ipost_mono; [| exact (refill_tree_cf_q c s)]. intros r _ E. exfalso. exact (N E).
Qed.

(* The contract from the walk: the walk proves the machine leaf, the model gives the two clauses (the quarantine
   clause, and the batch clause that is REP_W's soundness at kBatchClass). *)
Lemma refill_spec_cf_of_core : refill_spec_core_cf -> refill_spec_cf.
Proof.
intros H Hp inst ly S W regs mem md c HS AD HO HC.
exact (amreal_ipost im_segs _ W _ _ _ (cfx_ipost_conj _ _ _ (refill_tree_cf_q c S) (refill_tree_cf_batch_cl c S))
  (H Hp inst ly S W regs mem md c HS AD HO HC)).
Qed.

(* The owned set is inside AOX_cf (its first disjunct, YGcfMallocCompose.v:108). *)
Lemma aowned_AOX_cf : forall ly S a, aowned B ly S a -> AOX_cf B ly S a.
Proof. intros ly S a H. unfold AOX_cf, AOXm_cf. left. exact H. Qed.

(* The machine leaf gives rwalk_leaf_cf at the same start state, for a caller whose REP_STACK window was present at
   the call (Allocate's): outside AOX_cf at both ends a byte is neither owned nor in the class-full exception; the
   REP_W c window lies inside the REP_STACK one (REP_W_le); errno's bytes take the errno clause, the others
   acall_post_cf's frame; presence below the REP_W c window is the keep clause's. *)
Lemma refill_leaf_core_rwalk : forall Hp ly S c W regs mem md r W' c',
ly_stk_lo ly + REP_STACK <= spZ regs -> (forall a, spZ regs - REP_STACK <= a < spZ regs -> apresent (w_H W) mem a) ->
refill_leaf_core_cf Hp ly S c W regs mem md r W' c' -> rwalk_leaf_cf Hp ly S c W regs mem md r W' c'.
Proof.
intros Hp ly S c W regs mem md r W' c' SLO PRC
  (ly' & regs' & mem' & md' & Ec & P & A0 & _ & XM & EXC & ERC & ERR & RAW & KEEP & MK).
destruct P as (AR & LE & WL & RP & IO & VF & PR).
pose proof (REP_W_le c) as RW.
assert (NO : forall l s a, ~ AOX_cf B l s a -> ~ aowned B l s a) by (intros l s a N O; exact (N (aowned_AOX_cf l s a O))).
assert (NE : forall a, ~ AOX_cf B ly S a -> ~ AOX_cf B ly' (snd r) a -> ~ refill_exc_cf c ly S ly' (snd r) a)
  by (intros a N1 N2 [_ [O|O]]; [exact (N1 O) | exact (N2 O)]).
assert (NW : forall a, ~ (spZ regs - REP_STACK <= a < spZ regs) -> ~ (spZ regs - REP_W c <= a < spZ regs))
  by (intros a N H; apply N; lia).
exists ly', regs', mem', md'.
split; [exact Ec|]. split; [exact AR|]. split; [exact XM|]. split; [exact EXC|]. split; [exact ERC|].
split; [exact LE|]. split; [exact WL|].
split; [exact RP|]. split; [exact IO|].
split.
{ intros a Ra N1 N2 N3. pose proof (NW a N3) as N3'.
  destruct (Z_le_gt_dec (as_errno B) a) as [E1|E1]; [destruct (Z_lt_ge_dec a (as_errno B + 4)) as [E2|E2]|].
  - exact (ERR a Ra (conj E1 E2) (NO _ _ _ N1) (NO _ _ _ N2) N3' (NE a N1 N2)).
  - apply VF; [exact Ra | exact (NO _ _ _ N1) | exact (NO _ _ _ N2) | | exact (NE a N1 N2)].
    unfold ascratch. intros [H|H]; [exact (N3' H) | lia].
  - apply VF; [exact Ra | exact (NO _ _ _ N1) | exact (NO _ _ _ N2) | | exact (NE a N1 N2)].
    unfold ascratch. intros [H|H]; [exact (N3' H) | lia]. }
split; [intros x N1 N2 N3; exact (RAW x (NO _ _ _ N1) (NO _ _ _ N2) (NW _ N3) (NE _ N1 N2))|].
split; [exact MK|].
split; [|exact A0].
intros a Ha. destruct (Z_lt_le_dec a (spZ regs - REP_W c)) as [L|L].
- exact (KEEP a ltac:(lia) (conj (proj1 Ha) L) (PRC a Ha)).
- exact (PR a (conj L (proj2 Ha))).
Qed.

(* The relation across Allocate's entry tick (the conjuncts after ARcf read no st_nev). *)
Lemma ARX_cf_tick : forall Hp inst ly S W mem md, ARX_cf B IOK Hp inst ly S W mem md ->
ARX_cf B IOK Hp inst ly (set_nev (st_nev S + 1) S) W mem md.
Proof.
intros Hp inst ly S W mem md H. unfold ARX_cf in *. destruct H as (I & A & R).
split; [exact I|]. split; [exact (ARcf_tick im_segs B ly S Hp W mem md A)|]. destruct S; exact R.
Qed.

(* ---- Allocate's site (AGif0n.v:283-298): the call state is Allocate's entry state S0 after its tick. ---- *)
Lemma refill_state_gen_tick : forall Hp inst ly S0 W mem md n,
ARXq_cf B IOK Hp inst ly S0 W mem md -> rpre_cf B S0 n -> 0 <= n -> from_primary n = true ->
pc_chunks (cache S0 (chunk_class n)) = [] ->
refill_state_gen_cf Hp inst ly (set_nev (st_nev S0 + 1) S0) W mem md (chunk_class n).
Proof.
intros Hp inst ly S0 W mem md n HQ HR Hn Hfp Hemp.
unfold rpre_cf, rpre_cfr, ROOM_cf in HR. destruct HR as (_ & HW & (_ & HE & HB) & _).
pose proof (proj1 (primary_geometry n Hn Hfp)) as Hc.
pose proof (ARXq_cf_qtight B IOK Hp inst ly S0 W mem md HQ) as QT.
unfold refill_state_gen_cf.
split; [exact (ARX_cf_tick Hp inst ly S0 W mem md (ARXq_cf_ARX B IOK Hp inst ly S0 W mem md HQ))|].
split; [exact (WfP_cf_weaken _ 1 1 1 1 0 0 _ (WfP_cf_tick' _ S0 HW) ltac:(lia) ltac:(lia) ltac:(lia))|].
split; [pose proof (qtight_qloose S0 QT) as QL; destruct S0; exact QL|].
split; [intros _; destruct S0; exact HB|].
split; [intros _; split; [destruct S0; exact HE | exact (WfP_cf_weaken _ 1 1 1 1 1 0 _ (WfP_cf_tick' _ S0 HW) ltac:(lia) ltac:(lia) ltac:(lia))]|].
split; [lia|]. destruct S0; exact Hemp.
Qed.

Lemma refill_call_gen_alloc : ag_refill_ret_ok -> forall inst ly W (regs : bvmap 5 word) mem c (sp0 : Z),
ly_stk_lo ly + AFSTACK <= sp0 -> sp0 <= ly_stk_hi ly -> sp0 mod 16 = 0 ->
(forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem a) ->
spZ regs = sp0 - 176 -> getr regs 1 = w64 ag_refill_ret -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 im_tp ->
getr regs 10 = w64 (ly_T ly + t_cache) -> getr regs 11 = w64 (ly_T ly + t_cache + 80 * c) ->
getr regs 12 = w64 inst -> getr regs 13 = w64 c ->
refill_call_gen_cf inst ly W regs mem c.
Proof.
intros [RO R4] inst ly W regs mem c sp0 Hlo Hhi Hal Hpres Hsp Hra Hgp Htp Ha0 Ha1 Ha2 Ha3.
pose proof (REP_W_le c) as RW. pose proof REP_STACK_le as RS.
unfold refill_call_gen_cf, raZ. rewrite Hsp, Hra.
split; [exact RO|]. split; [exact R4|].
split; [replace (sp0 - 176) with (sp0 + (-11) * 16) by lia; rewrite Z_mod_plus_full; exact Hal|].
split; [unfold AFSTACK in Hlo; lia|]. split; [lia|].
split; [intros a Ha; apply Hpres; unfold AFSTACK; lia|].
exact (conj Hgp (conj Htp (conj Ha0 (conj Ha1 (conj Ha2 Ha3))))).
Qed.

(* THE COROLLARY: Allocate's refill walk (refill_walk_cf, text above) from the generic contract.  The tick is
   Allocate's (malloc_cf's own), the registers Allocate's (ag_refill_ret, sp0 - 176 inside AFSTACK), and the leaf at
   the ticked call state is the leaf at S0 (rwalk_leaf_cf reads its start state only through AOX_cf and
   length (st_secs ..)).  qtight at the result is the interface instance's, from refill_q_cf (refill_q_cf_keep). *)
Theorem refill_walk_cf_of_spec : ag_refill_ret_ok -> refill_spec_cf -> refill_walk_cf.
Proof.
intros RET HS Hp inst ly S0 W mem md n sp0 regs HQ HR Hn Hfp Hemp AD HO Hlo _ Hhi Hal Hpres Hsp Hra Hgp Htp Ha0 Ha1 Ha2 Ha3.
pose proof (refill_state_gen_tick Hp inst ly S0 W mem md n HQ HR Hn Hfp Hemp) as ST.
pose proof (refill_call_gen_alloc RET inst ly W regs mem (chunk_class n) sp0 Hlo Hhi Hal Hpres Hsp Hra Hgp Htp Ha0 Ha1 Ha2 Ha3)
  as CA.
assert (SLO : ly_stk_lo ly + REP_STACK <= spZ regs) by (pose proof REP_STACK_le; rewrite Hsp; unfold AFSTACK in Hlo; lia).
assert (PRC : forall a, spZ regs - REP_STACK <= a < spZ regs -> apresent (w_H W) mem a)
  by (pose proof REP_STACK_le; intros a Ha; apply Hpres; rewrite Hsp in Ha; unfold AFSTACK; lia).
(* the admission at the ticked call state: the tick keeps st_secs, so both meters (CfParams.cf_hull_counts) *)
pose proof (cf_hull_counts (set_nev (st_nev S0 + 1) S0) S0 eq_refl eq_refl HO) as HO1.
eapply amreal_mono; [| exact (HS Hp inst ly _ W regs mem md _ ST AD HO1 CA)].
intros r W' c' [L _]. pose proof (refill_leaf_core_rwalk _ _ _ _ _ _ _ _ _ _ _ SLO PRC L) as RWL. destruct S0; exact RWL.
Qed.

(* ---- Satisfiability of the walk's STATE premises at a start state.  (The register and stack premises are the call
   site's, as AIfaceM.if_refill states them; a unit's witness instantiates them at its own call.) ---- *)
(* Generic: wherever the call-site relation holds and ROOM_cf and the hull admission hold, rpre holds, so the state
   premises reduce to ARXq_cf, ROOM_cf, cf_hull_ok and the empty cache.  A unit instantiates it at its own start
   state (preset below; reply's at A/AD26.v:215 through lane W's init_state lemma). *)
Lemma refill_state_start : forall Hp inst ly S W mem md n,
  ARXq_cf B IOK Hp inst ly S W mem md -> ROOM_cf S -> cf_hull_ok S -> rpre_cf B S n.
Proof.
intros Hp inst ly S W mem md n H R HO.
destruct (ARXq_cf_ARcf B IOK Hp inst ly S W mem md H) as (M & _).
exact (conj (amc_universe _ _ _ _ _ M) (conj (amc_wf _ _ _ _ _ M) (conj R HO))).
Qed.

(* Preset's start state: the first miss of the run, at init_state, with the empty ghost set. *)
Lemma refill_state_nil_init : forall inst ly (W : world im_segs) mem md n,
  IOK inst -> AR im_segs B ly init_state W mem md -> AI im_segs (w_H W) (w_A W) md ->
  start_cells_cf im_segs B ly init_state W mem -> start_pf_cf im_segs B ly W mem ->
  (forall x, YK0g.covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x = true -> YK0g.covered (vm_maps (m_vmmaps md)) x = true) ->
  EXH_OFF_t /\ errb_obj_owned_t B /\ errb_ial_apart_t B -> pf_cells_owned_t B ->
  exists W', wle W W' /\ AI im_segs (w_H W') (w_A W') md /\
  ARXq_cf B IOK [] inst ly init_state W' mem md /\ rpre_cf B init_state n /\
  pc_chunks (cache init_state (chunk_class n)) = [].
Proof.
intros inst ly W mem md n I A HAI CELLS PFC LM HO HPO.
destruct (ARXq_cf_nil_init B IOK inst ly W mem md I A HAI CELLS PFC LM HO HPO) as (W' & L & HAI' & HQ).
exists W'. split; [exact L|]. split; [exact HAI'|]. split; [exact HQ|].
split; [exact (refill_state_start [] inst ly init_state W' mem md n HQ ROOM_cf_init cf_hull_ok_init)|].
unfold cache. cbn [st_cache init_state]. unfold znth. rewrite nth_repeat. reflexivity.
Qed.

(* ---- WITNESS at Allocate's site, at preset's real start (YGcfNilInit.ARcf_nil_init): the first miss of the run,
   at init_state, the empty ghost set.  The register premises are Allocate's call (refill_call_gen_alloc). ---- *)
Lemma refill_state_gen_nil_init : forall inst ly (W : world im_segs) mem md n,
  IOK inst -> AR im_segs B ly init_state W mem md -> AI im_segs (w_H W) (w_A W) md ->
  start_cells_cf im_segs B ly init_state W mem -> start_pf_cf im_segs B ly W mem ->
  0 <= n -> from_primary n = true ->
  (forall x, YK0g.covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x = true -> YK0g.covered (vm_maps (m_vmmaps md)) x = true) ->
  EXH_OFF_t /\ errb_obj_owned_t B /\ errb_ial_apart_t B -> pf_cells_owned_t B ->
  exists W', wle W W' /\ AI im_segs (w_H W') (w_A W') md /\
  refill_state_gen_cf [] inst ly (set_nev (st_nev init_state + 1) init_state) W' mem md (chunk_class n).
Proof.
intros inst ly W mem md n I A HAI CELLS PFC Hn Hfp LM HO HPO.
destruct (refill_state_nil_init inst ly W mem md n I A HAI CELLS PFC LM HO HPO) as (W' & L & HAI' & HQ & HR & HE).
exists W'. split; [exact L|]. split; [exact HAI'|].
exact (refill_state_gen_tick [] inst ly init_state W' mem md n HQ HR Hn Hfp HE).
Qed.

(* The unit's image fact for Enqueue's site: the symbol table's thread pointer is the image's (refill_call_gen_cf
   states tp as Allocate's interface does, w64 im_tp; Enqueue's pre gives w64 (as_tp B)).  An IMAGE row of the unit
   hypotheses (cgif: AImg_cgif's im_tp := TFIB_TP, AGif2cgif.v:30, with TfibSyms' ts_tp, YF0m.v:293). *)
Definition tp_img_t : Prop := as_tp B = im_tp.

(* ---- WITNESS at Enqueue's miss arm inside Deallocate (cgif YFg6.v:272-279; the cf call state is CfF1's, commit
   f8bbf53382b1): the hypotheses are exactly what enq_pre_cf (YGcfInstEnq.v:134-145) and its call
   segment give at the refill call, NO qtight among them (quar_n X = queued_n X + ck_n k there): ARX_cf (:136),
   batch_room_cf (:136), qloose (:145), X as Deallocate's ticked entry state qx S0 .. with Wf_cf S0 (:137), the miss
   arm's empty batch cache, the call's registers (YFh5.at_CALLR, sp = Enqueue's entry sp - 64), and Enqueue's own
   stack window CLenq.QSTACK_G = 64 + REP_W kBatchClass (REP_W_enq).  ERRB_ROOM is not needed: the batch class has
   no report path. ---- *)
Lemma refill_gen_enq_site : forall Hp inst ly X W mem md (regs : bvmap 5 word) (spE : Z),
  ARX_cf B IOK Hp inst ly X W mem md -> batch_room_cf X -> qloose X ->
  (exists S0 k0 z tr, X = DGif0.qx S0 k0 z tr /\ Wf_cf (as_universe B) S0) ->
  pc_chunks (cache X kBatchClass) = [] ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  spE mod 16 = 0 -> ly_stk_lo ly + CLenq.QSTACK_G <= spE -> spE <= ly_stk_hi ly ->
  (forall a, spE - CLenq.QSTACK_G <= a < spE -> apresent (w_H W) mem a) ->
  spZ regs = spE - 64 ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> tp_img_t ->
  getr regs 10 = w64 (ly_T ly + t_cache) -> getr regs 11 = w64 (ly_T ly + t_cache + 80 * kBatchClass) ->
  getr regs 12 = w64 inst -> getr regs 13 = w64 kBatchClass ->
  refill_state_gen_cf Hp inst ly X W mem md kBatchClass /\ refill_call_gen_cf inst ly W regs mem kBatchClass.
Proof.
intros Hp inst ly X W mem md regs spE HA HB QL HX Hemp RO R4 Hal Hlo Hhi Hpres Hsp Hgp Htp ETP Ha0 Ha1 Ha2 Ha3.
pose proof REP_W_enq as RE.
split.
- unfold refill_state_gen_cf.
  split; [exact HA|].
  split; [destruct HX as (S0 & k0 & z & tr & -> & W0);
          exact (WfP_cf_qx _ S0 k0 z tr W0 (ARX_cf_wf B IOK Hp inst ly _ W mem md HA))|].
  split; [exact QL|]. split; [intros _; exact HB|]. split; [intros N; exfalso; exact (N eq_refl)|].
  split; [unfold kBatchClass; lia | exact Hemp].
- unfold refill_call_gen_cf. rewrite Hsp.
  split; [exact RO|]. split; [exact R4|].
  split; [replace (spE - 64) with (spE + (-4) * 16) by lia; rewrite Z_mod_plus_full; exact Hal|].
  split; [lia|]. split; [lia|].
  split; [intros a Ha; apply Hpres; lia|].
  unfold tp_img_t in ETP. rewrite <- ETP. exact (conj Hgp (conj Htp (conj Ha0 (conj Ha1 (conj Ha2 Ha3))))).
Qed.

End b.
End a.
