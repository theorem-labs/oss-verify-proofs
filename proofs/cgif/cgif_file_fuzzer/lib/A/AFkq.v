(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0s YK0i YP09 YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI04 YK18.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG0f YG0v YG0n YG0d YG0k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0l YG0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0m AFl1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YFfj YFfk.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Open Scope am_scope.
Definition refill_post (U : list (list Z)) (pp cc bb : Z) (s : astate) (c : Z) (ns : bool) (r : unit * astate) : Prop :=
WfP U (pp - 1) cc bb (snd r) /\ regs_only s (snd r) /\ st_cache_inited (snd r) = true /\
(pc_chunks (cache (snd r) c) = [] -> ns = false).
Lemma refill_tree_ok : forall U pp cc bb s c ns,
WfP U pp cc bb s -> 1 <= c <= 31 -> 1 <= pp -> preg s c   ->
atok ns (refill_tree c s) (refill_post U pp cc bb s c).
Proof.
intros U pp cc bb s c ns W Hc Hpp Hreg.
pose proof (class_ok c Hc) as (Ksz & K32 & Kmax & Kmc & Kmc2 & Kmcs).
unfold refill_tree. apply atok_bind. unfold init_cache_if_needed. apply atok_bind. apply atok_get. cbn [fst snd].
assert (STEP1 : forall s1, WfP U pp cc bb s1 -> st_cache_inited s1 = true -> regs_only s s1 ->
st_regions s1 = st_regions s -> cdef s1 c = cdef s c -> atok ns (refill_if_empty c s1) (refill_post U pp cc bb s c)).
2:{ destruct (st_cache_inited s) eqn:Ei.
- apply atok_ret. apply (STEP1 s W Ei (regs_only_refl s) eq_refl eq_refl).
- apply atok_put. apply STEP1; [apply WfP_init_caches; [exact W | exact Ei] | reflexivity | unfold regs_only; cbn; repeat split; reflexivity | reflexivity |].
cbn [fst snd]. apply cdef_ext; [reflexivity|]. unfold class_elems. rewrite (cache_after_init s c ltac:(lia)). reflexivity. }
intros s1 W1 Hi1 RO1 ER1 DEF1.
assert (HL : (Z.to_nat c < length (st_regions s1))%nat) by (eapply WfP_len_regions; [exact W1 | lia]).
assert (HLc : (Z.to_nat c < length (st_cache s1))%nat) by (eapply WfP_len_cache; [exact W1 | lia]).
pose proof (wf_classes _ _ _ _ _ W1 c Hc) as C1. unfold wf_class in C1. rewrite Hi1 in C1.
pose proof (wr_cache _ _ _ _ _ _ C1) as [PM1 PL1].
unfold refill_if_empty. apply atok_bind. apply atok_get_pc. cbn [fst snd].
destruct (pc_chunks (cache s1 c)) as [|o l] eqn:El.
-
rewrite PM1. apply atok_bind.
assert (N1 : 1 <= max_cached c / 2) by (apply Z.div_le_lower_bound; lia).
assert (N8 : max_cached c / 2 <= 8) by (apply Z.div_le_upper_bound; lia).
assert (N3 : max_cached c / 2 <= max_cached c) by (apply Z.div_le_upper_bound; lia).
eapply atok_mono; [|apply (get_from_allocator_ok U pp cc bb s1 c (max_cached c / 2) ns W1 Hc Hpp); [exact N1 | exact Kmcs | exact N8 | exact (preg_room U pp cc bb s s1 c (max_cached c / 2) W1 Hc Hpp Hi1 RO1 DEF1 El N8 Hreg)]].
intros ns1 [got s2] Hg. cbn [fst snd]. destruct got as [tops|].
+ destruct Hg as (r2 & rest & W2 & -> & Hruns & Hel & Hlen & Hfl).
apply atok_set_pc.
set (r' := mkRegion (rg_mapped_user r2) (rg_alloc_user r2) (rg_mapped_fa r2) rest (rg_holes r2)).
assert (W3 : WfP U (pp - 1) cc bb (upd_pc c (mkPC (max_cached c) (cache_fill_order tops)) (upd_reg c r' s1))).
{ rewrite <- (upd_reg_upd_reg c r2 r' s1).
pose proof (wf_classes _ _ _ _ _ W2 c Hc) as C2. unfold wf_class in C2.
rewrite reg_upd_reg in C2 by (lia || exact HL). change (cache (upd_reg c r2 s1) c) with (cache s1 c) in C2.
change (st_cache_inited (upd_reg c r2 s1)) with (st_cache_inited s1) in C2. rewrite Hi1 in C2.
eapply (WfP_set_region_pc U (pp - 1) cc bb (upd_reg c r2 s1) c); [exact W2 | exact Hc | | lia | | |].
- change (st_cache_inited (upd_reg c r2 s1)) with (st_cache_inited s1). rewrite Hi1.
change (chunk_offs (upd_reg c r2 s1) c) with (chunk_offs s1 c). change (batch_offs (upd_reg c r2 s1) c) with (batch_offs s1 c).
eapply (cls_ok_repart c r2 (cache s1 c) true _ _ r' _ true _ _ []); try exact C2; try reflexivity.
+ exact Hruns.
+ subst r'. cbnr. pose proof (wr_fa_len _ _ _ _ _ _ C2). lia.
+ cbn [pc_max pc_chunks]. split; [reflexivity|]. unfold cache_fill_order. rewrite length_rev. lia.
+ subst r'. cbnr. rewrite Hel, El. unfold cache_fill_order. cbn [pc_chunks app].
change (chunk_offs (upd_reg c r2 s1) c) with (chunk_offs s1 c). change (batch_offs (upd_reg c r2 s1) c) with (batch_offs s1 c).
pose proof (perm_cache_refill (fa_elems (class_size c) rest) [] (chunk_offs s1 c) (batch_offs s1 c) tops) as PP. cbn [app] in PP. exact PP.
- rewrite reg_upd_reg by (lia || exact HL). subst r'. cbnr. pose proof (wf_prim_ev _ _ _ _ _ W2) as PE.
unfold kUserMapSize in *. lia.
-
pose proof (wf_fa_room _ _ _ _ _ W2 c Hc) as R. unfold class_elems in R. rewrite !reg_upd_reg in R by (lia || exact HL).
change (cache (upd_reg c r2 s1) c) with (cache s1 c) in R.
change (chunk_offs (upd_reg c r2 s1) c) with (chunk_offs s1 c) in R |- *. change (batch_offs (upd_reg c r2 s1) c) with (batch_offs s1 c) in R |- *.
change (st_nev (upd_reg c r2 s1)) with (st_nev s1) in R |- *.
subst r'. cbnr. eapply fa_room_xfer; [exact R | | apply Z.le_refl].
rewrite Hel, El. unfold cache_fill_order. cbn [pc_chunks]. rewrite !length_app, length_rev. cbn [length]. lia.
-
apply (regime_cap_keep U (pp - 1) cc bb (upd_reg c r2 s1) c _ W2 Hc); rewrite reg_upd_reg by (lia || exact HL); subst r'; cbnr; [reflexivity | lia]. }
unfold refill_post. cbn [fst snd]. split; [exact W3|]. split; [unfold regs_only in *; cbn; exact RO1|]. split; [exact Hi1|].
unfold upd_pc. rewrite cache_upd_same by (lia || (unfold upd_reg; cbn; exact HLc)). cbn [pc_chunks]. unfold cache_fill_order.
intros E. apply (f_equal (@length Z)) in E. rewrite length_rev in E. cbn in E. lia.
+ destruct Hg as (r' & -> & W2 & NS). apply atok_ret.
unfold refill_post. cbn [fst snd]. split; [exact W2|]. split; [unfold regs_only in *; cbn; exact RO1|]. split; [exact Hi1|]. intros _; exact NS.
- apply atok_ret. unfold refill_post. cbn [fst snd].
split; [eapply WfP_weaken; [exact W1 | lia | pose proof (wf_slack _ _ _ _ _ W1); lia | pose proof (wf_slack _ _ _ _ _ W1); lia]|].
split; [exact RO1|]. split; [exact Hi1|]. intros E; rewrite E in El; discriminate.
Qed.
Lemma refill_tree_apost : forall U pp cc bb s c,
WfP U pp cc bb s -> 1 <= c <= 31 -> 1 <= pp -> preg s c   ->
apost (refill_tree c s) (fun r => WfP U (pp - 1) cc bb (snd r) /\ regs_only s (snd r) /\ st_cache_inited (snd r) = true).
Proof.
intros U pp cc bb s c W Hc Hpp Hreg tr r Hp.
destruct (atok_apath _ true _ tr r (refill_tree_ok U pp cc bb s c true W Hc Hpp Hreg) Hp) as (ns' & A1 & A2 & A3 & _). splits; assumption.
Qed.
