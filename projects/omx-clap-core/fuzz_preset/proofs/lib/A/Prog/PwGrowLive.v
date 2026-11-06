(* fuzz_preset, program part (image-free): the LIVE REQUESTS and the EVENT LISTS of grow's walks against the
   post-implication text (the kit's cut 7cdbb61b5fa0, lib/A/PRH_FnReader.v blob f1ae32e3b2cd): ONE COPY for image A'
   (lib/A/Prog/PwGrow.v) and image B' (writer GrowAp, a Theorem Labs lane's grow A' lane; image B takes it by path).
   rule 24: no function proved. rule 24: proves no function (kind: list lemmas of a walk).
   WHAT. tgrow_specX's arms state the live requests after the call as the entry's moved by the arm's events,
   `Permutation (rs_live (room_of_cf S')) (hlive_from (rs_live (room_of_cf S)) E)`, and its premises bound the live
   counts along the all-granted events by PresetRun.pkR. The leaves (tfuzz_realloc_specX, PRH_FnAlloc.v 4d8aeba047e5)
   state blocks, not live requests; the bridge is CfRoomLivePreset.rs_live_blocks (rs_live (room_of_cf S) is
   map snd (blocks S), by definition) and YG0d.ablocks (map of (address, snd) over blocks S), so map snd (ablocks B ly S)
   is the live list (PwGrowG.grow_rs_live_ab; PwGrowG.v holds the generic live / count lemmas, grow_live_keep and
   grow_cnt_at). Here, what PwGrowG.v does not hold:
   - grow_live_kids / grow_live_swap1 / grow_live_swap2: the block facts the walk states after the kids call (and the
     prhReader_swap of the kids block, and of the kids and keys blocks of an object) are the events [prhPg_ev 56 cap]
     and [prhPg_ev 56 cap; prhPg_ev 8 cap] (prhPg_ev's two shapes, cap = 0 and cap <> 0);
   - grow_sec_cnt / grow_ccnt24: the leaves' sec_cnt / ccnt24 ARE the counts over the live list, by conversion;
   - grow_evs_*: prhPg_evs at the outcomes of each arm.
   Numerals: 56 / 8 (LENGTH: struct pj's kids / keys slot widths, PRH_FnReader's prhPg_ev), 0 / 1 / 6 (WORD: PJ_OBJ).
   No address. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetRun PresetRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnReader.
(* the live-list bridge and the count lemmas are PwGrowG.v's (BGrow3R, one home): grow_rs_live_ab, grow_live_keep,
   grow_cnt_at *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PwGrowG.
(* stdpp, through the LPS modules, shadows several list lemma names; the lemmas used here are Stdlib's *)
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Variable B : asyms.

#[local] Notation LIVE S := (PresetRoom.rs_live (YGcfRoom.room_of_cf S)).



Lemma grow_snd_ab : forall D, map snd (prhReader_ab D) = map (fun ak => snd ak + cf_head) D.
Proof. intros D. unfold prhReader_ab. rewrite map_map. reflexivity. Qed.

(* the kids block replaced by a new block of 56 cap' user bytes (the blocks before / after, as the walk states them
   after the kids call): the kids realloc's event *)
Lemma grow_live_kids : forall ly S ly' S' kids cap res bl,
  Permutation (ablocks B ly S) (prhReader_ab (kids_blkR kids cap) ++ bl) ->
  Permutation (ablocks B ly' S') ((res - cf_head, 56 * cap2R cap + cf_head) :: bl) ->
  Permutation (LIVE S') (PresetReqAt.hlive_from (LIVE S) [prhPg_ev 56 cap]).
Proof.
intros ly S ly' S' kids cap res bl P1 P2.
rewrite (grow_rs_live_ab B ly S), (grow_rs_live_ab B ly' S').
apply (Permutation_map snd) in P1, P2. rewrite map_app, grow_snd_ab in P1. cbn [map snd] in P2.
unfold PresetReqAt.hlive_from. cbn [fold_left]. revert P1.
unfold prhPg_ev, kids_blkR. destruct (Z.eqb_spec cap 0) as [Hc | Hc]; intros P1;
  cbn [map app fst snd PresetReqAt.hstep] in P1 |- *.
- eapply perm_trans; [exact P2|]. apply perm_skip. apply Permutation_sym. exact P1.
- eapply perm_trans; [exact P2|]. apply perm_skip.
  pose proof (PresetReqAt.rm1_perm (56 * cap + cf_head) _ _ P1) as R. cbn [PresetReqAt.rm1] in R.
  rewrite Z.eqb_refl in R. apply Permutation_sym. exact R.
Qed.

(* the same from a prhReader_swap of the kids block (an array, or an object whose keys realloc made no block) *)
Lemma grow_live_swap1 : forall ly S Hp Lam ly' S' Hp' Lam' kids cap k',
  prhReader_swap B ly S Hp Lam ly' S' Hp' Lam' (kids_blkR kids cap) [(k', 56 * cap2R cap)] ->
  Permutation (LIVE S') (PresetReqAt.hlive_from (LIVE S) [prhPg_ev 56 cap]).
Proof.
intros ly S Hp Lam ly' S' Hp' Lam' kids cap k' ((bl & P1 & P2) & _ & _).
exact (grow_live_kids ly S ly' S' kids cap k' bl P1 P2).
Qed.

(* an object's kids and keys blocks replaced: both reallocs' events *)
Lemma grow_live_swap2 : forall ly S Hp Lam ly' S' Hp' Lam' kids keys cap k' y',
  prhReader_swap B ly S Hp Lam ly' S' Hp' Lam' (kids_blkR kids cap ++ keys_blkR 6 keys cap)
    [(y', 8 * cap2R cap); (k', 56 * cap2R cap)] ->
  0 <= cap ->
  Permutation (LIVE S') (PresetReqAt.hlive_from (LIVE S) [prhPg_ev 56 cap; prhPg_ev 8 cap]).
Proof.
intros ly S Hp Lam ly' S' Hp' Lam' kids keys cap k' y' ((bl & P1 & P2) & _ & _) Hc0.
rewrite (grow_rs_live_ab B ly S), (grow_rs_live_ab B ly' S').
apply (Permutation_map snd) in P1, P2. rewrite map_app, grow_snd_ab in P1, P2.
unfold PresetReqAt.hlive_from. cbn [fold_left]. revert P1 P2.
unfold prhPg_ev, kids_blkR, keys_blkR. rewrite (Z.eqb_refl 6). destruct (Z.eqb_spec cap 0) as [Hc | Hc]; intros P1 P2;
  cbn [orb negb map app fst snd PresetReqAt.hstep] in P1, P2 |- *.
- eapply perm_trans; [exact P2|]. apply perm_skip. apply perm_skip. apply Permutation_sym. exact P1.
- eapply perm_trans; [exact P2|]. apply perm_skip. cbn [PresetReqAt.rm1].
  replace (56 * cap2R cap + cf_head =? 8 * cap + cf_head) with false
    by (symmetry; apply Z.eqb_neq; unfold cap2R; rewrite (proj2 (Z.eqb_neq cap 0) Hc); lia).
  apply perm_skip.
  pose proof (PresetReqAt.rm1_perm (56 * cap + cf_head) _ _ P1) as R1. cbn [PresetReqAt.rm1] in R1.
  rewrite Z.eqb_refl in R1.
  pose proof (PresetReqAt.rm1_perm (8 * cap + cf_head) _ _ R1) as R2. cbn [PresetReqAt.rm1] in R2.
  rewrite Z.eqb_refl in R2. apply Permutation_sym. exact R2.
Qed.

(* the leaves' two counts ARE the text's counts over the live list, by conversion *)
Lemma grow_sec_cnt : forall S,
  YGcfRoomLive.sec_cnt S = Z.of_nat (PresetReqAt.cnt YGcfRoomLive.rl_sec_req (LIVE S)).
Proof. intros S. reflexivity. Qed.
Lemma grow_ccnt24 : forall S,
  YGcfRoomLive.ccnt24 S = Z.of_nat (PresetReqAt.cnt (PresetRoom.in_cls YG00.kBatchClass) (LIVE S)).
Proof. intros S. reflexivity. Qed.

(* prhPg_evs at each arm's outcomes *)
Lemma grow_evs_lt : forall o n cap ok, n < cap -> prhPg_evs o n cap ok = [].
Proof. intros o n cap ok H. unfold prhPg_evs. rewrite (proj2 (Z.ltb_lt n cap) H). reflexivity. Qed.
Lemma grow_evs_all : forall o cap, prhPg_evs o cap cap [] = prhPg_ev 56 cap :: (if o then [prhPg_ev 8 cap] else []).
Proof. intros o cap. unfold prhPg_evs. rewrite Z.ltb_irrefl. cbn [nth]. destruct o; reflexivity. Qed.
Lemma grow_evs_false : forall o cap, prhPg_evs o cap cap [false] = [].
Proof. intros o cap. unfold prhPg_evs. rewrite Z.ltb_irrefl. reflexivity. Qed.
Lemma grow_evs_true : forall cap, prhPg_evs false cap cap [true] = [prhPg_ev 56 cap].
Proof. intros cap. unfold prhPg_evs. rewrite Z.ltb_irrefl. reflexivity. Qed.
Lemma grow_evs_tf : forall o cap, prhPg_evs o cap cap [true; false] = [prhPg_ev 56 cap].
Proof. intros o cap. unfold prhPg_evs. rewrite Z.ltb_irrefl. cbn [nth]. destruct o; reflexivity. Qed.
Lemma grow_evs_tt : forall cap, prhPg_evs true cap cap [true; true] = [prhPg_ev 56 cap; prhPg_ev 8 cap].
Proof. intros cap. unfold prhPg_evs. rewrite Z.ltb_irrefl. reflexivity. Qed.

(* ---- THE LIVE ROOM AT EACH EVENT (PRH_Base.prh_live_evs, tgrow_specX's request / live premise at the batch kit 7cdbb61b5fa0)
   gives each realloc's own live premise (tfuzz_realloc_specX: blocks_bytes S + (n + cf_head) <= LIVE_MAX at
   cnt <> fail): event 0 at the entry state (the kids call), event 1 at the state after the kids grant (the keys call),
   whose live list is the entry's moved by the kids event ---- *)
Lemma grow_sum_perm : forall l l' : list Z, Permutation l l' -> fold_right Z.add 0 l = fold_right Z.add 0 l'.
Proof. intros l l' H. induction H; cbn [fold_right]; lia. Qed.

Lemma grow_bb_live : forall (ly : alayout) S, blocks_bytes S = fold_right Z.add 0 (LIVE S).
Proof.
intros ly S. rewrite (blocks_bytes_bsum B ly S), (grow_rs_live_ab B ly S). unfold bsum.
induction (ablocks B ly S) as [|b l IH]; cbn [fold_right map]; [reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma grow_live_at_bb : forall (ly' : alayout) S S' E j,
  Permutation (LIVE S') (PresetReqAt.hlive_from (LIVE S) (firstn j E)) -> prh_live_at S E j = blocks_bytes S'.
Proof.
intros ly' S S' E j HP. unfold prh_live_at. rewrite (grow_bb_live ly' S').
apply grow_sum_perm. apply Permutation_sym. exact HP.
Qed.

Lemma grow_ev_req : forall k cap, prh_ev_req (prhPg_ev k cap) = k * cap2R cap + cf_head.
Proof. intros k cap. unfold prhPg_ev. destruct (cap =? 0); reflexivity. Qed.

(* the kids call's live premise, from event 0 *)
Lemma grow_room_kids : forall (ly : alayout) S o cap, prh_live_evs S (prhPg_evs o cap cap []) ->
  blocks_bytes S + (56 * cap2R cap + cf_head) <= LIVE_MAX.
Proof.
intros ly S o cap H. rewrite grow_evs_all in H.
specialize (H 0%nat (prhPg_ev 56 cap) eq_refl). rewrite grow_ev_req in H.
pose proof (grow_live_at_bb ly S S (prhPg_ev 56 cap :: (if o then [prhPg_ev 8 cap] else [])) 0) as E0.
cbn [firstn] in E0. rewrite PresetReqAt.hlive_from_nil in E0. specialize (E0 (Permutation_refl _)). lia.
Qed.

(* the keys call's live premise, from event 1, at a state whose live list is the entry's moved by the kids event *)
Lemma grow_room_keys : forall (ly2 : alayout) S S2 cap, prh_live_evs S (prhPg_evs true cap cap []) ->
  Permutation (LIVE S2) (PresetReqAt.hlive_from (LIVE S) [prhPg_ev 56 cap]) ->
  blocks_bytes S2 + (8 * cap2R cap + cf_head) <= LIVE_MAX.
Proof.
intros ly2 S S2 cap H HP.
assert (E1 : prh_live_at S (prhPg_evs true cap cap []) 1 = blocks_bytes S2).
{ apply (grow_live_at_bb ly2). rewrite grow_evs_all. exact HP. }
assert (Hn : nth_error (prhPg_evs true cap cap []) 1 = Some (prhPg_ev 8 cap)) by (rewrite grow_evs_all; reflexivity).
specialize (H 1%nat _ Hn). rewrite grow_ev_req, E1 in H. exact H.
Qed.

(* THE OUTCOME EXCLUSION'S INPUTS (each refused arm of tgrow_specX): the all-granted run's two events, each with its
   consumer window, split off for the two leaves' outcome clauses *)
Lemma grow_run_split : forall sm x os i o cap,
  prh_run_at sm x os i (prhPg_evs o cap cap []) ->
  prh_cons_from sm x os i (length (prhPg_evs o cap cap [])) ->
  prh_run_at sm x os i [prhPg_ev 56 cap] /\ prh_cons_from sm x os i 1 /\
  (o = true -> prh_run_at sm x os (i + 1) [prhPg_ev 8 cap] /\ prh_cons_from sm x os (i + 1) 1).
Proof.
intros sm x os i o cap Hr Hc. rewrite grow_evs_all in Hr, Hc.
change (prhPg_ev 56 cap :: (if o then [prhPg_ev 8 cap] else []))
  with ([prhPg_ev 56 cap] ++ (if o then [prhPg_ev 8 cap] else [])) in Hr, Hc.
rewrite length_app in Hc. cbn [length] in Hc.
apply (proj1 (prh_run_at_app_iff _ _ _ _ _ _)) in Hr as (Hr1 & Hr2).
apply (proj1 (prh_cons_from_app_iff _ _ _ _ _ _)) in Hc as (Hc1 & Hc2).
cbn [length] in Hr2. split; [exact Hr1|]. split; [exact Hc1|].
intros Ho. subst o. exact (conj Hr2 Hc2).
Qed.

End c.
