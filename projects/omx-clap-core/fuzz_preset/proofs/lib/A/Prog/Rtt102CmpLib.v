(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/pj_set_trans.v, with its module paths and module names changed; 381 of its 472 lines of code are new or changed and 692 lines of the source are left out. *)
(* UNFINISHED: first build (8e9d2ad2945) pending; the stretch's walk file Rtt102CmpA.v is not written yet *)
(* fuzz_preset, program walk of round_trip_text ON THE #102 PINS, stretch CMP (lane RttCmp of WalkRtt102, the text owner):
   the IMAGE-GENERIC lemmas the stretch's walk (Rtt102CmpA.v) uses, none of them a run.
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma support).
   - the pure models: the calls of any reading are at most a whole reading's (PjGrammar G7_1_calls / G7_2), the
     writer's text has no NUL byte (from the tree's representation pj_nodeR, as plain PjWriteAdapt.v pjwa_bytes does
     from pj_node, through WriterAppFacts.wdoc_no_zero), its longest number run (PjRoundTrip.G12_1);
   - the float-register keep composes (fregs_kept_x);
   - the tree representation pj_nodeR moves to a new memory and a new block predicate (PRH_Reader.v pj_nodeR_frame
     with the block predicate free to change on the tree's own blocks);
   - the frame-pointer chain at a call of round_trip_text (s0 = the entry sp, the entry ra / s0 saved at sp0 - 8 /
     sp0 - 16) and the call's trace in the universe (prh_univ_closure's frame-pointer clause at prh_ctx);
   - the harness blocks' tree visibility at a later state (AR_laws_x fields 1, 14, 15 at cf_head);
   - g_most / g_own_ran_out read through a view equal on prh_pst.
   Numerals: 8, 16 (LENGTH: word, frame-record slots at fp - 8 / fp - 16), 56 (LENGTH: a pj node), 4096 (DERIVED: the
   lowest return address fpchain admits), 2 ^ 28 / 2 ^ 30 / 2 ^ 32 (LENGTH: the texts' length bounds). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar PjRoundTrip PresetReqAt PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue WriterApp PjWriteHyp TxModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterSpec WriterSpecFacts WriterAppFacts.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnTx PRH_FnWriter PRH_FnReader PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcfTreeVis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S10Env.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- the pure models ---- *)

(* the calls of ANY run of the reader (an allocation may fail anywhere) are at most a whole reading's *)
Lemma rcl_calls_le : forall f x ok,
  (PjGrammar.calls (snd (PjGrammar.jr_run f x ok)) <= PjGrammar.ncalls f x)%nat.
Proof.
intros f x ok. destruct (PjGrammar.ok_upto_dec ok (PjGrammar.ncalls f x)) as [Hu | (j & Hj & Hf & Hu)].
- rewrite (PjGrammar.G7_1_calls f x ok Hu). lia.
- destruct (PjGrammar.G7_2 f x ok j Hj Hf Hu) as [_ Hc]. rewrite Hc. lia.
Qed.

(* a whole reading's calls are bounded by the text's length *)
Lemma rcl_ncalls_len : forall f x, (PjGrammar.ncalls f x <= 2 * length x + 2)%nat.
Proof. intros f x. unfold PjGrammar.ncalls. exact (PjGrammar.G7_4 f x []). Qed.

(* the writer's text read back: the tree, and a whole reading's calls are the tree's tcalls *)
Lemma rcl_read_back : forall t p, PjRoundTrip.pj_wf ReaderRes.jr_strtod t ->
  ck_read (WriterValue.wdoc t p) = Some t /\
  ck_ncalls (WriterValue.wdoc t p) = Z.of_nat (PjRoundTrip.tcalls t).
Proof.
intros t p H. split.
- exact (PjRoundTrip.G9 ReaderRes.jr_strtod t H p).
- unfold ck_ncalls. rewrite (PjRoundTrip.G9_calls ReaderRes.jr_strtod t H p). reflexivity.
Qed.

(* the longest number run of the writer's text (plain RttModel.v rtt_maxrun's argument, over G12_1 only) *)
Lemma rcl_maxrun : forall t p, PjWriteHyp.wlen t p + 1 <= 2 ^ 28 ->
  Z.of_nat (PjRoundTrip.maxrun (WriterValue.wdoc t p)) < 2 ^ 30.
Proof.
intros t p H. pose proof (PjRoundTrip.G12_1 (WriterValue.wdoc t p)) as G.
unfold PjWriteHyp.wlen in H. lia.
Qed.

(* the float-register keep composes *)
Lemma rcl_fregs_trans : forall f1 f2 f3 : YK11.FPState,
  fregs_kept_x f1 f2 -> fregs_kept_x f2 f3 -> fregs_kept_x f1 f3.
Proof. intros f1 f2 f3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.

(* the tree's strings are bytes without NUL (plain PjWriteAdapt.v pjwa_bytes over pj_nodeR: the string pattern has
   pj_cstrR's four conjuncts) *)
Lemma rcl_nodeR_bytes : forall segs t m lblk p D, pj_nodeR segs m lblk p t D -> WriterAppFacts.jv_bytes_ok t.
Proof.
intros segs t. induction t as [| | | txt bits | s | items IH | members IH] using jv_ind';
  intros m lblk p D H; cbn [pj_nodeR] in H; cbn [WriterAppFacts.jv_bytes_ok]; try exact I.
- destruct H as (_ & _ & num & str & kids & keys & n & cap & _ & _ & _ & _ & _ & _ & k & (_ & _ & _ & HF & _) & _).
  destruct (WriterSpecFacts.chars_ok txt HF) as [Hz Hb]. split; assumption.
- destruct H as (_ & _ & num & str & kids & keys & n & cap & _ & _ & _ & _ & _ & k & (_ & _ & _ & HF & _) & _).
  destruct (WriterSpecFacts.chars_ok s HF) as [Hz Hb]. split; assumption.
- destruct H as (_ & _ & num & str & kids & keys & n & cap & _ & _ & _ & _ & _ & _ & Di & _ & HI).
  clear - IH HI. revert kids Di HI.
  induction IH as [|x r Hx Hr IHr]; intros a Di HI; [exact I|].
  cbn [pj_itemsR] in HI. destruct HI as (D1 & D2 & _ & H1 & H2).
  split; [exact (Hx _ _ _ _ H1) | exact (IHr _ _ H2)].
- destruct H as (_ & _ & num & str & kids & keys & n & cap & _ & _ & _ & _ & _ & Di & _ & HI).
  clear - IH HI. revert kids keys Di HI.
  induction IH as [|[nm u] r Hx Hr IHr]; intros a ka Di HI; [exact I|].
  cbn [pj_memsR] in HI. destruct HI as (x & k & D1 & D2 & _ & _ & (_ & _ & _ & HF & _) & H1 & H2).
  destruct (WriterSpecFacts.chars_ok nm HF) as [Hz Hb].
  split; [exact Hb|]. split; [exact Hz|]. split; [exact (Hx _ _ _ _ H1) | exact (IHr _ _ _ H2)].
Qed.

Lemma rcl_wdoc_nz : forall segs m lblk p t D b, pj_nodeR segs m lblk p t D ->
  Forall (fun c => 0 < c < 256) (WriterValue.wdoc t b).
Proof.
intros segs m lblk p t D b H.
destruct (WriterAppFacts.wdoc_no_zero t b (rcl_nodeR_bytes segs t m lblk p D H)) as [Hz Hb].
exact (WriterAppFacts.str_chr _ Hb Hz).
Qed.

(* ---- the frame-pointer chain and the trace ---- *)

Lemma rcl_fpchain_ext : forall (ld ld' : Z -> option Z) top ch bp,
  fpchain ld bp top ch -> (forall a, bp - 16 <= a -> ld' a = ld a) -> fpchain ld' bp top ch.
Proof.
intros ld ld' top ch. induction ch as [|[[fp ra] nfp] rest IH]; intros bp H E; cbn [fpchain] in H |- *.
- destruct H as (r & Hr & Hb). exists r. split; [rewrite E by lia; exact Hr | exact Hb].
- destruct H as (Efp & Hal & Hra & Hnfp & Hra4 & Hrest). subst fp.
  split; [reflexivity|]. split; [exact Hal|]. split; [rewrite E by lia; exact Hra|].
  split; [rewrite E by lia; exact Hnfp|]. split; [exact Hra4|].
  destruct (bad_next bp top nfp) eqn:Eb; [exact Hrest|].
  unfold bad_next in Eb. apply orb_false_iff in Eb as [Eb _]. apply orb_false_iff in Eb as [Eb _].
  apply Z.leb_gt in Eb.
  apply (IH nfp Hrest). intros a Ha. apply E. lia.
Qed.

(* the return addresses of a chain, read off its records *)
Lemma rcl_flat_map_ra : forall (pc0 : Z) (ch : list (Z * Z * Z)),
  flat_map (fun r => match r with (_, ra, _) => if ra =? pc0 then [] else [ra] end) ch =
  flat_map (fun ra => if ra =? pc0 then [] else [ra]) (spine ch).
Proof.
intros pc0 ch. unfold spine. induction ch as [|[[a ra] b] t IH]; [reflexivity|].
cbn [flat_map map fst snd]. rewrite IH. reflexivity.
Qed.

(* a call's trace with a walkable first frame is the pc0-filtered trace of its return site and the chain's ras *)
Lemma rcl_trace_eq : forall lyc pc0 regs ch, frame0_ok lyc regs = true ->
  call_trace lyc pc0 regs ch = prh_trace pc0 (raZ regs) (spine ch).
Proof.
intros lyc pc0 regs ch Hf. unfold call_trace. rewrite Hf. unfold unwind_of_chain, prh_trace.
rewrite rcl_flat_map_ra. reflexivity.
Qed.

Section rcs. Context {rc : YM05.RunCeil}.
(* the chain at a call of a frame-pointer function whose s0 is its entry sp0: the record (sp0, ra0, s0e) the prologue
   saved (ra at sp0 - 8, s0 at sp0 - 16), then the entry's chain, read above sp0 in a view equal to the entry's there *)
Lemma rcl_call_chain : forall (ly0 lyc : alayout) (rd0 rd : reader) sp0 s0e ra0 ch0 spc,
  achain ly0 rd0 sp0 s0e ch0 -> ly_top lyc = ly_top ly0 ->
  4096 <= ra0 -> sp0 mod 8 = 0 -> YM05.alloc_ceiling <= sp0 -> sp0 < ly_top ly0 - 16 -> spc + 16 <= sp0 ->
  rdword rd (sp0 - 8) = Some ra0 -> rdword rd (sp0 - 16) = Some s0e ->
  (forall a, sp0 <= a -> rd a = rd0 a) ->
  achain lyc rd spc sp0 ((sp0, ra0, s0e) :: ch0).
Proof.
intros ly0 lyc rd0 rd sp0 s0e ra0 ch0 spc Hch Etop Hra Hal Hceil Htop Hsp Hw1 Hw2 Hrd.
right. rewrite Etop. split; [exact Hsp|]. split; [exact Htop|]. split; [exact Hal|]. split.
- cbn [fpchain]. split; [reflexivity|]. split; [exact Hal|]. split; [exact Hw1|]. split; [exact Hw2|].
  split; [exact Hra|].
  destruct Hch as [(Hc & ->) | (H1 & H2 & H3 & H4 & H5)].
  + assert (Eb : bad_next sp0 (ly_top ly0) s0e = true).
    { unfold bad_next. apply orb_true_iff. destruct Hc as [Hc | [Hc | Hc]].
      - left. apply orb_true_iff. left. apply Z.leb_le. lia.
      - left. apply orb_true_iff. right. apply Z.leb_le. lia.
      - right. apply negb_true_iff, Z.eqb_neq. exact Hc. }
    rewrite Eb. reflexivity.
  + assert (Eb : bad_next sp0 (ly_top ly0) s0e = false).
    { unfold bad_next. rewrite (proj2 (Z.leb_gt s0e sp0)) by lia.
      rewrite (proj2 (Z.leb_gt (ly_top ly0 - 16) s0e)) by lia. rewrite H3. reflexivity. }
    rewrite Eb. apply (rcl_fpchain_ext (rdword rd0) (rdword rd) (ly_top ly0) ch0 s0e H4).
    intros a Ha. apply S10Env.ts_rdword_keep. intros j Hj. apply Hrd. lia.
- constructor; [cbn [fst]; lia|].
  destruct Hch as [(_ & ->) | (_ & _ & _ & _ & H5)]; [constructor|].
  eapply Forall_impl; [|exact H5]. intros r Hr. cbn beta in Hr. lia.
Qed.

(* the chain premise of a runtime allocator call from such a state *)
Lemma rcl_chain_pre : forall (lyc : alayout) (rd : reader) regs ch,
  4096 <= raZ regs -> spZ regs + 16 < ly_top lyc -> YM05.alloc_ceiling <= s0Z regs ->
  achain lyc rd (spZ regs) (s0Z regs) ch -> spZ regs + 16 <= s0Z regs -> s0Z regs < ly_top lyc - 16 ->
  s0Z regs mod 8 = 0 ->
  chain_pre lyc rd regs ch.
Proof.
intros lyc rd regs ch Hra Hf Hc0 Hch H1 H2 H3. split; [exact Hra|].
unfold frame0_ok. rewrite (proj2 (Z.ltb_lt _ _) Hf).
assert (Eb : bad_next (spZ regs) (ly_top lyc) (s0Z regs) = false).
{ unfold bad_next. rewrite (proj2 (Z.leb_gt (s0Z regs) (spZ regs))) by lia.
  rewrite (proj2 (Z.leb_gt (ly_top lyc - 16) (s0Z regs))) by lia. rewrite H3. reflexivity. }
rewrite Eb. split; [exact H1|].
destruct Hch as [(Hc & _) | (_ & _ & _ & H4 & _)]; [|exact H4].
exfalso. destruct Hc as [Hc | [Hc | Hc]]; lia.
Qed.

End rcs.

(* ---- the tree representation at a new memory and a new block predicate ---- *)

Lemma rcl_cstrR_move : forall segs m m' (lblk lblk' : Z -> Z -> Prop) a k s, pj_cstrR segs m lblk a k s ->
  (lblk a k -> lblk' a k) ->
  (forall x, a <= x < a + k -> mbyte segs m' x = mbyte segs m x) -> pj_cstrR segs m' lblk' a k s.
Proof.
intros segs m m' lblk lblk' a k s (Hl & Hk & Hn & Hf & Hb) HL E.
split; [exact (HL Hl)|]. split; [exact Hk|]. split; [exact Hn|]. split; [exact Hf|].
apply (garr8R_frame segs m m' a (s ++ [0]) Hb). intros x Hx. apply E. rewrite length_app in Hx. cbn [length] in Hx. lia.
Qed.

Lemma rcl_memsR_move : forall segs m m' (lblk lblk' : Z -> Z -> Prop) (P P' : Z -> jv -> list (Z * Z) -> Prop) l a ka D,
  pj_memsR segs m lblk P a ka l D ->
  (forall i nm u x k D1, nth_error l i = Some (nm, u) -> In (x, k) D -> incl D1 D ->
     rd_u64 segs m (ka + 8 * Z.of_nat i) x -> pj_cstrR segs m lblk x k nm -> P (a + 56 * Z.of_nat i) u D1 ->
     rd_u64 segs m' (ka + 8 * Z.of_nat i) x /\ pj_cstrR segs m' lblk' x k nm /\ P' (a + 56 * Z.of_nat i) u D1) ->
  pj_memsR segs m' lblk' P' a ka l D.
Proof.
intros segs m m' lblk lblk' P P' l. induction l as [|[nm u] r IH]; intros a ka D H HP; cbn [pj_memsR] in H |- *;
  [exact H|].
destruct H as (x & k & D1 & D2 & -> & Hx & Hc & H1 & H2). exists x, k, D1, D2. split; [reflexivity|].
pose proof (HP 0%nat nm u x k D1 eq_refl (or_introl eq_refl)
  (fun y Hy => in_cons _ _ _ (in_or_app _ _ _ (or_introl Hy)))) as HP0.
replace (a + 56 * Z.of_nat 0) with a in HP0 by lia. replace (ka + 8 * Z.of_nat 0) with ka in HP0 by lia.
destruct (HP0 Hx Hc H1) as (Hx' & Hc' & H1'). split; [exact Hx'|]. split; [exact Hc'|].
split; [exact H1'|].
apply (IH (a + 56) (ka + 8) D2 H2). intros i nm' u' x' k' D1' Hi Hin Hinc Hx2 Hc2 HP2.
specialize (HP (S i) nm' u' x' k' D1' Hi (in_cons _ _ _ (in_or_app _ _ _ (or_intror Hin)))
  (fun y Hy => in_cons _ _ _ (in_or_app _ _ _ (or_intror (Hinc y Hy))))).
replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) in HP by lia.
replace (ka + 8 * Z.of_nat (S i)) with (ka + 8 + 8 * Z.of_nat i) in HP by lia.
exact (HP Hx2 Hc2 HP2).
Qed.

(* PRH_Reader.v pj_nodeR_frame, the block predicate free to change on the tree's own blocks *)
Lemma rcl_nodeR_move : forall segs t m m' (lblk lblk' : Z -> Z -> Prop) p D, pj_nodeR segs m lblk p t D ->
  pj_agreeR segs m m' (pj_footR p D) -> (forall a k, In (a, k) D -> lblk a k -> lblk' a k) ->
  pj_nodeR segs m' lblk' p t D.
Proof.
intros segs t. induction t as [| | | txt bits | s | items IH | members IH] using jv_ind';
  intros m m' lblk lblk' p D H HM HL; cbn [pj_nodeR] in H |- *;
  assert (HM1 : forall x, pj_footR p D x -> mbyte segs m' x = mbyte segs m x) by (intros x Hx; exact (proj1 (HM x Hx)));
  destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Hb);
  (split; [exact Hn|]); (split; [exact Ha|]); exists num, str, kids, keys, n, cap;
  (split; [apply (pj_hdrR_frame segs m m'); [exact Hh | intros x Hx; apply HM; left; exact Hx]|]).
- exact Hb.
- exact Hb.
- exact Hb.
- destruct Hb as (E1 & E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED].
  apply (rcl_cstrR_move segs m m' lblk lblk'); [exact Hc | apply HL; subst D; left; reflexivity |].
  intros x Hx. apply HM1. right. exists (str, k).
  split; [subst D; left; reflexivity | unfold pj_holdsR; cbn [fst snd]; exact Hx].
- destruct Hb as (E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED].
  apply (rcl_cstrR_move segs m m' lblk lblk'); [exact Hc | apply HL; subst D; left; reflexivity |].
  intros x Hx. apply HM1. right. exists (str, k).
  split; [subst D; left; reflexivity | unfold pj_holdsR; cbn [fst snd]; exact Hx].
- destruct Hb as (Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact Ek|]. split; [exact En|]. split; [exact Hc|].
  split.
  { destruct Hcap as [Hcap | (Hcp & Hlb)]; [left; exact Hcap | right; split; [exact Hcp|]].
    apply HL; [subst D; rewrite (proj2 (Z.eqb_neq cap 0)) by lia; left; reflexivity | exact Hlb]. }
  assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
  exists Di. split; [exact ED|].
  apply (pj_itemsR_mono (pj_nodeR segs m lblk) (pj_nodeR segs m' lblk') items kids Di Hi).
  intros i u D1 Hil Hinc HP.
  pose proof (pj_nth_lenR items i u Hil) as Hlt.
  assert (Hp : 0 < cap) by lia.
  assert (Hin : In (kids, 56 * cap) D).
  { subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left; reflexivity. }
  rewrite Forall_forall in IH.
  apply (IH u (nth_error_In items i Hil) m m' lblk lblk' _ D1 HP).
  + intros x Hx. apply HM. destruct Hx as [Hx|(b & Hb & Hx)].
    * right. exists (kids, 56 * cap). split; [exact Hin | unfold pj_holdsR; cbn [fst snd]; lia].
    * right. exists b. split; [apply HDi; apply Hinc; exact Hb | exact Hx].
  + intros a0 k0 Hin0 Hl0. apply HL; [apply HDi; apply Hinc; exact Hin0 | exact Hl0].
- destruct Hb as (Es & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact En|]. split; [exact Hc|].
  split.
  { destruct Hcap as [Hcap | (Hcp & Hlk & Hly)]; [left; exact Hcap | right; split; [exact Hcp|]].
    split.
    - apply HL; [subst D; rewrite (proj2 (Z.eqb_neq cap 0)) by lia; left; reflexivity | exact Hlk].
    - apply HL; [subst D; rewrite (proj2 (Z.eqb_neq cap 0)) by lia; right; left; reflexivity | exact Hly]. }
  assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
  exists Di. split; [exact ED|].
  apply (rcl_memsR_move segs m m' lblk lblk' (pj_nodeR segs m lblk) (pj_nodeR segs m' lblk') members kids keys Di Hi).
  intros i nm u x k D1 Hil Hxk Hinc Hx Hcs HP.
  pose proof (pj_nth_lenR members i (nm, u) Hil) as Hlt.
  assert (Hp : 0 < cap) by lia.
  assert (Hin : In (kids, 56 * cap) D /\ In (keys, 8 * cap) D).
  { subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. split; [left; reflexivity | right; left; reflexivity]. }
  split; [|split].
  + apply (rd_u64_frame segs m m'); [exact Hx|]. intros y Hy. apply HM1. right. exists (keys, 8 * cap).
    split; [exact (proj2 Hin) | unfold pj_holdsR; cbn [fst snd]; lia].
  + apply (rcl_cstrR_move segs m m' lblk lblk'); [exact Hcs | apply HL; apply HDi; exact Hxk |].
    intros y Hy. apply HM1. right. exists (x, k).
    split; [apply HDi; exact Hxk | unfold pj_holdsR; cbn [fst snd]; exact Hy].
  + rewrite Forall_forall in IH. specialize (IH (nm, u) (nth_error_In members i Hil)). cbn [snd] in IH.
    apply (IH m m' lblk lblk' _ D1 HP).
    * intros y Hy. apply HM. destruct Hy as [Hy|(b & Hb & Hy)].
      -- right. exists (kids, 56 * cap). split; [exact (proj1 Hin) | unfold pj_holdsR; cbn [fst snd]; lia].
      -- right. exists b. split; [apply HDi; apply Hinc; exact Hb | exact Hy].
    * intros a0 k0 Hin0 Hl0. apply HL; [apply HDi; apply Hinc; exact Hin0 | exact Hl0].
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variables (CTX0 : list (list Z)).
(* the allocator laws at the cf instance's head; THE HEAD IS AT LEAST ONE SHADOW GRANULE (PRH_Base.v prh_head_wide:
   the kit's one spelling, which a walk takes as a hypothesis; owner: the cf instance owner's preset_head_wide) *)
Hypothesis LAWS : AR_laws_x segs B ARx cf_head.
Hypothesis HW : prh_head_wide.

(* the trace of an allocator call of round_trip_text at a return site of its, from a state whose chain is the entry
   record (sp0, ra0, s0e) and the entry chain: the closure's frame-pointer clause at the text's prh_ctx *)
Lemma rcl_trace_univ : forall lyc regsc ra0 s0e ch0 sp0 rt,
  prh_univ_closure B CTX0 -> prh_ctx CTX0 F_round_trip_text (ra0 :: spine ch0) ->
  pi_fp F_round_trip_text = true -> frame0_ok lyc regsc = true ->
  In (raZ regsc) (pi_ret_sites F_round_trip_text rt) ->
  In (call_trace lyc (prh_pc0 B rt) regsc ((sp0, ra0, s0e) :: ch0)) (as_universe B).
Proof.
intros lyc regsc ra0 s0e ch0 sp0 rt HU HC Hfp Hf Hr. rewrite rcl_trace_eq by exact Hf.
exact (prh_univ_closure_site B CTX0 F_round_trip_text (ra0 :: spine ch0) rt (raZ regsc) HU HC Hfp Hr).
Qed.

(* a present byte is seen *)
Lemma rcl_aview_present : forall (W : world segs) mem a, apresent (w_H W) mem a -> aview segs (w_H W) mem a <> None.
Proof.
intros W mem a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate.
Qed.

(* the tree's blocks visible at a later state: each a live harness block there (in ablocks with its head in Hp), so
   AR_laws_x's harness-block shadow (field 14), blocks (field 1) and tail granule (field 15) give the view facts; the
   scalar facts are the earlier state's *)
Lemma rcl_tree_vis : forall ly S Hp W mem md (W0 : world segs) mem0 D,
  ARx ly S Hp W mem md -> PRH_FnWriter.prhWriter_tree_vis W0 mem0 D ->
  (forall a k, In (a, k) D -> In (a - cf_head, k + cf_head) (ablocks B ly S) /\ In (a - cf_head) Hp) ->
  PRH_FnWriter.prhWriter_tree_vis W mem D.
Proof.
intros ly S Hp W mem md W0 mem0 D HAR HTV HM.
unfold PRH_FnWriter.prhWriter_tree_vis, YGcfTreeVis.tree_vis_cf in *.
intros a k Hin. destruct (HTV a k Hin) as (A1 & A2 & A3 & A4 & _ & _ & _).
destruct (HM a k Hin) as [Hab Hhp]. unfold prh_head_wide in HW.
assert (Hreq : req_size (k + cf_head) = k + cf_head) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
destruct (alx_hshadow _ _ _ LAWS ly S Hp W mem md (a - cf_head) (k + cf_head) HAR Hab Hhp) as [Hbs Hhu].
rewrite Hreq in Hbs, Hhu. replace (a - cf_head + cf_head) with a in Hbs, Hhu by lia.
replace (k + cf_head - cf_head) with k in Hbs, Hhu by lia.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md (a - cf_head) (k + cf_head) HAR Hab) as (_ & _ & _ & _ & Hpr & _).
rewrite Hreq in Hpr.
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|].
split; [eapply block_shadow_range; [exact Hbs | lia | lia]|].
split; [intros Hk; apply Hhu; lia|].
intros x Hx. destruct (Z_lt_le_dec x (a + k)) as [Hl|Hl].
- destruct (Hpr x ltac:(lia)) as [Hpx _]. exact (rcl_aview_present W mem x Hpx).
- apply (alx_blocks_tail _ _ _ LAWS ly S Hp W mem md (a - cf_head) (k + cf_head) x HAR Hab).
  rewrite Hreq. replace (a - cf_head + (k + cf_head)) with (a + k) by lia. lia.
Qed.

(* g_most and g_own_ran_out are prh_pst cells (the sixth and seventh) *)
Lemma rcl_pst_most : forall j, (j < pi_gz_most)%nat -> Exists (in_zr (pi_g_most + Z.of_nat j)) prh_pst.
Proof.
intros j Hj. unfold prh_pst. do 5 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.
Lemma rcl_pst_own : forall j, (j < pi_gz_own_ran_out)%nat -> Exists (in_zr (pi_g_own_ran_out + Z.of_nat j)) prh_pst.
Proof.
intros j Hj. unfold prh_pst. do 6 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.

(* the two cells read through a view equal on prh_pst *)
Lemma rcl_most_kept : forall (W W' : world segs) mem mem' most,
  prh_most W mem most ->
  (forall a, Exists (in_zr a) prh_pst -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  prh_most W' mem' most.
Proof.
intros W W' mem mem' most [Hv Hr] HK. split; [|exact Hr].
apply (S10Env.ts_vm_av (w_H W) (w_H W') mem mem' pi_g_most pi_gz_most most); [|exact Hv].
intros j Hj. apply HK. exact (rcl_pst_most j Hj).
Qed.
Lemma rcl_own_kept : forall (W W' : world segs) mem mem' own,
  prh_own W mem own ->
  (forall a, Exists (in_zr a) prh_pst -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  prh_own W' mem' own.
Proof.
intros W W' mem mem' own [Hv Hr] HK. split; [|exact Hr].
apply (S10Env.ts_vm_av (w_H W) (w_H W') mem mem' pi_g_own_ran_out pi_gz_own_ran_out own); [|exact Hv].
intros j Hj. apply HK. exact (rcl_pst_own j Hj).
Qed.

(* the bytes of a byte list are seen at their addresses (FuzzStrdup.v sd_garr8_aview, over any listing) *)
Lemma rcl_garr8_aview : forall (W : world segs) m p l j, garr8 segs (mrestrict (w_H W) m) p l -> (j < length l)%nat ->
  aview segs (w_H W) m (p + Z.of_nat j) = Some (nth j l 0).
Proof.
intros W m p l j H Hj. unfold aview. rewrite (garr8_mbyte segs _ p l j H Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. exact (proj2 (H j Hj)).
Qed.

(* a NUL-terminated text without NUL: the string rules' first_byte (FuzzStrdup.v sd_first_byte over bytes_at) *)
Lemma rcl_first_byte : forall (W : world segs) m p l, bytes_at W m p (l ++ [0]) -> Forall (fun c => 0 < c < 256) l ->
  first_byte segs W m p (Z.of_nat (length l) + 1) 0 (Z.of_nat (length l)).
Proof.
intros W m p l Hg Hnz. split; [lia|]. split.
- intros i Hi. exists (nth (Z.to_nat i) l 0). split.
  + replace (p + i) with (p + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (rcl_garr8_aview W m p (l ++ [0]) (Z.to_nat i) Hg) by (rewrite length_app; cbn [length]; lia).
    rewrite app_nth1 by lia. reflexivity.
  + rewrite Forall_nth in Hnz. pose proof (Hnz (Z.to_nat i) 0 ltac:(lia)) as Hc. lia.
- intros _. rewrite (rcl_garr8_aview W m p (l ++ [0]) (length l) Hg) by (rewrite length_app; cbn [length]; lia).
  rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.

(* the string rules' src_ok over a byte window (FuzzStrdup.v sd_src_ok over bytes_at) *)
Lemma rcl_src_ok : forall (W : world segs) regs m p l, bytes_at W m p l ->
  (forall a, p <= a < p + Z.of_nat (length l) -> ~ (spZ regs - ESTACK <= a < spZ regs)) ->
  src_ok segs W regs m p (Z.of_nat (length l)).
Proof.
intros W regs m p l H Hw a Ha. split; [|exact (Hw a Ha)].
replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia.
rewrite (rcl_garr8_aview W m p l (Z.to_nat (a - p)) H) by lia. discriminate.
Qed.

(* the read-only view through a memory equal below the low-memory end (FuzzStrdup.v sd_rod_kept, over any listing:
   the read-only bytes are image bytes, pa_segs_low / pa_relro_img) *)
Lemma rcl_rod_kept : forall (W W' : world segs) m m',
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) m) ->
  (forall a, 0 <= a < kLowMemEnd -> aview segs (w_H W') m' a = aview segs (w_H W) m a) ->
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W') m').
Proof.
intros W W' m m' H HA a Hro Hn He. rewrite HA; [exact (H a Hro Hn He)|].
apply pa_segs_low. destruct Hro as [(sg & Hin & _ & Hr) | Hr];
  [exists sg; split; [exact Hin | exact Hr] | exact (pa_relro_img a Hr)].
Qed.

(* the tree's footprint is present at a state where its blocks are live harness blocks and its node is present *)
Lemma rcl_foot_present : forall ly S Hp W mem md Lam peak cnt fail ran most own p D,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> (forall bk, In bk D -> In bk Lam) ->
  (forall x, p <= x < p + 56 -> apresent (w_H W) mem x) ->
  forall x, pj_footR p D x -> apresent (w_H W) mem x.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own p D HAR HL HD Hp56 x [Hx | [[a k] [Hin Hx]]]; [exact (Hp56 x Hx)|].
unfold pj_holdsR in Hx. cbn [fst snd] in Hx. unfold prh_head_wide in HW.
pose proof (proj1 (Forall_forall _ _) (prh_ledger_blocks B ly S Hp W mem Lam peak cnt fail ran most own HL) (a, k) (HD _ Hin)) as Hb.
cbn [fst snd] in Hb. destruct Hb as (Hk0 & Hab & _ & _ & _).
assert (Hreq : req_size (k + cf_head) = k + cf_head) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md (a - cf_head) (k + cf_head) HAR Hab) as (_ & _ & _ & _ & Hpr & _).
rewrite Hreq in Hpr. exact (proj1 (Hpr x ltac:(lia))).
Qed.

(* the tree at a later memory whose view keeps its footprint, with its footprint present there (so writable), and a
   block predicate that holds of its blocks *)
Lemma rcl_nodeR_keep : forall (W W' : world segs) mem mem' (lblk lblk' : Z -> Z -> Prop) p t D,
  pj_nodeR segs (mrestrict (w_H W) mem) lblk p t D ->
  (forall x, pj_footR p D x -> aview segs (w_H W') mem' x = aview segs (w_H W) mem x) ->
  (forall x, pj_footR p D x -> apresent (w_H W') mem' x) ->
  (forall a k, In (a, k) D -> lblk a k -> lblk' a k) ->
  pj_nodeR segs (mrestrict (w_H W') mem') lblk' p t D.
Proof.
intros W W' mem mem' lblk lblk' p t D H E P HL.
apply (rcl_nodeR_move segs t _ _ lblk lblk' p D H); [|exact HL].
intros x Hx. split.
- apply (mbyte_of_aview segs). exact (E x Hx).
- intros _. apply (apresent_writable segs). exact (P x Hx).
Qed.

(* a covering hull's sub-range is visible (FuzzStrdup.v sd_hull_sub, over any reader) *)
Lemma rcl_hull_sub : forall (rd : reader) p m d n, shadow_hull_vis rd p m -> p <= d -> d + n <= p + m -> 0 < n ->
  shadow_hull_vis rd d n.
Proof.
intros rd p m d n Hh Hpd Hdn Hn s Hs. apply Hh.
pose proof (shadow_mono p d Hpd) as M1. pose proof (shadow_mono (d + n - 1) (p + m - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
  by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.

(* the granule after a string that ends inside a block of user size m at p: present, in the block or its tail
   granule (the division facts are named so lia reads them as linear) *)
Lemma rcl_tail_in_block : forall ly S Hp W mem md b n p m s a,
  ARx ly S Hp W mem md -> In (b, n) (ablocks B ly S) -> b + req_size n = p + m -> b <= p ->
  (forall x, b <= x < b + req_size n -> apresent (w_H W) mem x) -> p <= s -> s < p + m ->
  s < a < s - s mod 8 + 8 -> aview segs (w_H W) mem a <> None.
Proof.
intros ly S Hp W mem md b n p m s a HAR Hin Hend Hbp Hpr Hps Hsm Ha.
destruct (Z_lt_le_dec a (p + m)) as [Hl|Hl].
- assert (Hb : b <= a < b + req_size n) by lia.
  exact (rcl_aview_present W mem a (Hpr a Hb)).
- apply (alx_blocks_tail _ _ _ LAWS ly S Hp W mem md b n a HAR Hin). rewrite Hend.
  pose proof (Z.div_mod s 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound s 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod (p + m + 7) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (p + m + 7) 8 ltac:(lia)) as M2.
  set (k1 := s / 8) in *. set (r1 := s mod 8) in *. set (k2 := (p + m + 7) / 8) in *.
  set (r2 := (p + m + 7) mod 8) in *. lia.
Qed.

(* the facts the string rules ask of a NUL-terminated text that lies in a live HARNESS block (q, capw) of the
   ledger, the text's length below capw *)
Lemma rcl_hblk_str : forall ly S Hp W mem md Lam peak cnt fail ran most own q capw n,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> In (q, capw) Lam ->
  0 <= n -> n < capw ->
  0 < q /\ q + n + 1 <= 2 ^ 63 /\ q + n < YM05.alloc_ceiling /\
  YGcfStr.amem_range8 q (n + 1) /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF q (n + 1) /\
  shadow_hull_vis (aview segs (w_H W) mem) q (n + 1) /\
  (forall a, q + n < a < q + n - (q + n) mod 8 + 8 -> aview segs (w_H W) mem a <> None).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own q capw n HAR HL Hin Hn0 Hlt.
unfold prh_head_wide in HW.
pose proof (proj1 (Forall_forall _ _) (prh_ledger_blocks B ly S Hp W mem Lam peak cnt fail ran most own HL) (q, capw) Hin) as Hb.
cbn [fst snd] in Hb. destruct Hb as (Hk0 & Hab & Hhp & H16 & _).
assert (Hreq : req_size (capw + cf_head) = capw + cf_head)
  by (unfold req_size; destruct (Z.eqb_spec (capw + cf_head) 0); lia).
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md (q - cf_head) (capw + cf_head) HAR Hab)
  as (_ & H4096 & Hceil & Happ & Hpr & _).
rewrite Hreq in Hceil, Happ.
destruct (alx_hshadow _ _ _ LAWS ly S Hp W mem md (q - cf_head) (capw + cf_head) HAR Hab Hhp) as [Hbs Hhu].
rewrite Hreq in Hbs, Hhu. replace (q - cf_head + cf_head) with q in Hbs, Hhu by lia.
replace (capw + cf_head - cf_head) with capw in Hbs, Hhu by lia.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [lia|]. split; [lia|]. split; [lia|]. split.
{ unfold YGcfStr.amem_range8. unfold in_app, kLowShadowBeg, ASAN_CEIL in Happ.
  destruct Happ as (_ & [Hlo | (Hhb & Hhe)]).
  - left. rewrite C5. lia.
  - right. apply Z.mod_divide in H16; [|lia]. destruct H16 as [aq Haq].
    assert (EK : kHighMemBeg = 16 * (kHighMemBeg / 16)) by (rewrite C3; reflexivity).
    set (kb := kHighMemBeg / 16) in *. rewrite C4. lia. }
split; [eapply block_shadow_range; [exact Hbs | lia | lia]|].
split; [apply (rcl_hull_sub _ q capw q (n + 1)); [apply Hhu; lia | lia | lia | lia]|].
intros a Ha. apply (rcl_tail_in_block ly S Hp W mem md (q - cf_head) (capw + cf_head) q capw (q + n) a HAR Hab);
  [rewrite Hreq; lia | lia | exact (fun x Hx => proj1 (Hpr x Hx)) | lia | lia | exact Ha].
Qed.

(* the same of a text in a live RAW block (want, cap): not a harness block (its base is no hidden head), so
   AR_laws_x's block shadow law (no hidden head inside it, by the blocks' separation) gives the shadow; its
   amem_range8 is the caller's (a raw block's start bound is kHighMemBeg, not kHighMemBeg + 15) *)
Lemma rcl_rawblk_str : forall ly S Hp W mem md Lam peak cnt fail ran most own want cap n,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (want, cap) (ablocks B ly S) -> ~ In want Hp -> 0 <= n -> n < cap ->
  0 < want /\ want + n + 1 <= 2 ^ 63 /\ want + n < YM05.alloc_ceiling /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF want (n + 1) /\
  shadow_hull_vis (aview segs (w_H W) mem) want (n + 1) /\
  (forall a, want + n < a < want + n - (want + n) mod 8 + 8 -> aview segs (w_H W) mem a <> None).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own want cap n HAR HL Hwin HnHp Hn0 Hlt.
unfold prh_head_wide in HW.
assert (Hreq : req_size cap = cap) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia).
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md want cap HAR Hwin) as (_ & H4096 & Hceil & _ & Hpr & _).
rewrite Hreq in Hceil.
assert (Hnoh : forall h0, In h0 Hp -> ~ (want <= h0 < want + req_size cap)).
{ intros h0 Hh0 Hr. pose proof Hh0 as Hh0'.
  apply (Permutation_in _ (prh_ledger_heads B ly S Hp W mem Lam peak cnt fail ran most own HL)) in Hh0.
  apply in_map_iff in Hh0 as ([a k] & Ea & Hink). cbn [fst] in Ea.
  pose proof (proj1 (Forall_forall _ _) (prh_ledger_blocks B ly S Hp W mem Lam peak cnt fail ran most own HL) (a, k) Hink) as Hb.
  cbn [fst snd] in Hb. destruct Hb as (Hk0 & Hab & _ & _ & _).
  assert (Hne : (want, cap) <> (a - cf_head, k + cf_head)).
  { intros E. injection E as E1 _. apply HnHp. rewrite E1, Ea. exact Hh0'. }
  pose proof (sep_blocks_x _ _ _ LAWS ly S Hp W mem md want cap (a - cf_head) (k + cf_head) HAR Hwin Hab Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  assert (Hrk : req_size (k + cf_head) = k + cf_head) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
  rewrite Hreq, Hrk in Hd. rewrite Hreq in Hr. lia. }
destruct (alx_shadow _ _ _ LAWS ly S Hp W mem md want cap HAR Hwin Hnoh) as [Hbs Hhu].
rewrite Hreq in Hbs, Hhu.
split; [lia|]. split; [pose proof asan_consts as (C1 & _); lia|]. split; [lia|].
split; [eapply block_shadow_range; [exact Hbs | lia | lia]|].
split; [apply (rcl_hull_sub _ want cap want (n + 1)); [exact Hhu | lia | lia | lia]|].
intros a Ha. apply (rcl_tail_in_block ly S Hp W mem md want cap want cap (want + n) a HAR Hwin);
  [rewrite Hreq; lia | lia | exact (fun x Hx => proj1 (Hpr x Hx)) | lia | lia | exact Ha].
Qed.

End c.
