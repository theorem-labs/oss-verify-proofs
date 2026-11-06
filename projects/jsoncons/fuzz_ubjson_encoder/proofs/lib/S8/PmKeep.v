(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmModelFacts PmStatics PmStep.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMKP.

Ltac outW := repeat (apply L5C.outside_cons; [unfold L5.in_rng; cbn [fst snd]; lia|]); apply L5C.outside_nil.

Section Keep.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis KL : PMK.klayout segs L.

Definition cstatic (a : Z) : Prop := hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a.

Lemma kept_cstatic LB sp scr W a : cstatic a -> L5.outside W a -> L5C.kept L LB sp scr W a.
Proof.
  intros (I & S & E) OW. pose proof (PMK.kl_img segs L KL) as KI. split; [lia|]. split; [right; right; split; assumption|]. split; assumption.
Qed.
Lemma kept_stack LB M sp scr W a : L5C.stk (hl_sptop L) M sp scr -> 0 <= scr -> sp <= a < 2 ^ 64 -> L5.outside W a -> L5C.kept L LB sp scr W a.
Proof.
  intros ST Hs Ha OW. pose proof (PMK.kl_img segs L KL) as KI. pose proof (PMK.kl_errno segs L KL) as KE.
  apply (L5C.kept_stack_stk L LB M sp scr W a ST Hs Ha); [lia| exact OW].
Qed.
Lemma kept_block LB sp scr W B n a : In (B, n) LB -> B <= a < B + n -> 0 <= B -> B + n <= hl_ceil L -> (B + n <= hl_img_lo L \/ hl_img_hi L <= B) ->
  hl_sptop L <= 2 ^ 47 -> L5.outside W a -> L5C.kept L LB sp scr W a.
Proof.
  intros Hin Ha HB Hc Hh Hs OW. pose proof (PMK.kl_errno segs L KL) as KE.
  apply (L5C.kept_block L LB sp scr W B n a Hin Ha HB); [lia| lia| exact OW].
Qed.

Lemma ek_agree LB sp scr W M M' a n : PMK.ek L LB sp scr W M M' -> (forall i, a <= i < a + n -> L5C.kept L LB sp scr W i) -> L5C.agree_on M M' a n.
Proof. intros E K i Hi. apply E. apply K. exact Hi. Qed.
Lemma ek_agree_stack LB sp scr W M M' a n :
  PMK.ek L LB sp scr W M M' -> L5C.stk (hl_sptop L) M sp scr -> 0 <= scr -> sp <= a -> a + n <= 2 ^ 64 ->
  (forall i, a <= i < a + n -> L5.outside W i) -> L5C.agree_on M M' a n.
Proof. intros E ST Hs Ha Hn OW. apply (ek_agree LB sp scr W M M' a n E). intros i Hi. apply (kept_stack LB M sp scr W i ST Hs); [lia| apply OW; exact Hi]. Qed.
Lemma ek_agree_static LB sp scr W M M' a n :
  PMK.ek L LB sp scr W M M' -> (forall i, a <= i < a + n -> cstatic i /\ L5.outside W i) -> L5C.agree_on M M' a n.
Proof. intros E C. apply (ek_agree LB sp scr W M M' a n E). intros i Hi. destruct (C i Hi). apply kept_cstatic; assumption. Qed.

Lemma clear_agree M M' lo hi : L5C.agree_on M M' lo (hi - lo) -> L5.img_clear M lo hi -> L5.img_clear M' lo hi.
Proof. intros AG C i Hi. rewrite AG by lia. apply C. exact Hi. Qed.

Record sfoot : Prop := SFOOT {
  sf_wf : PMST.addrs_wf A;
  sf_ro : forall a, 65536 <= a < pa_rw_lo A -> cstatic a;
  sf_foot : forall iv a, In iv (pm_foot A) -> fst iv <= a < snd iv -> cstatic a;
  sf_canary : forall a, pa_canary A <= a < pa_canary A + 8 -> cstatic a;
  sf_initc : forall iv a, In iv (pm_initc A) -> fst iv <= a < snd iv -> cstatic a
}.
Hypothesis SF : sfoot.

Section Along.
Variables (LB : list (Z * Z)) (sp scr : Z) (W : list L5.range) (M M' : word -> option byte).
Hypothesis E : PMK.ek L LB sp scr W M M'.

Lemma dep_agree : (forall a, PMST.dep A a -> L5.outside W a) ->
  forall a, 0 <= a < 2 ^ 64 -> PMST.dep A a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof.
  intros OW a Ha D. apply E. apply kept_cstatic; [|apply OW; exact D].
  destruct D as [(iv & Hin & Hr)|[Hc|(iv & Hin & Hr)]]; [apply (sf_foot SF iv a Hin Hr)| apply (sf_canary SF a Hc)| apply (sf_initc SF iv a Hin Hr)].
Qed.

Lemma ls_ok_keep g : (forall a, PMST.dep A a -> L5.outside W a) -> (forall a, 65536 <= a < pa_rw_lo A -> L5.outside W a) ->
  PMST.ls_ok segs A g M -> PMST.ls_ok segs A g M'.
Proof.
  intros OD OR H. apply (PMST.ls_ok_frame segs A (sf_wf SF) M M'); [exact (dep_agree OD)| |exact H].
  intros a Ha Hn. rewrite E; [exact Hn|]. apply kept_cstatic; [apply (sf_ro SF); exact Ha| apply OR; exact Ha].
Qed.

Lemma base_ok_keep :
  (forall a, 65536 <= a < pa_rw_lo A -> L5.outside W a) -> (forall a, pa_canary A <= a < pa_canary A + 8 -> L5.outside W a) ->
  (forall a, pa_need_locks A <= a < pa_need_locks A + 1 -> L5.outside W a) -> (forall a, pa_locale_lock A <= a < pa_locale_lock A + 4 -> L5.outside W a) ->
  PMST.base_ok segs A M -> PMST.base_ok segs A M'.
Proof.
  intros O1 O2 O3 O4 (RO0 & (can & Hcan & CAN) & NL & LL).
  pose proof (PMST.aw_canary A (sf_wf SF)) as Hc. pose proof (PMST.aw_nl A (sf_wf SF)) as Hn. pose proof (PMST.aw_ll A (sf_wf SF)) as Hl. pose proof (PMST.aw_rw A (sf_wf SF)) as Hr.
  split; [|split; [|split]].
  - apply (clear_agree M M' 65536 (pa_rw_lo A)); [|exact RO0]. apply (ek_agree_static LB sp scr W M M' _ _ E). intros i Hi. split; [apply (sf_ro SF); lia| apply O1; lia].
  - exists can. split; [exact Hcan|]. apply (L5C.u64_at_agree segs M M'); [|lia|lia|exact CAN].
    apply (ek_agree_static LB sp scr W M M' _ _ E). intros i Hi. split; [apply (sf_canary SF); lia| apply O2; lia].
  - apply (clear_agree M M' _ _); [|exact NL]. apply (ek_agree_static LB sp scr W M M' _ _ E). intros i Hi. split; [|apply O3; lia].
    apply (sf_initc SF (pa_need_locks A, pa_need_locks A + 1)); [cbn; auto|cbn; lia].
  - apply (clear_agree M M' _ _); [|exact LL]. apply (ek_agree_static LB sp scr W M M' _ _ E). intros i Hi. split; [|apply O4; lia].
    apply (sf_initc SF (pa_locale_lock A, pa_locale_lock A + 4)); [cbn; auto|cbn; lia].
Qed.

Lemma agree_st a n : (forall i, a <= i < a + n -> cstatic i /\ L5.outside W i) -> L5C.agree_on M M' a n.
Proof. apply (ek_agree_static LB sp scr W M M' a n E). Qed.

Lemma loc_ok_keep b : (forall iv a, In iv (pa_loc_foot A) -> fst iv <= a < snd iv -> L5.outside W a) ->
  PMST.loc_ok segs A M b -> PMST.loc_ok segs A M' b.
Proof.
  intros OW H. pose proof (PMST.aw_gloc A (sf_wf SF)) as Hg. unfold PMST.loc_ok in *. destruct b.
  - destruct H as (G & P). destruct (PMST.aw_gloc_in A (sf_wf SF)) as (iv & Hin & Hlo & Hhi).
    assert (CS : forall i, pa_glocale A + 32 <= i < pa_glocale A + 41 -> cstatic i /\ L5.outside W i).
    { intros i Hi. split; [apply (sf_foot SF iv); [|lia]| apply (OW iv); [exact Hin| lia]].
      unfold pm_foot. cbn [app]. right. right. apply in_or_app. left. exact Hin. }
    split.
    + apply (L5C.u8_at_agree segs M M'); [|lia|lia|exact G]. apply agree_st. intros i Hi. apply CS. lia.
    + apply (L5C.u64_at_agree segs M M'); [|lia|lia|exact P]. apply agree_st. intros i Hi. apply CS. lia.
  - intros iv Hin. apply (clear_agree M M' (fst iv) (snd iv)); [|apply H; exact Hin]. apply agree_st. intros i Hi.
    split; [apply (sf_foot SF iv); [|lia]| apply (OW iv); [exact Hin| lia]].
    unfold pm_foot. cbn [app]. right. right. apply in_or_app. left. exact Hin.
Qed.

Lemma sys_ok_keep b : (forall a, pa_syscat_guard A <= a < pa_syscat_guard A + 2 -> L5.outside W a) ->
  PMST.sys_ok segs A M b -> PMST.sys_ok segs A M' b.
Proof.
  intros OW H. pose proof (PMST.aw_sysg A (sf_wf SF)) as Hg. unfold PMST.sys_ok in *.
  assert (CS : forall i, pa_syscat_guard A <= i < pa_syscat_guard A + 2 -> cstatic i /\ L5.outside W i).
  { intros i Hi. split; [|apply OW; exact Hi]. apply (sf_foot SF (pa_syscat_guard A, pa_syscat_guard A + 2)); [|cbn; lia]. unfold pm_foot. cbn. auto. }
  destruct b.
  - apply (L5C.u8_at_agree segs M M'); [|lia|lia|exact H]. apply agree_st. intros i Hi. apply CS. lia.
  - apply (clear_agree M M' _ _); [|exact H]. apply agree_st. intros i Hi. apply CS. lia.
Qed.

Lemma err_ok_keep b : (forall a, pa_errcat_guard A <= a < pa_errcat_guard A + 2 -> L5.outside W a) ->
  (forall a, pa_atexit A <= a < pa_atexit A + 544 -> L5.outside W a) ->
  PMST.err_ok segs A M b -> PMST.err_ok segs A M' b.
Proof.
  intros OG OA (G & AT). pose proof (PMST.aw_errg A (sf_wf SF)) as Hg. pose proof (PMST.aw_atexit A (sf_wf SF)) as Ha.
  assert (CG : forall i, pa_errcat_guard A <= i < pa_errcat_guard A + 2 -> cstatic i /\ L5.outside W i).
  { intros i Hi. split; [|apply OG; exact Hi]. apply (sf_foot SF (pa_errcat_guard A, pa_errcat_guard A + 2)); [|cbn; lia]. unfold pm_foot. cbn. auto. }
  assert (CA : forall i, pa_atexit A <= i < pa_atexit A + 544 -> cstatic i /\ L5.outside W i).
  { intros i Hi. split; [|apply OA; exact Hi]. apply (sf_foot SF (pa_atexit A, pa_atexit A + 544)); [|cbn; lia].
    unfold pm_foot. cbn [app]. right. right. apply in_or_app. right. cbn. auto. }
  split.
  - destruct b.
    + apply (L5C.u8_at_agree segs M M'); [|lia|lia|exact G]. apply agree_st. intros i Hi. apply CG. lia.
    + apply (clear_agree M M' _ _); [|exact G]. apply agree_st. intros i Hi. apply CG. lia.
  - apply (PMST.atexit_agree segs A (sf_wf SF) M M'); [|exact AT]. intros i Hi. apply (agree_st (pa_atexit A) 544); [exact CA| lia].
Qed.

End Along.
End Keep.
End PMKP.
