(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState ITree Nodes NodesMat Decode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad MSafe MSil STree Malloc MallocCtrl RawAlloc KInv KLink KStep KStepX
  Realloc ReallocProto MI_Tree MI_Inv MI_Sim MI_Contracts MI_Simrel MI_LedgerAgree MI_WRealloc MI_WRealloc2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocOracle MallocVocab MallocBlocks MallocHINV MallocFacts_inv MallocRealloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition KOWN (G : PState -> Model -> Prop) : assn PState := fun s mo =>
  (exists L, SIMREL (ps_m s) L /\ KL L (ps_brk s) mo) /\ G s mo.

Lemma KOWN_G : forall G s mo, KOWN G s mo -> G s mo.
Proof. intros G s mo [_ H]. exact H. Qed.

Lemma KOWN_minv : forall G s mo, KOWN G s mo -> minv mo /\ m_halted mo = None.
Proof. intros G s mo [(L & _ & HK) _]. split; [exact (kl_minv _ _ _ HK)| exact (kl_halt _ _ _ HK)]. Qed.

Lemma KOWN_weakG : forall G G' s mo, KOWN G s mo -> (G s mo -> G' s mo) -> KOWN G' s mo.
Proof. intros G G' s mo [H HG] HGG. split; auto. Qed.

(* [comment removed for export] *)
Lemma KOWN_other : forall G s s' mo, KOWN G s mo -> ps_m s' = ps_m s -> ps_brk s' = ps_brk s -> G s' mo -> KOWN G s' mo.
Proof. intros G s s' mo [(L & HS & HK) _] Em Eb HG. split; [|exact HG]. exists L. rewrite Em, Eb. auto. Qed.

(* [comment removed for export] *)
Lemma KL_of_HINV : forall G s mo resv st LB,
  KOWN G s mo -> strip st = ps_m s -> HINV_from resv st (ps_brk s) LB ->
  exists L LS BL, INVL x0 st L BL LS /\ ld_live L = map bslot BL /\ ld_resv L = resv /\ s_secret st = rc_secret
                  /\ CORR st LB BL /\ KL L (ps_brk s) mo.
Proof.
  intros G s mo resv st LB [(L1 & (st1 & BL1 & LS1 & Es1 & INV1 & LIVE1) & HK) _] Es [_ AR].
  destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & LIVE & RESV & SEC & CR).
  exists L, LS, BL. splits; auto.
  eapply KL_agree; [| exact HK]. eapply INVL_ledger_agree; [exact INV1| exact INV| congruence].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem raw_malloc_spec_k : forall G n, frame_ok G -> 0 <= n ->
  mspec (KOWN G) (raw_malloc n) (fun r s mo => KOWN G s mo /\ match r with Some _ => n < 2^63 | None => True end).
Proof.
  intros G n HG Hn. unfold raw_malloc.
  eapply mspec_bind; [apply mspec_get|]. intros s0.
  apply mspec_pointwise. intros s1 mo1 [-> [(L & HS & HK) HGs]].
  eapply mspec_bind.
  { eapply mspec_pre; [apply (membed_spec (cmalloc (ps_m s1) n) _ G L s1 HG (cmalloc_contract_sim _ _ _ HS Hn))|].
    intros s mo [-> ->]. auto. }
  intros [st' p]. cbn beta iota.
  apply mspec_pointwise. intros s2 mo2 (L' & Hp & HPost & HK' & HG' & Hm & Hfa & Hso).
  eapply mspec_seq with (R := fun s mo => s = set_m st' s2 /\ mo = mo2).
  { apply mspec_upd'. intros s mo [-> ->]. auto. }
  intros _. apply mspec_ret. intros s mo [-> ->].
  destruct (SIMREL_malloc _ _ _ _ _ _ HS Hn Hp) as [HS' _].
  assert (HG2 : G (set_m st' s2) mo2). { apply (HG s2 _ mo2 _); [reflexivity|reflexivity|apply vm_only_refl| exact HG']. }
  split.
  - split; [|exact HG2]. destruct p as [c|].
    + exists (set_live (c :: ld_live L') L'). split; [exact HS'|]. apply KL_set_live. exact HK'.
    + exists L'. split; [exact HS'| exact HK'].
  - destruct p as [c|]; [|exact I]. destruct (size_overflows n) eqn:E.
    + exfalso. rewrite (cmalloc_overflow _ _ E) in Hp. inversion Hp.
    + unfold size_overflows in E. apply Z.leb_gt in E. lia.
Qed.

Theorem raw_malloc_tsil : forall G n s mo, frame_ok G -> 0 <= n -> KOWN G s mo ->
  tsil (raw_malloc n s) mo
       (fun p mo' => match p with
                     | Unr => False
                     | Ok (r, s') => KOWN G s' mo' /\ match r with Some _ => n < 2^63 | None => True end
                     end).
Proof.
  intros G n s mo HG Hn HO.
  eapply tsil_mono; [apply (mspec_tsil _ _ _ s mo (raw_malloc_spec_k G n HG Hn) HO (tmm_raw_malloc n s))|].
  intros [|[r s']] mo'; cbn; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma live_of_HINV : forall st L LS BL LB (b : block),
  INVL x0 st L BL LS -> ld_live L = map bslot BL -> CORR st LB BL -> In b LB ->
  exists off n0, In ((blk_slot b, off), n0) BL /\ In (blk_slot b) (ld_live L)
    /\ blk_addr b = conc st (blk_slot b) + UNIT * off /\ blk_size b = n0.
Proof.
  intros st L LS BL LB b INV LIVE CR Hb.
  destruct (Forall2_In_l _ _ _ _ CR Hb) as (k & Hk & (C1 & C2 & C3)).
  destruct k as [[c off] n0]. cbn [bslot boff bsize fst snd] in C1, C2, C3.
  exists off, n0. rewrite C1. splits; auto.
  rewrite LIVE. apply in_map_iff. exists ((c, off), n0). split; [reflexivity| exact Hk].
Qed.

Theorem raw_free_spec_k : forall G resv st LB (b : block) (p : bptr) s0 mo0,
  frame_ok G -> KOWN G s0 mo0 -> strip st = ps_m s0 -> HINV_from resv st (ps_brk s0) LB ->
  In b LB -> fst p = blk_slot b ->
  mspec (fun s mo => s = s0 /\ mo = mo0) (raw_free p) (fun _ => KOWN G).
Proof.
  intros G resv st LB b p s0 mo0 HG HO Es HH Hb Hp.
  destruct (KL_of_HINV _ _ _ _ _ _ HO Es HH) as (L & LS & BL & INV & LIVE & RESV & SEC & CR & HK).
  destruct (live_of_HINV _ _ _ _ _ _ INV LIVE CR Hb) as (off & n0 & Hk & Hin & _).
  assert (HS : SIMREL (ps_m s0) L). { exists st, BL, LS. auto. }
  pose proof (KOWN_G _ _ _ HO) as HGs.
  unfold raw_free.
  eapply mspec_bind; [apply mspec_get|]. intros s1.
  apply mspec_pointwise. intros s2 mo1 [-> [-> ->]].
  rewrite Hp in *.
  eapply mspec_bind.
  { eapply mspec_pre; [apply (membed_spec (cfree (ps_m s0) (Some (blk_slot b))) _ G L s0 HG (cfree_contract_sim _ _ _ HS Hin))|].
    intros s mo [-> ->]. auto. }
  intros st'. cbn beta iota.
  apply mspec_pointwise. intros s2 mo2 (L' & Hpth & _ & HK' & HG' & Hm & Hfa & Hso).
  apply mspec_upd'. intros s mo [-> ->].
  pose proof (SIMREL_free _ _ _ _ _ HS Hin Hpth) as HS'.
  split; [| apply (HG s2 _ mo2 _); [reflexivity|reflexivity|apply vm_only_refl| exact HG']].
  exists (set_live (ap_remove (blk_slot b) (ld_live L')) L'). split; [exact HS'|]. apply KL_set_live. exact HK'.
Qed.

Theorem raw_free_tsil : forall G resv st LB (b : block) (p : bptr) s mo,
  frame_ok G -> KOWN G s mo -> strip st = ps_m s -> HINV_from resv st (ps_brk s) LB ->
  In b LB -> fst p = blk_slot b ->
  tsil (raw_free p s) mo (fun r mo' => match r with Unr => False | Ok (_, s') => KOWN G s' mo' end).
Proof.
  intros G resv st LB b p s mo HG HO Es HH Hb Hp.
  eapply tsil_mono; [apply (mspec_tsil _ _ _ s mo (raw_free_spec_k G resv st LB b p s mo HG HO Es HH Hb Hp) (conj eq_refl eq_refl) (tmm_raw_free p s))|].
  intros [|[r s']] mo'; cbn; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition realloc_kpost (G : PState -> Model -> Prop) (s0 : PState)
  (r : mstate * optr) (s : PState) (mo : Model) : Prop :=
  KOWN G s mo /\ ps_m s = strip (fst r) /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0.

Theorem realloc_spec_k : forall G resv st LB (b : block) (pf : aptr) n (o : mem) s0 mo0,
  frame_ok G -> KOWN G s0 mo0 -> strip st = ps_m s0 -> HINV_from resv st (ps_brk s0) LB ->
  In b LB -> fst pf = fst (blk_slot b) -> conc st pf = blk_addr b -> 0 <= n ->
  mspec (fun s mo => s = s0 /\ mo = mo0) (raw_realloc o st pf n) (realloc_kpost G s0).
Proof.
  intros G resv st LB b pf n o s0 mo0 HG HO Es HH Hb Hfst Hconc Hn.
  destruct (KL_of_HINV _ _ _ _ _ _ HO Es HH) as (L & LS & BL & INV & LIVE & RESV & SEC & CR & HK).
  destruct (live_of_HINV _ _ _ _ _ _ INV LIVE CR Hb) as (off & n0 & Hk & Hin & Haddr & _).
  pose proof (KOWN_G _ _ _ HO) as HGs.
  (* [comment removed for export] *)
  destruct (MI_WRealloc2.blk_region _ _ _ _ _ _ INV Hk) as (rg & Hrg & _). cbn [bslot fst snd] in Hrg.
  assert (Epf : pf = aadd (blk_slot b) (UNIT * off)).
  { unfold conc, get_region in Hconc, Haddr. rewrite Hfst in Hconc. rewrite Hrg in Hconc, Haddr. rewrite Haddr in Hconc.
    apply injective_projections; unfold aadd; cbn [fst snd]; [exact Hfst| lia]. }
  subst pf.
  (* [comment removed for export] *)
  pose proof (realloc_INVL st L BL LS (blk_slot b) off n0 n INV Hk Hn) as FT.
  pose proof (ptreeX_xctree_ok _ _ _ (ftreeX_xprun pans_mem pupd_mem pans_mem_range _ _ _ o FT)) as CT.
  unfold raw_realloc.
  eapply mspec_bind.
  { eapply mspec_pre; [apply (xmembed_spec (xmrun o (realloc st (Some (aadd (blk_slot b) (UNIT * off))) n)) _ G L s0 HG CT)|].
    intros s mo [-> ->]. auto. }
  intros [o' [st' q]]. cbn beta iota.
  apply mspec_pointwise. intros s2 mo2 (L' & Hpth & HPost & HK' & HG' & Hm & Hfa & Hso).
  eapply mspec_seq with (R := fun s mo => s = set_m (strip st') s2 /\ mo = mo2).
  { apply mspec_upd'. intros s mo [-> ->]. auto. }
  intros _. apply mspec_ret. intros s mo [-> ->].
  cbn [snd fst] in HPost. unfold RPOST in HPost. cbn [fst snd] in HPost.
  pose proof (xcpath_live Hpth) as Hlive.
  assert (HG2 : G (set_m (strip st') s2) mo2). { apply (HG s2 _ mo2 _); [reflexivity|reflexivity|apply vm_only_refl| exact HG']. }
  split; [| cbn; auto].
  split; [| exact HG2]. cbn [ps_m ps_brk set_m].
  destruct q as [p'|].
  - destruct HPost as (c' & off' & LS' & Ep' & Hoff' & INV').
    exists (set_live (map bslot (((c', off'), n) :: bl_remove (blk_slot b) BL)) L'). split; [| apply KL_set_live; exact HK'].
    exists st', (((c', off'), n) :: bl_remove (blk_slot b) BL), LS'. split; [reflexivity|]. split; [apply INVL_set_live; exact INV'| reflexivity].
  - destruct HPost as (LS' & INV').
    exists (set_live (map bslot BL) L'). split; [| apply KL_set_live; exact HK'].
    exists st', BL, LS'. split; [reflexivity|]. split; [apply INVL_set_live; exact INV'| reflexivity].
Qed.

Theorem realloc_tsil : forall G resv st LB (b : block) (pf : aptr) n (o : mem) s mo,
  frame_ok G -> KOWN G s mo -> strip st = ps_m s -> HINV_from resv st (ps_brk s) LB ->
  In b LB -> fst pf = fst (blk_slot b) -> conc st pf = blk_addr b -> 0 <= n ->
  tsil (raw_realloc o st pf n s) mo
       (fun r mo' => match r with Unr => False | Ok (x, s') => realloc_kpost G s x s' mo' end).
Proof.
  intros G resv st LB b pf n o s mo HG HO Es HH Hb Hfst Hconc Hn.
  eapply tsil_mono; [apply (mspec_tsil _ _ _ s mo (realloc_spec_k G resv st LB b pf n o s mo HG HO Es HH Hb Hfst Hconc Hn) (conj eq_refl eq_refl) (tmm_raw_realloc o st pf n s))|].
  intros [|[r s']] mo'; cbn; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma reserved_top_ge : forall l e, In e l -> bv_unsigned (fst e) + bv_unsigned (snd e) <= reserved_top l.
Proof.
  induction l as [|[a sz] l IH]; intros e Hin; [destruct Hin|].
  cbn [reserved_top]. destruct Hin as [<-|Hin]; cbn [fst snd]; [lia|]. specialize (IH e Hin). lia.
Qed.

(* [comment removed for export] *)
Lemma KL_init : forall segs brk0 mbase sp lim inp,
  bv_unsigned sp = rc_sp -> sp_window_lo <= rc_sp <= sp_window_hi ->
  valid_brk segs brk0 -> 0 < reserved_top (segments_reserved segs) ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling ->
  KL (led_init (reservedZ segs)) 0 (init_model (segments_reserved segs) brk0 mbase sp lim inp).
Proof.
  intros segs brk0 mbase sp lim inp Hsp Hspw (Hlo & Hhi & Hal) Hpos Hceil.
  constructor; rewrite ?m_vmmaps_init_model; cbn -[Z.pow Z.mul Z.add init_model].
  - apply minv_init; assumption.
  - apply m_halted_init_model.
  - split; [intros e []| apply pwdisj_nil].
  - reflexivity.
  - intros e Hin. pose proof (reserved_top_ge _ _ Hin). unfold ehi. lia.
  - unfold PGSZ in *. unfold page_size in Hal. lia.
  - intros b l [].
  - intros b l k [].
  - apply List.NoDup_nil.
  - intros b l H. discriminate.
  - split; reflexivity.
  - intros b l [].
  - intros e [].
  - apply m_vm_materialized_init.
  - intros e [].
Qed.

Theorem KOWN_init : forall G segs brk0 mbase sp lim inp,
  bv_unsigned sp = rc_sp -> sp_window_lo <= rc_sp <= sp_window_hi ->
  valid_brk segs brk0 -> 0 < reserved_top (segments_reserved segs) ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling ->
  G (ps_init (reservedZ segs)) (init_model (segments_reserved segs) brk0 mbase sp lim inp) ->
  KOWN G (ps_init (reservedZ segs)) (init_model (segments_reserved segs) brk0 mbase sp lim inp).
Proof.
  intros G segs brk0 mbase sp lim inp Hsp Hspw Hv Hpos Hceil HG. split; [|exact HG].
  exists (led_init (reservedZ segs)). split; [apply SIMREL_init| apply KL_init; assumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma m_vmmaps_with_tid : forall t mo, m_vmmaps (with_tid t mo) = m_vmmaps mo.
Proof. intros t mo. destruct mo; reflexivity. Qed.
Lemma m_halted_with_tid : forall t mo, m_halted (with_tid t mo) = m_halted mo.
Proof. intros t mo. destruct mo; reflexivity. Qed.

Lemma KL_with_tid : forall L pbrk mo t,
  0 < bv_unsigned t < PID_MAX_ENVELOPE -> KL L pbrk mo -> KL L pbrk (with_tid t mo).
Proof.
  intros L pbrk mo t Ht HK. destruct HK. constructor; rewrite ?m_vmmaps_with_tid, ?m_halted_with_tid, ?m_vm_materialized_with_tid; auto.
  apply minv_with_tid; assumption.
Qed.

Theorem KOWN_with_tid : forall G G' s mo t,
  0 < bv_unsigned t < PID_MAX_ENVELOPE -> KOWN G s mo -> (G s mo -> G' s (with_tid t mo)) -> KOWN G' s (with_tid t mo).
Proof.
  intros G G' s mo t Ht [(L & HS & HK) HG] HGG. split; [| exact (HGG HG)].
  exists L. split; [exact HS| apply KL_with_tid; assumption].
Qed.
End RC__1.
