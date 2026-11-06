(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Divembc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require SpinAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require SpinAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Ledger Hull Lazyiq4.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Divembc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.SpinAlg.Lazy9wo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.SpinAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Hull.Lazylo0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Ledger OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Hull OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Lazyiq4.

Module Madv3tp.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect Madvise.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require RelSpec SimInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec CatSim MmapSim AllocSim ShapeAlg Nodes.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SimInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.ExitSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Divembc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require SpinAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require SpinAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Ledger Hull Lazyiq4.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Divembc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.SpinAlg.Lazy9wo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.SpinAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Hull.Lazylo0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Ledger OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Hull OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Lazyiq4.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma syscall_spec_233 : forall i m o,
  bv_unsigned (in_sysno i) = 233%Z ->
  syscall_spec i m o <-> madvise_spec (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

(* [comment removed for export] *)
Lemma madvise_dontneed_outcome : forall addr len advice i m o,
  (bv_unsigned addr mod page_size = 0)%Z ->
  madvise_dontneed_b advice = true ->
  w_is0 len = false ->
  (bv_unsigned addr + page_round_up_Z (bv_unsigned len) < two_pow_64)%Z ->
  let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned len)) in
  madvise_dontneed_ok (m_vmmaps m) addr n = true ->
  madvise_spec addr len advice i m o <->
  o = Ok (mkEffect (Z_to_bv 64 0) [] [(addr, n)]) (madvise_dontneed_next m addr n) [].
Proof.
  intros addr len advice i m o Hal Hadv Hlen Hnw. cbv zeta. intros Hok.
  unfold madvise_spec.
  rewrite (proj2 (Z.eqb_eq _ _) Hal), Hadv, Hlen, (proj2 (Z.leb_gt _ _) Hnw). cbn [negb].
  sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hok in *; inv_sys. reflexivity.
  - intros ->. eexists _, _, _, _. split; [reflexivity|]. rewrite Hok.
    split; [|reflexivity]. eexists _, _, _, _. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition madvise_args_ok (ms : machine_state) (model : Model) : Prop :=
  let addr := ms_gpr ms 0 in
  let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) in
  (bv_unsigned addr mod page_size = 0)%Z
  /\ ms_gpr ms 1 <> Z_to_bv 64 0
  /\ ms_gpr ms 2 = Z_to_bv 64 4
  /\ (bv_unsigned addr + page_round_up_Z (bv_unsigned (ms_gpr ms 1)) < two_pow_64)%Z
  /\ madvise_dontneed_ok (m_vmmaps model) addr n = true.

(* [comment removed for export] *)
Lemma madvise_args_ok_intro : forall (ms : machine_state) (model : Model),
  let addr := ms_gpr ms 0 in
  let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) in
  (bv_unsigned addr mod page_size = 0)%Z ->
  ms_gpr ms 1 <> Z_to_bv 64 0 ->
  ms_gpr ms 2 = Z_to_bv 64 4 ->
  (bv_unsigned addr + page_round_up_Z (bv_unsigned (ms_gpr ms 1)) < two_pow_64)%Z ->
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  region_free (vm_noaccess (m_vmmaps model)) addr n = true ->
  madvise_args_ok ms model.
Proof.
  intros ms model addr n H1 H2 H3 H4 H5 H6 H7. unfold madvise_args_ok. cbv zeta.
  repeat (split; [assumption|]). unfold madvise_dontneed_ok. fold addr n. rewrite H5, H6, H7. reflexivity.
Qed.

Definition madvise_eff (ms : machine_state) : SyscallEffect :=
  mkEffect (Z_to_bv 64 0) []
           [(ms_gpr ms 0, Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))].

Definition madvise_model (addr n : word) (m : Model) : Model := madvise_dontneed_next m addr n.

Lemma madvise_model_halted : forall addr n m, m_halted (madvise_model addr n m) = m_halted m.
Proof. reflexivity. Qed.
Lemma madvise_model_vmmaps : forall addr n m, m_vmmaps (madvise_model addr n m) = m_vmmaps m.
Proof. reflexivity. Qed.
Lemma madvise_model_lazy : forall addr n m, m_vm_lazy (madvise_model addr n m) = m_vm_lazy m.
Proof. reflexivity. Qed.
Lemma madvise_model_materialized : forall addr n m,
  m_vm_materialized (madvise_model addr n m)
  = List.filter (page_outside_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)) (m_vm_materialized m).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma madvise_same_but_materialized : forall addr n m,
  same_but_materialized m (madvise_model addr n m).
Proof. intros addr n m. unfold same_but_materialized, madvise_model, madvise_dontneed_next. reflexivity. Qed.

Lemma int32_lit4 : madvise_dontneed_b (int32 (Z_to_bv 64 4)) = true.
Proof. vm_compute. reflexivity. Qed.

Section WithSegsM.
Variable segs : list Segment.

Lemma madvise_outcome_si : forall ms x8 model o,
  bv_unsigned x8 = 233%Z ->
  madvise_args_ok ms model ->
  syscall_spec (sys_input segs ms x8) model o <->
  o = Ok (madvise_eff ms)
         (madvise_model (ms_gpr ms 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) model) [].
Proof.
  (intros ms x8 model o Hno; (first [ intro dR_1; dand5 dR_1 as Hal Hlen H2 Hnw Hok | intros (Hal & Hlen & H2 & Hnw & Hok) ])).
  rewrite (syscall_spec_233 _ model o) by (rewrite in_sysno_si'; exact Hno).
  rewrite in_arg0_si', in_arg1_si', in_arg2_si', H2.
  unfold madvise_eff, madvise_model.
  apply (madvise_dontneed_outcome (ms_gpr ms 0) (ms_gpr ms 1) (int32 (Z_to_bv 64 4)) (sys_input segs ms x8) model o);
    [exact Hal | exact int32_lit4 | apply w_is0_false_of_ne; exact Hlen | exact Hnw | exact Hok].
Qed.

(* [comment removed for export] *)
Lemma node_madvise : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 233%Z ->
  madvise_args_ok ms model ->
  node_ok segs (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (apply_effect ms (madvise_eff ms)))
                    (madvise_model (ms_gpr ms 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) model)).
Proof.
  intros ms model x8 Hh Hsvc Hno Hargs.
  apply (node_det_nil segs ms model x8 (madvise_eff ms) _ [] Hh Hsvc).
  - intros o. apply (madvise_outcome_si ms x8 model o Hno Hargs).
  - rewrite madvise_model_halted. exact Hh.
  - reflexivity.
Qed.

Lemma srz_madvise : forall ms model x8 T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 233%Z ->
  madvise_args_ok ms model ->
  srealizes segs (mkCfg (advance_past_svc (apply_effect ms (madvise_eff ms)))
                        (madvise_model (ms_gpr ms 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) model)) T ->
  srealizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 T Hh Hsvc Hno Hargs Hc.
  eapply srz_silent1; [apply (node_madvise ms model x8); assumption | exact Hc].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

End WithSegsM.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Open Scope Z_scope.

(* [comment removed for export] *)
Theorem MInv_madvise : forall A AL E (addr n : word) m,
  MInv A AL E m -> MInv A AL E (madvise_model addr n m).
Proof.
  intros A AL E addr n m HI.
  apply (MInv_rebuild A AL E E m _
           (Some (page_outside_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))) HI).
  - apply madvise_model_materialized.
  - apply lazy_sub_eq. apply madvise_model_lazy.
  - rewrite madvise_model_lazy. exact (minv_lazy_nw HI).
  - rewrite madvise_model_vmmaps. exact (minv_maps_nw HI).
  - rewrite madvise_model_vmmaps. exact (minv_noacc_nw HI).
  - rewrite madvise_model_vmmaps. exact (minv_nooverlap HI).
  - unfold madvise_model, madvise_dontneed_next. rewrite eager_used_wvb. exact (minv_eager HI).
  - rewrite madvise_model_vmmaps. reflexivity.
  - exact (minv_budget HI).
Qed.

(* [comment removed for export] *)
Theorem MInv_madvise_remove : forall A1 B A2 AL1 AL2 E (addr n : word) m,
  MInv (A1 ++ B ++ A2) (AL1 ++ B ++ AL2) E m ->
  bv_unsigned addr mod page_size = 0 ->
  (forall l h, In (l, h) B -> bv_unsigned addr <= l /\ h <= bv_unsigned addr + bv_unsigned n) ->
  (forall lo hi, In (lo, hi) (A1 ++ A2) -> iv_sub (AL1 ++ B ++ AL2) lo hi ->
                 iv_sub (AL1 ++ AL2) lo hi \/ lazy_free (m_vm_lazy m) lo hi) ->
  MInv (A1 ++ A2) (AL1 ++ AL2) E (madvise_model addr n m).
Proof.
  intros A1 B A2 AL1 AL2 E addr n m HI Hal HB HX.
  pose proof (MInv_madvise _ _ E addr n m HI) as HI'.
  apply (MInv_hulls_remove_all A1 B A2 AL1 AL2 E _ HI').
  - intros p [l h] Hp Hin. destruct (HB l h Hin) as [H1 H2].
    rewrite madvise_model_materialized in Hp.
    exact (forgotten_pages_avoid _ _ l h _ p Hal H1 H2 (minv_aligned HI) Hp).
  - rewrite madvise_model_lazy. exact HX.
Qed.

(* [comment removed for export] *)
Theorem MInv_madvise_remove_A : forall A1 B A2 AL E (addr n : word) m,
  MInv (A1 ++ B ++ A2) AL E m -> MInv (A1 ++ A2) AL E (madvise_model addr n m).
Proof.
  intros A1 B A2 AL E addr n m HI. apply (MInv_hull_remove_all A1 B A2 AL E). apply MInv_madvise. exact HI.
Qed.

Lemma lazy_free_madvise : forall (addr n : word) m lo hi,
  lazy_free (m_vm_lazy m) lo hi -> lazy_free (m_vm_lazy (madvise_model addr n m)) lo hi.
Proof. intros addr n m lo hi H. rewrite madvise_model_lazy. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma region_free_sub : forall (l : list (word * word)) (S L a n : word),
  region_free l S L = true ->
  bv_unsigned S <= bv_unsigned a -> bv_unsigned a + bv_unsigned n <= bv_unsigned S + bv_unsigned L ->
  region_free l a n = true.
Proof.
  induction l as [|[b k] l IH]; intros S L a n H H1 H2; [reflexivity|].
  cbn [region_free] in *. apply andb_true_iff in H as [Hov Hr].
  apply andb_true_iff. split; [| exact (IH S L a n Hr H1 H2)].
  apply negb_true_iff in Hov. apply negb_true_iff.
  unfold iv_overlap in *. apply andb_false_iff in Hov. apply andb_false_iff.
  destruct Hov as [Hov|Hov]; apply Z.ltb_ge in Hov; [left|right]; apply Z.ltb_ge; lia.
Qed.

(* [comment removed for export] *)
Lemma region_free_iv_subtract : forall (b k : word) (lo hi : Z) (S L : word),
  bv_unsigned b + bv_unsigned k <= 2 ^ 64 ->
  negb (iv_overlap S L b k) = true ->
  region_free (iv_subtract b k lo hi) S L = true.
Proof.
  intros b k lo hi S L Hnw Hov.
  pose proof (u64_bound b) as Bb. pose proof (u64_bound k) as Bk.
  apply negb_true_iff in Hov. unfold iv_overlap in Hov.
  apply andb_false_iff in Hov.
  assert (Hov' : bv_unsigned b + bv_unsigned k <= bv_unsigned S \/ bv_unsigned S + bv_unsigned L <= bv_unsigned b).
  { destruct Hov as [Hov|Hov]; apply Z.ltb_ge in Hov; [left|right]; exact Hov. }
  clear Hov.
  unfold iv_subtract.
  destruct (Z.ltb (bv_unsigned b) lo) eqn:E1; destruct (Z.ltb hi (bv_unsigned b + bv_unsigned k)) eqn:E2;
    cbn [app region_free]; rewrite ?andb_true_r; repeat (apply andb_true_iff; split); try reflexivity;
    apply negb_true_iff; unfold iv_overlap; apply andb_false_iff.
  all: try (apply Z.ltb_lt in E1). all: try (apply Z.ltb_lt in E2).
  all: cbn [fst snd]; rewrite ?Z_to_bv64_unsigned_small by lia.
  all: destruct Hov' as [Hov|Hov]; [left|right]; apply Z.ltb_ge; lia.
Qed.

Lemma region_free_app : forall (X Y : list (word * word)) (S L : word),
  region_free X S L = true -> region_free Y S L = true -> region_free (X ++ Y) S L = true.
Proof.
  induction X as [|[c d] X IHX]; intros Y S L HX HY; [exact HY|].
  cbn [app region_free] in *. apply andb_true_iff in HX as [H1 H2]. apply andb_true_iff.
  split; [exact H1| exact (IHX Y S L H2 HY)].
Qed.

Lemma region_free_maps_subtract : forall (l : list (word * word)) (lo hi : Z) (S L : word),
  entries_nowrap l ->
  region_free l S L = true ->
  region_free (maps_subtract l lo hi) S L = true.
Proof.
  induction l as [|[b k] l IH]; intros lo hi S L Hnw H; [reflexivity|].
  cbn [maps_subtract]. cbn [region_free] in H. apply andb_true_iff in H as [Hov Hr].
  apply entries_nowrap_cons in Hnw as [Hb Hl].
  apply region_free_app.
  - apply region_free_iv_subtract; [| exact Hov]. unfold entry_nowrap, Ledger.hi in Hb. cbn [fst snd] in Hb. exact Hb.
  - apply IH; [exact Hl | exact Hr].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition noacc_free (S L : word) (m : Model) : Prop :=
  region_free (vm_noaccess (m_vmmaps m)) S L = true.

Lemma noacc_free_vmmaps : forall S L m m',
  vm_noaccess (m_vmmaps m') = vm_noaccess (m_vmmaps m) -> noacc_free S L m -> noacc_free S L m'.
Proof. intros S L m m' E H. unfold noacc_free in *. rewrite E. exact H. Qed.

Lemma noacc_free_sbm : forall S L m m',
  same_but_materialized m m' -> noacc_free S L m -> noacc_free S L m'.
Proof.
  intros S L m m' SB H. apply (noacc_free_vmmaps S L m m'); [| exact H].
  rewrite (same_but_materialized_vmmaps _ _ SB). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma noacc_free_grant_rw : forall S L flags a n m,
  noacc_free S L m -> noacc_free S L (grant_model flags a n false m).
Proof.
  intros S L flags a n m H. apply (noacc_free_vmmaps S L m); [| exact H].
  rewrite grant_model_vmmaps. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma noacc_free_commit_rw : forall S L flags addr n m,
  entries_nowrap (vm_noaccess (m_vmmaps m)) ->
  noacc_free S L m -> noacc_free S L (commit_model flags addr n false m).
Proof.
  intros S L flags addr n m Hnw H. unfold noacc_free in *. rewrite commit_model_vmmaps. cbn [commit_vmmaps vm_noaccess app].
  apply region_free_maps_subtract; assumption.
Qed.

(* [comment removed for export] *)
Lemma noacc_free_munmap : forall S L a n m,
  entries_nowrap (vm_noaccess (m_vmmaps m)) ->
  noacc_free S L m -> noacc_free S L (munmap_modelL a n m).
Proof.
  intros S L a n m Hnw H. unfold noacc_free in *. rewrite munmap_modelL_vmmaps. cbn [munmap_vmmaps vm_noaccess].
  apply region_free_maps_subtract; assumption.
Qed.

Lemma noacc_free_madvise : forall S L addr n m,
  noacc_free S L m -> noacc_free S L (madvise_model addr n m).
Proof. intros S L addr n m H. exact (noacc_free_sbm S L m _ (madvise_same_but_materialized addr n m) H). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
End Madv3tp.


Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma In_map_has : forall X (a n : word), In (a, n) X -> map_has X a n = true.
Proof.
  intros X a n Hin. unfold map_has. apply existsb_exists. exists (a, n). split; [exact Hin|].
  cbn [fst snd]. unfold bv_eqb. rewrite !Z.eqb_refl. reflexivity.
Qed.

Lemma zin_rangeb_false : forall x r, zin_rangeb x r = false <-> ~ (lo r <= x < hi r).
Proof.
  intros x r. rewrite <- zin_rangeb_iff. destruct (zin_rangeb x r); split; intros H.
  - discriminate H. - exfalso; apply H; reflexivity. - intros X; discriminate X. - reflexivity.
Qed.

Lemma zcovb_nil : forall x, zcovb [] x = false.
Proof. reflexivity. Qed.

(* [comment removed for export] *)

Lemma zcovb_lazy_interior : forall (b k : word) x,
  entry_nowrap (b, k) -> zcovb (lazy_interior b k) x = true -> bv_unsigned b <= x < bv_unsigned b + bv_unsigned k.
Proof.
  intros b k x Hnw H. apply zcovb_true in H. destruct H as (p & Hin & Hx).
  pose proof (lazy_interior_sub b k p Hnw Hin) as [L R]. unfold lo, hi in *. cbn [fst snd] in *. lia.
Qed.

Lemma zcovb_single : forall (b k : word) x, zcovb [(b, k)] x = true -> bv_unsigned b <= x < bv_unsigned b + bv_unsigned k.
Proof.
  intros b k x H. rewrite zcovb_cons, zcovb_nil, orb_false_r in H. apply zin_rangeb_iff in H.
  unfold lo, hi in H. cbn [fst snd] in H. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition eager_map (a n : word) (m : Model) : Prop :=
  forall x, bv_unsigned a <= x < bv_unsigned a + bv_unsigned n -> zcovb (cuts m) x = false.

(* [comment removed for export] *)
Definition cuts_covered (m : Model) : Prop :=
  forall x, zcovb (cuts m) x = true -> zcovb (vm_maps (m_vmmaps m)) x = true.

(* [comment removed for export] *)
Definition cuts_coveredb (m : Model) : bool :=
  forallb (fun c => Z.leb (hi c) (lo c)
                    || existsb (fun e => Z.leb (lo e) (lo c) && Z.leb (hi c) (hi e)) (vm_maps (m_vmmaps m)))
          (cuts m).

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma eager_used_munmap_refund : forall (a n : word) m,
  entries_nowrap (vm_maps (m_vmmaps m)) ->
  entries_nowrap (vm_noaccess (m_vmmaps m)) -> entries_nowrap (m_vm_lazy m) ->
  nooverlap (vm_maps (m_vmmaps m)) ->
  In (a, n) (vm_maps (m_vmmaps m)) -> eager_map a n m ->
  eager_used (munmap_modelL a n m) + bv_unsigned n <= eager_used m.
Proof.
  intros a n m HX HNA HL Hd Hin HE.
  pose proof (eager_used_munmap_le a n m HX HNA HL Hd Hin) as LE.
  assert (R : rem (a, n) (cuts m) = bv_unsigned n); [|lia].
  unfold rem. replace (bv_unsigned n) with (hi (a, n) - lo (a, n)) by (unfold lo, hi; cbn [fst snd]; lia).
  apply zmeasure_all; [apply lo_hi|].
  intros x Hx. unfold lo, hi in Hx. cbn [fst snd] in Hx. rewrite (HE x Hx). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lazy_sub_munmap : forall (a n : word) m,
  entries_nowrap (m_vm_lazy m) -> lazy_sub (m_vm_lazy (munmap_modelL a n m)) (m_vm_lazy m).
Proof.
  intros a n m Hnw. rewrite munmap_modelL_lazy.
  apply lazy_sub_subtract; [exact Hnw | apply (lo_hi_range a n) | apply (lo_hi_range a n)].
Qed.

Lemma lazy_free_munmap : forall (a n : word) m lo hi,
  entries_nowrap (m_vm_lazy m) -> lazy_free (m_vm_lazy m) lo hi -> lazy_free (m_vm_lazy (munmap_modelL a n m)) lo hi.
Proof. intros a n m lo hi Hnw H. exact (lazy_free_mono _ _ lo hi (lazy_sub_munmap a n m Hnw) H). Qed.

Lemma lazy_free_munmap_MInv : forall A AL E (a n : word) m lo hi,
  MInv A AL E m -> lazy_free (m_vm_lazy m) lo hi -> lazy_free (m_vm_lazy (munmap_modelL a n m)) lo hi.
Proof. intros A AL E a n m lo hi HI. apply lazy_free_munmap. exact (minv_lazy_nw HI). Qed.

Theorem MInv_munmap_refund : forall A AL E (a n : word) m,
  MInv A AL E m ->
  map_has (vm_maps (m_vmmaps m)) a n = true ->
  eager_map a n m ->
  MInv A AL (E - bv_unsigned n) (munmap_modelL a n m).
Proof.
  intros A AL E a n m HI Hhas HE.
  apply (MInv_rebuild A AL E (E - bv_unsigned n) m _
           (Some (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n))) HI).
  - apply munmap_modelL_materialized.
  - apply lazy_sub_munmap. exact (minv_lazy_nw HI).
  - rewrite munmap_modelL_lazy. apply maps_subtract_nowrap; [exact (minv_lazy_nw HI) | apply (lo_hi_range a n) | apply (lo_hi_range a n)].
  - rewrite munmap_modelL_vmmaps. cbn. apply entries_nowrap_map_remove. exact (minv_maps_nw HI).
  - rewrite munmap_modelL_vmmaps. cbn. apply maps_subtract_nowrap; [exact (minv_noacc_nw HI) | apply (lo_hi_range a n) | apply (lo_hi_range a n)].
  - rewrite munmap_modelL_vmmaps. cbn. apply nooverlap_map_remove. exact (minv_nooverlap HI).
  - pose proof (eager_used_munmap_refund a n m (minv_maps_nw HI) (minv_noacc_nw HI) (minv_lazy_nw HI)
                  (minv_nooverlap HI) (map_has_In _ _ _ Hhas) HE).
    pose proof (minv_eager HI). lia.
  - rewrite munmap_modelL_vmmaps. reflexivity.
  - pose proof (minv_budget HI). pose proof (bv_unsigned_in_range 64 n). lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma eager_map_vm : forall (a n : word) m m',
  m_vmmaps m' = m_vmmaps m -> m_vm_lazy m' = m_vm_lazy m -> eager_map a n m -> eager_map a n m'.
Proof. intros a n m m' H1 H2 HE x Hx. unfold cuts in *. rewrite H1, H2. apply HE. exact Hx. Qed.

Lemma eager_map_sbm : forall (a n : word) m m',
  same_but_materialized m m' -> eager_map a n m -> eager_map a n m'.
Proof.
  intros a n m m' SB HE. rewrite SB. apply (eager_map_vm a n m); [apply m_vmmaps_wvb| apply m_vm_lazy_wvb| exact HE].
Qed.

Lemma eager_map_m_vm : forall (a n : word) m m',
  m_vm m' = m_vm m -> eager_map a n m -> eager_map a n m'.
Proof.
  intros a n m m' E. destruct m as [fd vm io fs proc lim tm], m' as [fd' vm' io' fs' proc' lim' tm' sg' sc'].
  cbn in E. subst vm'. apply eager_map_vm; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma eager_map_munmap : forall (a n b k : word) m,
  entries_nowrap (vm_noaccess (m_vmmaps m)) -> entries_nowrap (m_vm_lazy m) ->
  eager_map a n m -> eager_map a n (munmap_modelL b k m).
Proof.
  intros a n b k m HN HL HE x Hx. unfold cuts. rewrite munmap_modelL_vmmaps, munmap_modelL_lazy.
  cbn [vm_noaccess munmap_vmmaps]. pose proof (lo_hi_range b k) as [R0 R1].
  specialize (HE x Hx). unfold cuts in HE. rewrite zcovb_app in HE. apply orb_false_iff in HE. destruct HE as [E1 E2].
  rewrite zcovb_app, !zcovb_maps_subtract by assumption. rewrite E1, E2. reflexivity.
Qed.

Lemma eager_map_munmap_MInv : forall A AL E (a n b k : word) m,
  MInv A AL E m -> eager_map a n m -> eager_map a n (munmap_modelL b k m).
Proof. intros A AL E a n b k m HI. apply eager_map_munmap; [exact (minv_noacc_nw HI)| exact (minv_lazy_nw HI)]. Qed.

(* [comment removed for export] *)
Lemma lazy_free_of_eager_map : forall (a n : word) m,
  eager_map a n m -> lazy_free (m_vm_lazy m) (bv_unsigned a) (bv_unsigned a + bv_unsigned n).
Proof.
  intros a n m HE x Hx. specialize (HE x Hx). unfold cuts in HE. rewrite zcovb_app in HE.
  apply orb_false_iff in HE. exact (proj2 HE).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma eager_map_grant : forall (a n : word) flags (b k : word) na m,
  entry_nowrap (b, k) ->
  (bv_unsigned b + bv_unsigned k <= bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned b) ->
  eager_map a n m -> eager_map a n (grant_model flags b k na m).
Proof.
  intros a n flags b k na m Hnw D HE x Hx. unfold cuts. rewrite grant_model_vmmaps, grant_model_lazy.
  cbn [vm_noaccess grant_vmmaps].
  specialize (HE x Hx). unfold cuts in HE. rewrite zcovb_app in HE. apply orb_false_iff in HE. destruct HE as [E1 E2].
  rewrite !zcovb_app, E2, orb_false_r.
  assert (NB : zin_rangeb x (b, k) = false) by (apply zin_rangeb_false; unfold lo, hi; cbn [fst snd]; lia).
  assert (NI : zcovb (lazy_interior b k) x = false).
  { destruct (zcovb (lazy_interior b k) x) eqn:E; [|reflexivity]. pose proof (zcovb_lazy_interior b k x Hnw E). lia. }
  destruct na; [rewrite zcovb_cons, NB, E1|rewrite E1]; (destruct (mmap_noreserve_b flags); [rewrite NI|]); reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma eager_map_commit : forall (a n : word) flags (b k : word) na m,
  entries_nowrap (vm_noaccess (m_vmmaps m)) -> entries_nowrap (m_vm_lazy m) -> entry_nowrap (b, k) ->
  (bv_unsigned b + bv_unsigned k <= bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned b) ->
  eager_map a n m -> eager_map a n (commit_model flags b k na m).
Proof.
  intros a n flags b k na m HN HL Hnw D HE x Hx. unfold cuts. rewrite commit_model_vmmaps, commit_model_lazy.
  cbn [vm_noaccess commit_vmmaps]. pose proof (lo_hi_range b k) as [R0 R1].
  specialize (HE x Hx). unfold cuts in HE. rewrite zcovb_app in HE. apply orb_false_iff in HE. destruct HE as [E1 E2].
  rewrite !zcovb_app, !zcovb_maps_subtract by assumption. rewrite E1, E2.
  assert (NI : zcovb (lazy_interior b k) x = false).
  { destruct (zcovb (lazy_interior b k) x) eqn:E; [|reflexivity]. pose proof (zcovb_lazy_interior b k x Hnw E). lia. }
  assert (NS : zcovb [(b, k)] x = false).
  { destruct (zcovb [(b, k)] x) eqn:E; [|reflexivity]. pose proof (zcovb_single b k x E). lia. }
  destruct na; [rewrite NS|rewrite zcovb_nil]; (destruct (mmap_noreserve_b flags); [rewrite NI| rewrite zcovb_nil]); reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma eager_map_new : forall flags (b k : word) m,
  mmap_noreserve_b flags = false ->
  (forall x, bv_unsigned b <= x < bv_unsigned b + bv_unsigned k -> zcovb (cuts m) x = false) ->
  eager_map b k (grant_model flags b k false m).
Proof.
  intros flags b k m NR FREE x Hx. unfold cuts. rewrite grant_model_vmmaps, grant_model_lazy, NR.
  cbn [vm_noaccess grant_vmmaps app]. apply FREE. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma cuts_covered_free : forall m (b k : word),
  cuts_covered m -> region_free (vm_maps (m_vmmaps m)) b k = true -> 0 < bv_unsigned k ->
  forall x, bv_unsigned b <= x < bv_unsigned b + bv_unsigned k -> zcovb (cuts m) x = false.
Proof.
  intros m b k CC RF Hk x Hx. destruct (zcovb (cuts m) x) eqn:E; [|reflexivity]. exfalso.
  apply CC in E. apply zcovb_true in E. destruct E as (e & He & Hxe).
  destruct (Z.eq_dec (bv_unsigned (snd e)) 0) as [Z0|NZ]; [unfold lo, hi in Hxe; lia|].
  pose proof (bv_unsigned_in_range 64 (snd e)).
  pose proof (region_free_disjoint _ b k e RF He Hk ltac:(lia)) as D. unfold lo, hi in *. cbn [fst snd] in D. lia.
Qed.

Lemma cuts_covered_free_app : forall m (b k : word),
  cuts_covered m -> region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) b k = true -> 0 < bv_unsigned k ->
  forall x, bv_unsigned b <= x < bv_unsigned b + bv_unsigned k -> zcovb (cuts m) x = false.
Proof.
  intros m b k CC RF Hk. apply cuts_covered_free; [exact CC| | exact Hk]. apply (region_free_app_r _ _ _ _ RF).
Qed.

Theorem eager_map_new_covered : forall flags (b k : word) m,
  cuts_covered m -> mmap_noreserve_b flags = false ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) b k = true -> 0 < bv_unsigned k ->
  eager_map b k (grant_model flags b k false m).
Proof.
  intros flags b k m CC NR RF Hk. apply eager_map_new; [exact NR|]. exact (cuts_covered_free_app m b k CC RF Hk).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cuts_covered_vm : forall m m',
  vm_maps (m_vmmaps m') = vm_maps (m_vmmaps m) -> cuts m' = cuts m -> cuts_covered m -> cuts_covered m'.
Proof. intros m m' H1 H2 CC x Hx. rewrite H1. apply CC. rewrite <- H2. exact Hx. Qed.

Lemma cuts_covered_sbm : forall m m', same_but_materialized m m' -> cuts_covered m -> cuts_covered m'.
Proof.
  intros m m' SB CC. rewrite SB. apply (cuts_covered_vm m); [rewrite m_vmmaps_wvb; reflexivity| | exact CC].
  unfold cuts. rewrite m_vmmaps_wvb, m_vm_lazy_wvb. reflexivity.
Qed.

Lemma cuts_covered_m_vm : forall m m', m_vm m' = m_vm m -> cuts_covered m -> cuts_covered m'.
Proof.
  intros m m' E. destruct m as [fd vm io fs proc lim tm], m' as [fd' vm' io' fs' proc' lim' tm' sg' sc'].
  cbn in E. subst vm'. apply cuts_covered_vm; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cuts_covered_grant : forall flags (b k : word) na m,
  entry_nowrap (b, k) -> cuts_covered m -> cuts_covered (grant_model flags b k na m).
Proof.
  intros flags b k na m Hnw CC x Hx. unfold cuts in Hx. rewrite grant_model_vmmaps, grant_model_lazy in Hx.
  rewrite grant_model_vmmaps. cbn [vm_noaccess vm_maps grant_vmmaps] in *.
  rewrite zcovb_cons. rewrite !zcovb_app in Hx.
  assert (OLD : zcovb (vm_noaccess (m_vmmaps m)) x = true \/ zcovb (m_vm_lazy m) x = true ->
                zin_rangeb x (b, k) || zcovb (vm_maps (m_vmmaps m)) x = true).
  { intros H. rewrite (CC x); [apply orb_true_r|]. unfold cuts. rewrite zcovb_app. apply orb_true_iff. exact H. }
  assert (NEW : bv_unsigned b <= x < bv_unsigned b + bv_unsigned k -> zin_rangeb x (b, k) || zcovb (vm_maps (m_vmmaps m)) x = true).
  { intros H. replace (zin_rangeb x (b, k)) with true; [reflexivity|]. symmetry. apply zin_rangeb_iff. unfold lo, hi. cbn [fst snd]. lia. }
  apply orb_true_iff in Hx. destruct Hx as [Hx|Hx].
  - destruct na; [rewrite zcovb_cons in Hx; apply orb_true_iff in Hx; destruct Hx as [Hx|Hx]|].
    + apply NEW. apply zin_rangeb_iff in Hx. unfold lo, hi in Hx. cbn [fst snd] in Hx. exact Hx.
    + apply OLD. left. exact Hx.
    + apply OLD. left. exact Hx.
  - apply orb_true_iff in Hx. destruct Hx as [Hx|Hx].
    + destruct (mmap_noreserve_b flags); [|discriminate Hx]. apply NEW. exact (zcovb_lazy_interior b k x Hnw Hx).
    + apply OLD. right. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma cuts_covered_commit : forall flags (b k : word) na m,
  entries_nowrap (vm_noaccess (m_vmmaps m)) -> entries_nowrap (m_vm_lazy m) -> entry_nowrap (b, k) ->
  (forall x, bv_unsigned b <= x < bv_unsigned b + bv_unsigned k -> zcovb (vm_maps (m_vmmaps m)) x = true) ->
  cuts_covered m -> cuts_covered (commit_model flags b k na m).
Proof.
  intros flags b k na m HN HL Hnw IN CC x Hx. unfold cuts in Hx. rewrite commit_model_vmmaps, commit_model_lazy in Hx.
  rewrite commit_model_vmmaps. cbn [vm_noaccess vm_maps commit_vmmaps] in *. pose proof (lo_hi_range b k) as [R0 R1].
  rewrite !zcovb_app, !zcovb_maps_subtract in Hx by assumption.
  assert (OLD : zcovb (vm_noaccess (m_vmmaps m)) x = true \/ zcovb (m_vm_lazy m) x = true -> zcovb (vm_maps (m_vmmaps m)) x = true).
  { intros H. apply CC. unfold cuts. rewrite zcovb_app. apply orb_true_iff. exact H. }
  apply orb_true_iff in Hx. destruct Hx as [Hx|Hx]; apply orb_true_iff in Hx; destruct Hx as [Hx|Hx].
  - destruct na; [|discriminate Hx]. apply IN. exact (zcovb_single b k x Hx).
  - apply OLD. left. apply andb_true_iff in Hx. exact (proj1 Hx).
  - destruct (mmap_noreserve_b flags); [|discriminate Hx]. apply IN. exact (zcovb_lazy_interior b k x Hnw Hx).
  - apply OLD. right. apply andb_true_iff in Hx. exact (proj1 Hx).
Qed.

Lemma cuts_covered_commit_contained : forall flags (b k : word) na m,
  entries_nowrap (vm_noaccess (m_vmmaps m)) -> entries_nowrap (m_vm_lazy m) -> entry_nowrap (b, k) ->
  map_contains (vm_maps (m_vmmaps m)) b k = true ->
  cuts_covered m -> cuts_covered (commit_model flags b k na m).
Proof.
  intros flags b k na m HN HL Hnw MC. apply cuts_covered_commit; [exact HN| exact HL| exact Hnw|].
  destruct (map_contains_In _ _ _ MC) as (e & He & L & R). unfold lo, hi in L, R. cbn [fst snd] in L, R.
  intros x Hx. apply zcovb_true. exists e. split; [exact He| unfold lo, hi; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma cuts_covered_munmap : forall (b k : word) m,
  entries_nowrap (vm_noaccess (m_vmmaps m)) -> entries_nowrap (m_vm_lazy m) ->
  nooverlap (vm_maps (m_vmmaps m)) -> In (b, k) (vm_maps (m_vmmaps m)) -> 0 < bv_unsigned k ->
  cuts_covered m -> cuts_covered (munmap_modelL b k m).
Proof.
  intros b k m HN HL NO Hin Hk CC x Hx. unfold cuts in Hx. rewrite munmap_modelL_vmmaps, munmap_modelL_lazy in Hx.
  rewrite munmap_modelL_vmmaps. cbn [vm_noaccess vm_maps munmap_vmmaps] in *. pose proof (lo_hi_range b k) as [R0 R1].
  rewrite zcovb_app, !zcovb_maps_subtract in Hx by assumption.
  assert (CX : zcovb (vm_maps (m_vmmaps m)) x = true /\ ~ (bv_unsigned b <= x < bv_unsigned b + bv_unsigned k)).
  { apply orb_true_iff in Hx. destruct Hx as [Hx|Hx]; apply andb_true_iff in Hx; destruct Hx as [Hx Hr];
      (split; [apply CC; unfold cuts; rewrite zcovb_app; apply orb_true_iff; auto|
               unfold zinb in Hr; intros X; destruct (Z.leb_spec (bv_unsigned b) x); destruct (Z.ltb_spec x (bv_unsigned b + bv_unsigned k)); cbn in Hr; try discriminate Hr; lia]). }
  destruct CX as [CX NR]. apply zcovb_true in CX. destruct CX as (e & He & Hxe).
  apply zcovb_true. exists e. split; [|exact Hxe].
  unfold map_remove. apply filter_In. split; [exact He|]. unfold bv_eqb.
  destruct (Z.eqb_spec (bv_unsigned (fst e)) (bv_unsigned b)) as [E|NE]; [|reflexivity]. exfalso.
  (* [comment removed for export] *)
  assert (SAME : e = (b, k) \/ (hi e <= lo (b, k) \/ hi (b, k) <= lo e)).
  { clear - NO He Hin. induction (vm_maps (m_vmmaps m)) as [|e0 X IH]; [destruct He|].
    destruct NO as [N0 NO]. destruct He as [->|He], Hin as [E0|Hin].
    - left. exact E0.
    - right. exact (N0 _ Hin).
    - right. subst e0. destruct (N0 _ He); [right|left]; assumption.
    - exact (IH NO Hin He). }
  destruct SAME as [->|D]; [apply NR; unfold lo, hi in Hxe; cbn [fst snd] in Hxe; exact Hxe|].
  unfold lo, hi in D, Hxe. cbn [fst snd] in D. rewrite E in Hxe, D. pose proof (bv_unsigned_in_range 64 (snd e)). lia.
Qed.

Lemma cuts_covered_munmap_MInv : forall A AL E (b k : word) m,
  MInv A AL E m -> In (b, k) (vm_maps (m_vmmaps m)) -> 0 < bv_unsigned k ->
  cuts_covered m -> cuts_covered (munmap_modelL b k m).
Proof.
  intros A AL E b k m HI Hin Hk. apply cuts_covered_munmap; [exact (minv_noacc_nw HI)| exact (minv_lazy_nw HI)| exact (minv_nooverlap HI)| exact Hin| exact Hk].
Qed.

(* [comment removed for export] *)
Lemma lazy_free_of_region_free : forall m (b k : word),
  cuts_covered m -> region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) b k = true -> 0 < bv_unsigned k ->
  lazy_free (m_vm_lazy m) (bv_unsigned b) (bv_unsigned b + bv_unsigned k).
Proof.
  intros m b k CC RF Hk x Hx. pose proof (cuts_covered_free_app m b k CC RF Hk x Hx) as H.
  unfold cuts in H. rewrite zcovb_app in H. apply orb_false_iff in H. exact (proj2 H).
Qed.

Lemma lazy_free_new_grant : forall flags (b k : word) na m,
  cuts_covered m -> mmap_noreserve_b flags = false ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) b k = true -> 0 < bv_unsigned k ->
  lazy_free (m_vm_lazy (grant_model flags b k na m)) (bv_unsigned b) (bv_unsigned b + bv_unsigned k).
Proof.
  intros flags b k na m CC NR RF Hk. apply (lazy_free_grant flags b k na m _ _ NR).
  exact (lazy_free_of_region_free m b k CC RF Hk).
Qed.
