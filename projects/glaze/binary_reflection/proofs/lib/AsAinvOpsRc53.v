(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAinvRelease3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvZone3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation u := bv_unsigned.

Lemma page_base_rng : forall a : word, u (page_base a) <= u a < u (page_base a) + 4096 /\ u (page_base a) mod 4096 = 0.
Proof.
  intros a. unfold page_base, page_base_of, page_size. pose proof (u64_range a) as Ha.
  assert (H : 0 <= u a / 4096 * 4096 <= u a) by (Z.div_mod_to_equations; lia).
  rewrite u64_lit by lia. split; [Z.div_mod_to_equations; lia|]. apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ivb_refl : forall iv : Z * Z, (Z.eqb (fst iv) (fst iv) && Z.eqb (snd iv) (snd iv))%bool = true.
Proof. intros [a b]. cbn. rewrite !Z.eqb_refl. reflexivity. Qed.
Lemma ivb_true : forall x iv : Z * Z, (Z.eqb (fst x) (fst iv) && Z.eqb (snd x) (snd iv))%bool = true -> x = iv.
Proof. intros [a b] [c d] H. cbn in H. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity. Qed.


Lemma remove1_iv_in_perm : forall iv A, In iv A -> Permutation A (iv :: remove1_iv iv A).
Proof.
  intros iv A. induction A as [| x r IH]; intros Hin; [destruct Hin|]. cbn [remove1_iv].
  destruct (Z.eqb (fst x) (fst iv) && Z.eqb (snd x) (snd iv))%bool eqn:E.
  - rewrite (ivb_true x iv E). apply Permutation_refl.
  - destruct Hin as [-> | Hin]; [rewrite ivb_refl in E; discriminate E|].
    apply (Permutation_trans (perm_skip x (IH Hin))). apply perm_swap.
Qed.

Lemma remove1_iv_incl : forall iv A, incl (remove1_iv iv A) A.
Proof.
  intros iv A. induction A as [| x r IH]; [intros y Hy; exact Hy|]. cbn [remove1_iv].
  destruct (Z.eqb (fst x) (fst iv) && Z.eqb (snd x) (snd iv))%bool.
  - intros y Hy. right. exact Hy.
  - intros y [-> | Hy]; [left; reflexivity | right; exact (IH y Hy)].
Qed.
Lemma In_remove1_iv_neq : forall x iv A, In x A -> x <> iv -> In x (remove1_iv iv A).
Proof.
  intros x iv A. induction A as [| y r IH]; intros Hin NE; [destruct Hin|]. cbn [remove1_iv].
  destruct (Z.eqb (fst y) (fst iv) && Z.eqb (snd y) (snd iv))%bool eqn:E.
  - destruct Hin as [-> | Hin]; [exfalso; exact (NE (ivb_true x iv E)) | exact Hin].
  - destruct Hin as [-> | Hin]; [left; reflexivity | right; exact (IH Hin NE)].
Qed.
Lemma A_bytes_perm : forall A B, Permutation A B -> A_bytes A = A_bytes B.
Proof. intros A B P. induction P; cbn [A_bytes]; lia. Qed.

Lemma A_bytes_remove1_iv : forall iv A, In iv A -> A_bytes (remove1_iv iv A) = A_bytes A - (snd iv - fst iv).
Proof. intros iv A Hin. rewrite (A_bytes_perm _ _ (remove1_iv_in_perm iv A Hin)). cbn [A_bytes]. lia. Qed.
Lemma A_wf_remove1_iv : forall iv A, A_wf A -> A_wf (remove1_iv iv A).
Proof. intros iv A H. unfold A_wf in *. rewrite Forall_forall in H |- *. intros x Hx. exact (H x (remove1_iv_incl iv A x Hx)). Qed.



(* [comment removed for export] *)
Lemma sh_lo_le_hi : forall mp n, 1 <= n -> sh_lo mp <= sh_hi mp (sec_map_size n).
Proof.
  intros mp n Hn. pose proof (sec_map_size_ge n Hn) as [G _]. pose proof (rz_range n). unfold sh_lo, sh_hi, PG in *.
  apply Zplus_le_compat_l. apply Z.div_le_mono; lia.
Qed.
Lemma pgdn_mono : forall x y, x <= y -> pgdn x <= pgdn y.
Proof. intros x y H. unfold pgdn, PG. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia. Qed.
Lemma pgup_mono : forall x y, x <= y -> pgup x <= pgup y.
Proof. intros x y H. unfold pgup, PG. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia. Qed.
Lemma hull_geom : forall mp n, 1 <= n ->
  sec_hull_lo mp <= sec_inner_lo mp /\ sec_inner_lo mp <= sec_hull_lo mp + PG /\ sec_hull_lo mp <= sh_lo mp /\ sh_lo mp <= sec_inner_lo mp
  /\ sec_inner_hi mp n <= sec_hull_hi mp n /\ sec_hull_hi mp n <= sec_inner_hi mp n + PG
  /\ sec_inner_hi mp n <= sh_hi mp (sec_map_size n) /\ sh_hi mp (sec_map_size n) <= sec_hull_hi mp n
  /\ sec_hull_lo mp mod PG = 0 /\ sec_inner_lo mp mod PG = 0 /\ sec_inner_hi mp n mod PG = 0 /\ sec_hull_hi mp n mod PG = 0
  /\ sec_hull_lo mp <= sec_inner_hi mp n /\ sec_inner_lo mp <= sec_hull_hi mp n.
Proof.
  intros mp n Hn. pose proof (sh_lo_le_hi mp n Hn) as LE. unfold sec_hull_lo, sec_inner_lo, sec_inner_hi, sec_hull_hi.
  pose proof (pgdn_le (sh_lo mp)). pose proof (pgup_ge (sh_lo mp)). pose proof (pgup_pgdn (sh_lo mp)).
  pose proof (pgdn_le (sh_hi mp (sec_map_size n))). pose proof (pgup_ge (sh_hi mp (sec_map_size n))). pose proof (pgup_pgdn (sh_hi mp (sec_map_size n))).
  pose proof (pgdn_mod (sh_lo mp)). pose proof (pgup_mod (sh_lo mp)). pose proof (pgdn_mod (sh_hi mp (sec_map_size n))). pose proof (pgup_mod (sh_hi mp (sec_map_size n))).
  pose proof (pgdn_mono _ _ LE). pose proof (pgup_mono _ _ LE).
  unfold PG in *. repeat split; try assumption; lia.
Qed.

Lemma A_wf_sec_edges : forall mp n, 1 <= n -> A_wf (sec_edges mp n).
Proof.
  intros mp n Hn. pose proof (hull_geom mp n Hn) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & M1 & M2 & M3 & M4 & G9 & G10).
  unfold A_wf, sec_edges. unfold page_size. fold PG.
  constructor; [cbn [fst snd]; repeat split; [exact G1 | exact M1 | exact M2] |].
  constructor; [cbn [fst snd]; repeat split; [exact G5 | exact M3 | exact M4] | constructor].
Qed.
Lemma A_wf_app : forall A B, A_wf A -> A_wf B -> A_wf (A ++ B).
Proof. intros A B HA HB. unfold A_wf in *. apply Forall_app. split; assumption. Qed.
Lemma A_wf_release : forall A mp n, 1 <= n -> A_wf A -> A_wf (release_aa A mp n).
Proof. intros A mp n Hn H. unfold release_aa. apply A_wf_app; [apply A_wf_remove1_iv; exact H | apply A_wf_sec_edges; exact Hn]. Qed.

Lemma A_bytes_release : forall A mp n, In (sec_hull_lo mp, sec_hull_hi mp n) A ->
  A_bytes (release_aa A mp n) = A_bytes A - sec_hull mp n + A_bytes (sec_edges mp n).
Proof.
  intros A mp n Hin. unfold release_aa. rewrite A_bytes_app, (A_bytes_remove1_iv _ _ Hin). cbn [fst snd]. unfold sec_hull. lia.
Qed.
Lemma A_bytes_release_le : forall A mp n, In (sec_hull_lo mp, sec_hull_hi mp n) A ->
  A_bytes (release_aa A mp n) <= A_bytes A - sec_hull mp n + 2 * PG.
Proof. intros A mp n Hin. rewrite (A_bytes_release A mp n Hin). pose proof (sec_edges_bytes mp n). lia. Qed.

Lemma hull_in_release : forall A mp n lo' hi', In (lo', hi') A -> (lo', hi') <> (sec_hull_lo mp, sec_hull_hi mp n) ->
  In (lo', hi') (release_aa A mp n).
Proof. intros A mp n lo' hi' Hin NE. unfold release_aa. apply in_app_iff. left. exact (In_remove1_iv_neq _ _ _ Hin NE). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma page_allowedb_true_iff : forall A p, page_allowedb A p = true <-> exists iv, In iv A /\ fst iv <= u p /\ u p + page_size <= snd iv.
Proof.
  intros A p. unfold page_allowedb. rewrite existsb_exists. split.
  - intros (iv & Hin & Hb). apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. exists iv. repeat split; assumption.
  - intros (iv & Hin & H1 & H2). exists iv. split; [exact Hin|]. apply andb_true_intro. split; apply Z.leb_le; assumption.
Qed.

(* [comment removed for export] *)
Lemma edge_page : forall mp n p, 1 <= n -> p mod PG = 0 ->
  sec_hull_lo mp <= p -> p + PG <= sec_hull_hi mp n -> ~ (sec_inner_lo mp <= p < sec_inner_hi mp n) ->
  page_allowedb (sec_edges mp n) (Z_to_bv 64 p) = true \/ ~ (0 <= p < 2 ^ 64).
Proof.
  intros mp n p Hn AL H1 H2 NI. destruct (Z_lt_le_dec p 0) as [NEG|POS]; [right; lia|].
  destruct (Z_lt_le_dec p (2 ^ 64)) as [LT|GE]; [| right; lia]. left.
  pose proof (hull_geom mp n Hn) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & M1 & M2 & M3 & M4 & G9 & G10).
  apply page_allowedb_true_iff. rewrite u64_lit by lia. unfold page_size. fold PG. unfold sec_edges.
  destruct (Z_lt_le_dec p (sec_inner_lo mp)) as [LO | HI].
  - exists (sec_hull_lo mp, sec_inner_lo mp). split; [left; reflexivity|]. cbn [fst snd].
    unfold PG in *. Z.div_mod_to_equations. nia.
  - assert (HI' : sec_inner_hi mp n <= p) by lia.
    exists (sec_inner_hi mp n, sec_hull_hi mp n). split; [right; left; reflexivity|]. cbn [fst snd].
    unfold PG in *. Z.div_mod_to_equations. nia.
Qed.

Lemma page_allowedb_release : forall A mp n (p : word), 1 <= n ->
  page_allowedb A p = true -> u p mod PG = 0 -> ~ (sec_inner_lo mp <= u p < sec_inner_hi mp n) ->
  page_allowedb (release_aa A mp n) p = true.
Proof.
  intros A mp n p Hn AP AL NI. pose proof (u64_range p) as Rp.
  apply page_allowedb_true_iff in AP as (iv & Hin & H1 & H2). unfold release_aa.
  destruct (decide (iv = (sec_hull_lo mp, sec_hull_hi mp n))) as [-> | NE].
  - cbn [fst snd] in H1, H2. apply page_allowedb_app_r. unfold page_size in H2. fold PG in H2.
    destruct (edge_page mp n (u p) Hn AL H1 H2 NI) as [E | X]; [| exfalso; exact (X Rp)].
    rewrite Z_to_bv_bv_unsigned in E. exact E.
  - apply page_allowedb_app_l. apply page_allowedb_true_iff. exists iv. split; [exact (In_remove1_iv_neq _ _ _ Hin NE) | exact (conj H1 H2)].
Qed.


(* [comment removed for export] *)
Lemma range_allowed_release : forall A mp n lo hi, 1 <= n -> 0 <= lo -> hi <= 2 ^ 64 ->
  range_allowed A lo hi ->
  (hi <= sec_inner_lo mp \/ sec_inner_hi mp n <= lo) ->
  range_allowed (release_aa A mp n) lo hi.
Proof.
  intros A mp n lo hi Hn Hlo Hhi RA OFF a Ha. pose proof (hull_geom mp n Hn) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & M1 & M2 & M3 & M4 & G9 & G10).
  pose proof (page_base_rng (Z_to_bv 64 a)) as ((P1 & P2) & P3). rewrite (u64_lit a) in P1, P2 by lia.
  apply (page_allowedb_release A mp n _ Hn (RA a Ha)); [unfold PG; exact P3|].
  (* [comment removed for export] *)
  intros [I1 I2]. unfold PG in *. destruct OFF as [O | O]; Z.div_mod_to_equations; nia.
Qed.

(* [comment removed for export] *)
Lemma inner_nonempty : forall mp n, 64513 <= n -> sec_inner_lo mp + PG <= sec_inner_hi mp n.
Proof.
  intros mp n Hn. pose proof (sec_map_size_ge n ltac:(lia)) as [G _]. pose proof (rz_range n).
  unfold sec_inner_lo, sec_inner_hi, pgup, pgdn, sh_lo, sh_hi, PG in *. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem MInv_release : forall A mp n mdl, 64513 <= n ->
  A_wf A -> In (sec_hull_lo mp, sec_hull_hi mp n) A -> MInv A mdl ->
  (forall p, In p (m_vm_materialized mdl) -> ~ (sec_inner_lo mp <= u p < sec_inner_hi mp n)) ->
  MInv (release_aa A mp n) mdl.
Proof.
  intros A mp n mdl Hn AW HA [N1 N2 N3 N4 N5] CLR. assert (Hn1 : 1 <= n) by lia. constructor.
  - exact N1.
  - exact N2.
  - intros p Hp. apply (page_allowedb_release A mp n p Hn1 (N3 p Hp)); [unfold PG; exact (N2 p Hp) | exact (CLR p Hp)].
  - exact N4.
  - pose proof (inner_nonempty mp n Hn). rewrite (A_bytes_release A mp n HA).
    pose proof (hull_geom mp n Hn1) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & M1 & M2 & M3 & M4 & G9 & G10).
    unfold sec_hull. cbn [A_bytes sec_edges fst snd]. unfold PG in *. lia.
Qed.


(* [comment removed for export] *)
Lemma madvise_next_mat : forall m (a n : word),
  m_vm_materialized (madvise_dontneed_next m a n) = List.filter (page_outside_range (u a) (u a + u n)) (m_vm_materialized m).
Proof. intros [fd [maps lazy mat] io fs proc lim tm] a n. reflexivity. Qed.
Lemma madvise_next_clear : forall m (a n p : word),
  In p (m_vm_materialized (madvise_dontneed_next m a n)) -> ~ (u a <= u p < u a + u n).
Proof.
  intros m a n p Hp [H1 H2]. rewrite madvise_next_mat in Hp. apply filter_In in Hp as [_ Hout].
  unfold page_outside_range in Hout. apply Bool.negb_true_iff in Hout. apply andb_false_iff in Hout as [X|X]; [apply Z.leb_gt in X | apply Z.ltb_ge in X]; lia.
Qed.

Lemma madvise_next_sbm : forall m (a n : word), same_but_materialized m (madvise_dontneed_next m a n).
Proof. intros m a n. unfold madvise_dontneed_next. apply with_vm_backing_same. Qed.
Lemma MInv_madvise_next : forall A m (a n : word), MInv A m -> MInv A (madvise_dontneed_next m a n).
Proof.
  intros A m a n [N1 N2 N3 N4 N5].
  pose proof (same_but_materialized_frame _ _ (madvise_next_sbm m a n)) as (_ & EV & EL & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EE).
  constructor; rewrite ?madvise_next_mat, ?EL, ?EV, ?EE.
  - apply NoDup_filter. exact N1.
  - intros p Hp. apply filter_In in Hp as [Hp _]. exact (N2 p Hp).
  - intros p Hp. apply filter_In in Hp as [Hp _]. exact (N3 p Hp).
  - intros p Hp. apply filter_In in Hp as [Hp _]. exact (N4 p Hp).
  - exact N5.
Qed.
(* [comment removed for export] *)
Theorem MInv_release_madvise : forall A mp n m (a len : word), 64513 <= n ->
  A_wf A -> In (sec_hull_lo mp, sec_hull_hi mp n) A -> MInv A m ->
  u a = sec_inner_lo mp -> u a + u len = sec_inner_hi mp n ->
  MInv (release_aa A mp n) (madvise_dontneed_next m a len).
Proof.
  intros A mp n m a len Hn AW HA MI Ea Elen. apply (MInv_release A mp n _ Hn AW HA (MInv_madvise_next A m a len MI)).
  intros p Hp. rewrite <- Ea, <- Elen. exact (madvise_next_clear m a len p Hp).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma shadow_apart : forall mp msz a n, mp mod 8 = 0 -> (mp + msz) mod 8 = 0 ->
  (a + n <= mp \/ mp + msz <= a) -> sh_hi a n <= sh_lo mp \/ sh_hi mp msz <= sh_lo a.
Proof. intros mp msz a n M1 M2 D. unfold sh_lo, sh_hi. Z.div_mod_to_equations. lia. Qed.
(* [comment removed for export] *)
Lemma inner_apart : forall mp nn a n, 1 <= nn -> mp mod PG = 0 ->
  (a + n <= mp \/ mp + sec_map_size nn <= a) -> sh_hi a n <= sec_inner_lo mp \/ sec_inner_hi mp nn <= sh_lo a.
Proof.
  intros mp nn a n Hn AL D. pose proof (hull_geom mp nn Hn) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
  pose proof (sec_map_size_ge nn Hn) as [_ SM].
  assert (M1 : mp mod 8 = 0) by (clear -AL; unfold PG in AL; Z.div_mod_to_equations; lia).
  assert (M2 : (mp + sec_map_size nn) mod 8 = 0) by (clear -AL SM; unfold PG in *; Z.div_mod_to_equations; lia).
  destruct (shadow_apart mp (sec_map_size nn) a n M1 M2 D); lia.
Qed.
(* [comment removed for export] *)
Lemma secsum2_perm : forall l l', Permutation l l' ->
  fold_right (fun s acc => sc_mapsz s + sec_hull (sc_map s) (sc_n s) + acc) 0 l = fold_right (fun s acc => sc_mapsz s + sec_hull (sc_map s) (sc_n s) + acc) 0 l'.
Proof. intros l l' P. induction P; cbn [fold_right]; lia. Qed.
Section SecFree.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation IA := (bt_ia bt).

  (* [comment removed for export] *)
  Lemma rep_ledger_release : forall st mdl mp n, rep_ledger bt st mdl -> rep_ledger bt (op_sec_release st mp n) mdl.
  Proof. intros st mdl mp n H. exact H. Qed.

  Theorem rep_budget_sec_free : forall st st' Lc Lc' FF mdl mdl' s (qt qg : Z),
    WFq bt st Lc FF qt qg -> rep_budget bt st Lc mdl -> In s (a_sec st) ->
    (forall p n, In (p, n) Lc' -> In (p, n) Lc /\ (p, n) <> (sc_user s, sc_n s)) ->
    a_reg st' = a_reg st -> a_dep st' = a_dep st -> a_nres st' = a_nres st ->
    a_aa st' = release_aa (a_aa st) (sc_map s) (sc_n s) -> a_shsec st' = a_shsec st + 2 * PG ->
    Permutation (a_sec st) (s :: a_sec st') ->
    MInv (a_aa st') mdl' -> eager_used mdl' + sc_mapsz s <= eager_used mdl ->
    rep_budget bt st' Lc' mdl'.
  Proof.
    intros st st' Lc Lc' FF mdl mdl' s qt qg W (BU1 & BU2 & BU3 & BU4 & BU5 & BU6 & BU7 & BU8 & BU9) Hs HLc EREG EDEP ENRES EAA ESH PERM MI EAG.
    pose proof ceil_rng as CR. pose proof ceil_pg as CP.
    pose proof W as (_ & _ & _ & (_ & _ & _ & _ & NDM & _) & _ & _ & _ & _ & (RNG & _ & _ & _ & _ & _ & _ & _ & _ & INS & _) & _).
    destruct (sec_facts bt st Lc FF W s Hs) as (SA1 & SA2 & SA3 & SA4 & SA5 & SA6 & SA7 & SA8).
    assert (Hn1 : 1 <= sc_n s) by (clear -SA7; lia). unfold sc_mapsz in SA2, SA4, SA6, EAG.
    assert (M8a : sc_map s mod 8 = 0) by (clear -SA3; unfold PG in SA3; Z.div_mod_to_equations; lia).
    assert (M8b : (sc_map s + sec_map_size (sc_n s)) mod 8 = 0) by (clear -SA3 SA4; unfold PG in *; Z.div_mod_to_equations; lia).
    pose proof (hull_geom (sc_map s) (sc_n s) Hn1) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
    pose proof (img_lits bt st Lc FF W) as [I1 I2]. pose proof (band_facts bt st Lc FF W) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    pose proof (fixed_facts bt st Lc FF W) as (_ & _ & _ & _ & F1 & F2 & F3 & _).
    destruct (RNG _ _ (all_ranges_dyn bt st _ (sec_dyn st s Hs))) as ((D1 & D2 & D3 & D4 & D5) & _).
    (* [comment removed for export] *)
    assert (NDS : List.NoDup (s :: a_sec st')) by exact (Permutation_NoDup PERM (NoDup_map_inv _ _ NDM)).
    assert (INS' : forall x, In x (a_sec st') -> In x (a_sec st) /\ x <> s).
    { intros x Hx. split; [exact (Permutation_in x (Permutation_sym PERM) (or_intror Hx))|]. intros ->. inversion NDS as [| ? ? NI _]; subst. exact (NI Hx). }
    (* [comment removed for export] *)
    assert (XFER : forall lo hi, 0 <= lo -> hi <= 2 ^ 64 -> range_allowed (a_aa st) lo hi ->
                   (hi <= sec_inner_lo (sc_map s) \/ sec_inner_hi (sc_map s) (sc_n s) <= lo) -> range_allowed (a_aa st') lo hi).
    { intros lo hi Hlo Hhi RA OFF. rewrite EAA. exact (range_allowed_release _ _ _ lo hi Hn1 Hlo Hhi RA OFF). }
    unfold rep_budget. rewrite EAA at 1. rewrite EREG, EDEP, ENRES, ESH.
    split. { apply A_wf_release; [exact Hn1 | exact BU1]. }
    split. { exact MI. }
    split. { (* [comment removed for export] *) intros lo hi Hin. pose proof (BU3 lo hi Hin) as RA. unfold SHC in Hin.
             destruct Hin as [E | [E | [E | []]]]; injection E as <- <-.
             - apply XFER; [unfold sh_lo, SB; clear -CR; lia | unfold SB; clear; lia | exact RA |].
               right. clear -G7 SA2 CP. unfold sh_lo, sh_hi, sc_mapsz in *. Z.div_mod_to_equations. lia.
             - apply XFER; [unfold sh_lo, SB; clear -I1; lia | unfold sh_hi, SB, AS_LO in *; clear -I1 I2; Z.div_mod_to_equations; lia | exact RA |].
               apply (inner_apart (sc_map s) (sc_n s)); [exact Hn1 | exact SA3 |]. unfold sc_mapsz in D4. clear -D4 I1. lia.
             - apply XFER; [unfold sh_lo, SB; clear -F1; lia | unfold sh_hi, SB, FAKE_SIZE in *; clear -F1 F2 CR; Z.div_mod_to_equations; lia | exact RA |].
               apply (inner_apart (sc_map s) (sc_n s)); [exact Hn1 | exact SA3 |].
               destruct (fs_vs_dyn bt st Lc FF W _ _ (sec_dyn st s Hs)) as [X|X]; unfold sc_mapsz in X; clear -X; lia. }
    split. { (* [comment removed for export] *) intros p n Hin. destruct (HLc p n Hin) as [HinL NE]. pose proof (BU4 p n HinL) as RA.
             destruct (live_range bt st Lc FF W p n HinL) as (L1 & L2 & L3 & L4).
             apply XFER; [unfold sh_lo, SB, PTRLO in *; clear -L1; lia | unfold sh_hi, SB, PTRLO, NMAX in *; clear -L1 L2 L3 CR; Z.div_mod_to_equations; lia | exact RA |].
             apply (inner_apart (sc_map s) (sc_n s)); [exact Hn1 | exact SA3 |]. unfold sc_mapsz.
             destruct (is_primary n) eqn:HP.
             - pose proof (live_chunk bt st Lc FF W p n HinL HP) as (C1 & C2 & _ & C4 & C5 & C6). cbn zeta in C2, C4, C5.
               destruct (carved_range bt st Lc FF W _ _ C1 C2) as (_ & _ & R3 & R4 & _).
               destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st s Hs)) as [X|X]; unfold sc_mapsz in X; clear -X R3 R4 C4 C5 C6; unfold PG, KSPACE in *; lia.
             - destruct (live_sec bt st Lc FF W p n HinL HP) as (sc & Hsc & Eu & En).
               assert (NEs : sc <> s) by (intros ->; apply NE; rewrite Eu, En; reflexivity).
               destruct (sec_facts bt st Lc FF W sc Hsc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
               destruct (sec_cases bt st Lc FF W sc s Hsc Hs) as [E | X]; [exact (False_ind _ (NEs E))|].
               unfold sc_mapsz in X, Q6. rewrite <- Eu, <- En. clear -X Q5 Q6. unfold PG in *. lia. }
    split. { (* [comment removed for export] *) intros c Hc. destruct (BU5 c Hc) as [RA1 RA2].
             pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14).
             destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st s Hs)) as [X|X]; unfold sc_mapsz in X.
             - split.
               + apply XFER; [unfold sh_lo, SB; clear -R1 B5; lia | unfold sh_lo, SB, KSPACE, PG in *; clear -R1 R2 R5 B4 CR R8; Z.div_mod_to_equations; lia | exact RA1 |].
                 right. clear -X R1 G7 M8b. unfold sh_lo, sh_hi in *. Z.div_mod_to_equations. lia.
               + apply XFER; [unfold sh_lo, SB; clear -R1 R2 R8 B5; lia | unfold sh_lo, SB, KSPACE, PG in *; clear -R1 R2 R5 R6 B4 CR R8; Z.div_mod_to_equations; lia | exact RA2 |].
                 right. clear -X R1 R2 R8 G7 M8b. unfold sh_lo, sh_hi in *. Z.div_mod_to_equations. lia.
             - split.
               + apply XFER; [unfold sh_lo, SB; clear -R1 B5; lia | unfold sh_lo, SB, KSPACE, PG in *; clear -R1 R2 R5 B4 CR R8; Z.div_mod_to_equations; lia | exact RA1 |].
                 left. clear -X R1 R2 R5 R6 R8 G4 R11 R13. unfold sh_lo, KSPACE, PG in *. Z.div_mod_to_equations. lia.
               + apply XFER; [unfold sh_lo, SB; clear -R1 R2 R8 B5; lia | unfold sh_lo, SB, KSPACE, PG in *; clear -R1 R2 R5 R6 B4 CR R8; Z.div_mod_to_equations; lia | exact RA2 |].
                 left. clear -X R1 R2 R5 R6 R8 G4 R12 R14. unfold sh_lo, KSPACE, PG in *. Z.div_mod_to_equations. lia. }
    split. { (* [comment removed for export] *) intros s' Hs'. destruct (INS' s' Hs') as [Hs0 NEs]. pose proof (BU6 s' Hs0) as RA.
             destruct (sec_facts bt st Lc FF W s' Hs0) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
             apply XFER; [unfold sh_lo, SB; clear -Q1; lia | unfold sh_hi, SB in *; clear -Q1 Q2 CR; Z.div_mod_to_equations; lia | exact RA |].
             apply (inner_apart (sc_map s) (sc_n s)); [exact Hn1 | exact SA3 |]. unfold sc_mapsz.
             destruct (sec_cases bt st Lc FF W s' s Hs0 Hs) as [E | X]; [exact (False_ind _ (NEs E)) | unfold sc_mapsz in X; clear -X; lia]. }
    split. { (* [comment removed for export] *) intros b Hb. pose proof (BU7 b Hb) as RA.
             destruct (store_blocks_range bt st Lc FF W b Hb) as (S1 & S2 & S3).
             assert (OFFB : b + 2 ^ 23 <= AS_LO \/ AS_HEAPLO <= b).
             { destruct Hb as [<- | Hb].
               - destruct (RNG _ _ (all_ranges_fixed bt st _ INS)) as ((_ & _ & _ & _ & X) & _). exact X.
               - destruct (RNG _ _ (all_ranges_dyn bt st _ (store_dyn st b Hb))) as ((_ & _ & _ & _ & X) & _). exact X. }
             apply XFER; [clear -S1; lia | clear -S2 CR; lia | exact RA |].
             clear -OFFB G4 G7 SA1 SA2 B6. unfold sh_lo, sh_hi, sc_mapsz, AS_LO, AS_HEAPLO, SB in *. Z.div_mod_to_equations. lia. }
    split. { (* [comment removed for export] *)
             pose proof (BU9 s Hs) as HIN. rewrite EAA.
             pose proof (A_bytes_release_le (a_aa st) (sc_map s) (sc_n s) HIN) as AB.
             assert (SC : sec_charge st = sc_mapsz s + sec_hull (sc_map s) (sc_n s) + sec_charge st').
             { unfold sec_charge. rewrite (secsum2_perm _ _ PERM). reflexivity. }
             assert (PC : prim_charge st' = prim_charge st) by (unfold prim_charge; rewrite EREG; reflexivity).
             assert (DC : depot_charge st' = depot_charge st) by (unfold depot_charge; rewrite EDEP; reflexivity).
             rewrite PC, DC. clear -BU8 AB SC EAG. unfold sc_mapsz in *. lia. }
    (* [comment removed for export] *)
    intros s' Hs'. destruct (INS' s' Hs') as [Hs0 NEs]. rewrite EAA. apply hull_in_release; [exact (BU9 s' Hs0)|].
    destruct (sec_facts bt st Lc FF W s' Hs0) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
    destruct (sec_cases bt st Lc FF W s' s Hs0 Hs) as [E | X]; [exact (False_ind _ (NEs E))|]. unfold sc_mapsz in X.
    intros E. injection E as E1 E2.
    (* [comment removed for export] *)
    pose proof (sec_map_size_ge (sc_n s) Hn1) as [Z1 _]. pose proof (sec_map_size_ge (sc_n s') ltac:(clear -Q7; lia)) as [Z2 _].
    pose proof (rz_range (sc_n s)). pose proof (rz_range (sc_n s')).
    clear -X E1 Z1 Z2 H H0 SA7 Q7. unfold sec_hull_lo, pgdn, sh_lo, PG in *. Z.div_mod_to_equations. lia.
  Qed.
End SecFree.
End AsAinvRelease3.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrameE3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.AsAinvOpsQ3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvZone3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsD3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrameE3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc23 AsAinvRelease3.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac lia ::= am_lia.
#[local] Notation u := bv_unsigned.

(* [comment removed for export] *)
Lemma nth_error_swap_remove : forall {A} (l : list A) i j s x, nth_error l i = Some s -> nth_error (swap_remove l i) j = Some x ->
  (j < length l - 1)%nat /\ ((j = i /\ nth_error l (length l - 1) = Some x) \/ (j <> i /\ nth_error l j = Some x)).
Proof.
  intros A l i j s x Hi Hj. unfold swap_remove in Hj. destruct (rev l) as [|lst r'] eqn:ER.
  - assert (l = []) by (rewrite <- (rev_involutive l), ER; reflexivity). subst l. destruct i; discriminate Hi.
  - assert (EL : l = rev r' ++ [lst]) by (rewrite <- (rev_involutive l), ER; reflexivity).
    set (l' := rev r') in *. assert (LL : length l = S (length l')) by (rewrite EL, length_app; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia).
    assert (LAST : nth_error l (length l - 1) = Some lst).
    { replace (length l - 1)%nat with (length l') by lia. rewrite EL, nth_error_app2, Nat.sub_diag by lia. reflexivity. }
    destruct (Nat.ltb_spec i (length l')) as [LT | GE].
    + assert (LF : length (firstn i l') = i) by (rewrite length_firstn; lia).
      destruct (Nat.lt_ge_cases j i) as [J1 | J1].
      * rewrite nth_error_app1 in Hj by lia. rewrite nth_error_firstn in Hj. destruct (Nat.ltb_spec j i); [| lia].
        split; [lia|]. right. split; [lia|]. rewrite EL, nth_error_app1 by lia. exact Hj.
      * rewrite nth_error_app2 in Hj by lia. rewrite LF in Hj. destruct (j - i)%nat as [|d] eqn:ED.
        -- cbn in Hj. injection Hj as <-. assert (j = i) by lia. subst j. split; [lia|]. left. split; [reflexivity | exact LAST].
        -- cbn [app nth_error] in Hj. rewrite nth_error_skipn in Hj. assert (EJ : (S i + d)%nat = j) by lia. rewrite EJ in Hj.
           pose proof (nth_error_lt _ _ _ Hj) as Hl. split; [lia|]. right. split; [lia|]. rewrite EL, nth_error_app1 by lia. exact Hj.
    + pose proof (nth_error_lt _ _ _ Hj) as Hl. split; [lia|]. right. split; [| rewrite EL, nth_error_app1 by lia; exact Hj].
      pose proof (nth_error_lt _ _ _ Hi) as Hil. lia.
Qed.
Lemma swap_remove_length : forall {A} (l : list A) i s, nth_error l i = Some s -> Z.of_nat (length (swap_remove l i)) = Z.of_nat (length l) - 1.
Proof. intros A l i s H. pose proof (Permutation_length (swap_remove_perm l i s H)) as PL. cbn [length] in PL. lia. Qed.



Section RC5.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation IA := (bt_ia bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.
  Ltac uilia := unfold DEPOT_NIDS, DEPOT_MAP1 in *; unfold IB, DEPOT_TAB, SSOBJ, IA_FLAG, IA_INST, IASZ in *; ulia.
  Ltac dsj := repeat match goal with H : _ \/ _ |- _ => destruct H end.
  Ltac Zlia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, T_PC, PC_SZ, T_QC, T_UNW, NMAX in *; unfold boxed in *; dsj; Z.div_mod_to_equations; lia.

  (* [comment removed for export] *)
  Definition idx_lo (st : ast) : Z := match nth_error (a_sec st) (length (a_sec st) - 1) with Some sl => sc_map sl + 24 | None => 0 end.
  Definition idx_hi (st : ast) : Z := match nth_error (a_sec st) (length (a_sec st) - 1) with Some sl => sc_map sl + 32 | None => 0 end.

  Definition foot_secfree (st : ast) (i : nat) (s : schunk) (z : Z) : Prop :=
    qhdr bt z \/ gq_objs st z
    \/ (IB bt + 120 <= z < IB bt + 728)
    \/ (bt_ptrarr bt + 8 * Z.of_nat i <= z < bt_ptrarr bt + 8 * Z.of_nat i + 8)
    \/ (idx_lo st <= z < idx_hi st)
    \/ (sh_lo (sc_map s) <= z < sh_hi (sc_map s) (sc_mapsz s))
    \/ (T + 2768 <= z < T + 3168) \/ CEIL <= z.

  Definition OPS_REP_secfree : Prop := forall st Lc FF (M M' : mem) mdl mdl' gq' m n i s (qt qg : Z),
    WFq bt st Lc FF qt qg -> Rep bt st Lc FF M mdl ->
    (forall x, In x (flat_map ba_items gq') <-> In x (flat_map ba_items (a_gq st)) /\ x <> (m, n)) ->
    In (m, n) (flat_map ba_items (a_gq st)) -> is_primary n = false ->
    nth_error (a_sec st) i = Some s -> sc_user s = m + 16 ->
    let len := Z.of_nat (length (a_sec st)) in
    agrees_off (foot_secfree st i s) M M' ->
    rep_list bt M' (IB bt + 888) gq' -> rep_batches bt M' gq' ->
    cellZ SG M' (IB bt + 120) 8 (len - 1) -> byteZ SG M' (IB bt + 680) 0 ->
    (forall sl, Z.of_nat i < len - 1 -> nth_error (a_sec st) (length (a_sec st) - 1) = Some sl ->
        cellZ SG M' (bt_ptrarr bt + 8 * Z.of_nat i) 8 (sc_map sl) /\ cellZ SG M' (sc_map sl + 24) 8 (Z.of_nat i)) ->
    (* [comment removed for export] *)
    Permutation ((Z_to_bv 64 (sc_map s), Z_to_bv 64 (sc_mapsz s)) :: vm_maps (m_vmmaps mdl')) (vm_maps (m_vmmaps mdl)) ->
    (forall a, in_ivz (vm_noaccess (m_vmmaps mdl')) a <-> in_ivz (vm_noaccess (m_vmmaps mdl)) a) ->
    Forall (fun e : word * word => 0 < bv_unsigned (snd e)) (vm_noaccess (m_vmmaps mdl')) ->
    (forall a, pg_in_ivz (m_vm_lazy mdl') a <-> pg_in_ivz (m_vm_lazy mdl) a) ->
    Forall (fun iv : word * word => bv_unsigned (fst iv) mod PG = 0 /\ bv_unsigned (snd iv) mod PG = 0
                                   /\ 0 < bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= CEIL
                                   /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= ia_img_lo (bt_ia bt) \/ ia_img_hi (bt_ia bt) <= bv_unsigned (fst iv)))
           (m_vm_lazy mdl') ->
    vm_reserved (m_vmmaps mdl') = vm_reserved (m_vmmaps mdl) -> vm_brk (m_vmmaps mdl') = vm_brk (m_vmmaps mdl) ->
    vm_start_brk (m_vmmaps mdl') = vm_start_brk (m_vmmaps mdl) -> vm_mmap_base (m_vmmaps mdl') = vm_mmap_base (m_vmmaps mdl) ->
    vm_init_sp (m_vmmaps mdl') = vm_init_sp (m_vmmaps mdl) ->
    vm_limit (m_vmmaps mdl') = vm_limit (m_vmmaps mdl) ->
    (* [comment removed for export] *)
    MInv (release_aa (a_aa st) (sc_map s) (sc_n s)) mdl' -> eager_used mdl' + sc_mapsz s <= eager_used mdl ->
    Rep bt (op_sec_free (set_gq st gq') i) Lc FF M' mdl'.

  Lemma PIN5dec : forall st i s, Xdec (fun z => qhdr bt z \/ gq_objs st z \/ (IB bt + 120 <= z < IB bt + 128) \/ (IB bt + 680 <= z < IB bt + 681)
      \/ (bt_ptrarr bt + 8 * Z.of_nat i <= z < bt_ptrarr bt + 8 * Z.of_nat i + 8) \/ (idx_lo st <= z < idx_hi st)
      \/ (sh_lo (sc_map s) <= z < sh_hi (sc_map s) (sc_mapsz s))).
  Proof using.
    intros st i s. apply Xdec_or; [apply Xdec_iv|]. apply Xdec_or; [| repeat (apply Xdec_or; [apply Xdec_iv|]); apply Xdec_iv].
    (lazymatch goal with |- ?G => let G' := eval unfold gq_objs in G in change_no_check G' end). apply (Xdec_ex_list (a_gq st) (fun b z => ba_addr b <= z < ba_addr b + BATCHSZ)). intros b. apply Xdec_iv.
  Qed.

  Theorem OPS_REP_secfree_pf : OPS_REP_secfree.
  Proof using.
    intros st Lc FF M M' mdl mdl' gq' m n i s qt qg W R QREL RMIN HPn Hnth Hus. cbn zeta.
    intros AGR NLIST NBAT CNCH CMTX CMOVE PM NA NP' LZ FL' E1 E2 E3 E4 E6 E5 MI EAG.
    set (len := Z.of_nat (length (a_sec st))) in *.
    (* [comment removed for export] *)
    pose proof W as ((WR1 & WR2) & WC & (WQ1 & WQ2 & WQ3 & WQ4 & WQ5 & WQ6) & (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8) & (LV1 & LV2 & LV3) & WK & WD & WM' & (RNG & PW' & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _) & G).
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    pose proof (image_facts bt st Lc FF W) as IMF. cbn zeta in IMF.
    destruct IMF as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z14 & Z15 & Z16 & YC).
    destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & SP4 & SP5) & SP6 & SP7 & SP8 & SPH). assert (SBH : AS_HEAPLO <= SBEG) by (clear -SP7 SPH; lia). box SP4. box SP5.
    pose proof (img_lits bt st Lc FF W) as [I1 I2]. pose proof (band_facts bt st Lc FF W) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    pose proof (thread_page_facts bt st Lc FF W) as (_ & _ & _ & _ & TPI & TPB).
    assert (TPG : T + PG <= SBEG \/ SBEG + KSPACE + PG <= T) by (apply (space_vs_fixed bt st Lc FF W _ _ INT); ulia).
    pose proof (img_pw bt st Lc FF W) as IPW. unfold img_ranges in IPW. cbn [PW seps fst snd] in IPW.
    destruct IPW as ((J1 & J2 & J3 & J4 & J5 & J6 & J7 & _) & _). box J1. box J2. box J3. box J4. box J5. box J6. box J7. box TPI. box TPB. box TPG.
    pose proof (bt_ok_W bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DC & DT & DR & _).
    assert (HC24 : 1 <= BATCHCLASS <= 30) by ((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia).
    (* [comment removed for export] *)
    assert (Hs : In s (a_sec st)) by exact (nth_error_In _ _ Hnth).
    assert (Hq : In (m, n) (quar st)) by ((lazymatch goal with |- ?G => let G' := eval unfold quar in G in change_no_check G' end); rewrite flat_map_app; apply in_app_iff; right; exact RMIN).
    assert (Hsn : sc_n s = n).
    { destruct (quar_sec bt st Lc FF W m n Hq HPn) as (sc & Hsc & Eu & En). rewrite <- (sec_user_inj bt st Lc FF sc s W Hsc Hs ltac:(lia)). exact En. }
    destruct (sec_facts bt st Lc FF W s Hs) as (SA1 & SA2 & SA3 & SA4 & SA5 & SA6 & SA7 & SA8).
    pose proof (nth_error_lt _ _ _ Hnth) as Hil.
    set (SR := swap_remove (a_sec st) i).
    pose proof (swap_remove_perm (a_sec st) i s Hnth) as PERM. fold SR in PERM.
    assert (NDS0 : List.NoDup (a_sec st)) by exact (NoDup_map_inv _ _ S5).
    assert (NDS : List.NoDup (s :: SR)) by exact (Permutation_NoDup (Permutation_sym PERM) NDS0).
    assert (INSR : forall x, In x SR <-> In x (a_sec st) /\ x <> s).
    { intros x. split.
      - intros Hx. split; [exact (Permutation_in x PERM (or_intror Hx))|]. intros ->. inversion NDS as [| ? ? NI _]; subst. exact (NI Hx).
      - intros [Hx NE]. destruct (Permutation_in x (Permutation_sym PERM) Hx) as [E | Hx']; [exfalso; exact (NE (eq_sym E)) | exact Hx']. }
    set (st' := op_sec_free (set_gq st gq') i).
    assert (ESEN : sec_entry (set_gq st gq') i = s) by ((lazymatch goal with |- ?G => let G' := eval unfold sec_entry in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_sec set_gq] in G in change_no_check G' end); exact (nth_error_nth _ _ _ Hnth)).
    assert (QSUB : forall x, In x (quar st') <-> In x (quar st) /\ x <> (m, n)).
    { intros x. (lazymatch goal with |- ?G => let G' := eval unfold quar, st' in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_tq a_gq op_sec_free set_gq] in G in change_no_check G' end). rewrite !flat_map_app, !in_app_iff, (QREL x). split.
      - intros [X | [X Y]]; [| am_tauto]. split; [left; exact X|]. intros ->.
        unfold quar in WQ6. rewrite flat_map_app, map_app in WQ6.
        destruct (in_split _ _ X) as (l1 & l2 & EX). rewrite EX, map_app in WQ6. cbn [map fst] in WQ6. rewrite <- app_assoc in WQ6. cbn [app] in WQ6.
        apply (NoDup_remove_2 _ _ _ WQ6). apply in_app_iff. right. apply in_app_iff. right. apply (in_map fst _ _ RMIN).
      - am_tauto. }
    (* [comment removed for export] *)
    assert (GQfacts : forall z, gq_objs st z -> exists b, In b (a_tq st ++ a_gq st) /\ In b (a_gq st) /\ carved bt st BATCHCLASS (ba_addr b)
                        /\ SBEG <= ba_addr b /\ ba_addr b + BATCHSZ <= SBEG + KSPACE /\ ba_addr b <= z < ba_addr b + BATCHSZ).
    { intros z (b & Hb & Hz). assert (Hb2 : In b (a_tq st ++ a_gq st)) by (apply in_app_iff; right; exact Hb).
      destruct (batch_facts bt st Lc FF W b Hb2) as (CVb & _ & Bl1 & Bl2). exists b. repeat (split; [assumption|]). exact Hz. }
    assert (GQspace : forall z, gq_objs st z -> SBEG <= z < SBEG + KSPACE).
    { intros z Gz. destruct (GQfacts z Gz) as (b & _ & _ & _ & Bl1 & Bl2 & Hz). lia. }
    (* [comment removed for export] *)
    assert (IDXfacts : forall z, idx_lo st <= z < idx_hi st -> exists sl, nth_error (a_sec st) (length (a_sec st) - 1) = Some sl /\ In sl (a_sec st) /\ sc_map sl + 24 <= z < sc_map sl + 32).
    { intros z Hz. unfold idx_lo, idx_hi in Hz. destruct (nth_error (a_sec st) (length (a_sec st) - 1)) as [sl|] eqn:EL; [| lia].
      exists sl. split; [reflexivity|]. split; [exact (nth_error_In _ _ EL) | exact Hz]. }
    (* [comment removed for export] *)
    assert (RMSband : forall z, sh_lo (sc_map s) <= z < sh_hi (sc_map s) (sc_mapsz s) -> SB <= z < AS_HEAPLO).
    { intros z Hz. unfold sh_lo, sh_hi in Hz. clear -Hz SA1 SA2 B6 B7. Zlia. }
    assert (PTRfacts : 0 <= Z.of_nat i < len /\ len <= a_nres st /\ 8 * a_nres st <= 2 ^ 23) by ((lazymatch goal with |- ?G => let G' := eval unfold len in G in change_no_check G' end); clear -Hil S1 S3; lia).
    destruct (RNG _ _ (all_ranges_fixed bt st _ IN8)) as ((PD1 & PD2 & PD3 & PD4 & PD5) & _). box PD4. box PD5.
    pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ IN8) (all_ranges_fixed bt st _ INT) ltac:(intros E; injection E; intros; ulia)) as D8T. hnf in D8T. cbn in D8T. box D8T.
    pose proof (space_vs_fixed bt st Lc FF W _ _ IN8 ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE in G in change_no_check G' end); lia)) as SP8'. box SP8'.
    assert (IDXdyn : forall z, idx_lo st <= z < idx_hi st -> exists sl, In sl (a_sec st) /\ sc_map sl + 24 <= z < sc_map sl + 32 /\ sc_map sl + 32 <= sc_map sl + sc_mapsz sl
                     /\ 0 < sc_map sl /\ sc_map sl + sc_mapsz sl <= CEIL /\ In (sc_map sl, sc_map sl + sc_mapsz sl) (dyn_ranges st)).
    { intros z Hz; destruct (IDXfacts z Hz) as (sl & _ & Hsl & Hz2); exists sl; destruct (sec_facts bt st Lc FF W sl Hsl) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8);
         (split; [exact Hsl|]); (split; [exact Hz2|]); (split; [clear -A5 A6 A7; unfold PG in *; lia|]); (split; [exact A1|]); (split; [exact A2|]); exact (sec_dyn st sl Hsl). }
    (* [comment removed for export] *)
    set (PIN := fun z : Z => qhdr bt z \/ gq_objs st z \/ (IB bt + 120 <= z < IB bt + 128) \/ (IB bt + 680 <= z < IB bt + 681)
                             \/ (bt_ptrarr bt + 8 * Z.of_nat i <= z < bt_ptrarr bt + 8 * Z.of_nat i + 8) \/ (idx_lo st <= z < idx_hi st)
                             \/ (sh_lo (sc_map s) <= z < sh_hi (sc_map s) (sc_mapsz s))).
    pose proof (PIN5dec st i s) as PINd. fold PIN in PINd.
    set (Mmid := fun a : word => if PINd (u a) then M a else M' a).
    assert (P : Rep bt st Lc FF Mmid mdl).
    { apply (Rep_frame_q bt st Lc FF M Mmid mdl W R); intros a NEa; unfold Mmid in NEa |- *;
         destruct (PINd (u a)) as [IN|NI]; [exfalso; exact (NEa eq_refl)|];
         destruct (AGR a NEa) as [Hf Hd]; (split; [| exact Hd]);
         intros HC; unfold foot_secfree in Hf; unfold PIN in NI;
         destruct Hf as [Hf|[Hf|[Hf|[Hf|[Hf|[Hf|[Hf|Hf]]]]]]]; [am_tauto | am_tauto | | am_tauto | am_tauto | am_tauto | exact (stats_not_cells bt st Lc FF W (u a) Hf HC) | exact (ceil_not_cells bt st Lc FF W (u a) Hf HC)];
         apply (instjunk_not_cells bt st Lc FF W (u a)); [| exact HC]; (lazymatch goal with |- ?G => let G' := eval unfold instjunk in G in change_no_check G' end);
         destruct (Z_lt_dec (u a) (IB bt + 128)) as [L1|L1]; [exfalso; apply NI; right; right; left; lia|];
         destruct (Z.eq_dec (u a) (IB bt + 680)) as [L2|L2]; [exfalso; apply NI; right; right; right; left; lia | lia]. }
    (* [comment removed for export] *)
    assert (AG : forall z, ~ PIN z -> 0 <= z < 2 ^ 64 -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z)).
    { intros z Hz Hr. (lazymatch goal with |- ?G => let G' := eval unfold Mmid in G in change_no_check G' end). rewrite (u64_lit z) by lia. destruct (PINd z) as [IN|NI]; [exfalso; exact (Hz IN) | reflexivity]. }
    assert (DEF : DEFK Mmid M').
    { intros a NEa. unfold Mmid in NEa. destruct (PINd (u a)) as [IN|NI]; [| exfalso; exact (NEa eq_refl)]. exact (proj2 (AGR a NEa)). }
    pose proof (bt_ok_W bt st Lc FF W) as (_ & _ & PRV & QI1 & _).
    destruct QI1 as (plo & phi & Hplo & PP1 & PP2). destruct (PRV plo phi (or_introl Hplo)) as [PP3 PP4].
    assert (INI : ia_img_lo IA <= IB bt + 112 /\ IB bt + 985 <= ia_img_hi IA) by ((lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end); clear -PP1 PP2 PP3 PP4; lia). clear plo phi Hplo PP1 PP2 PP3 PP4.
    assert (PTRZ : forall z, bt_ptrarr bt + 8 * Z.of_nat i <= z < bt_ptrarr bt + 8 * Z.of_nat i + 8 -> bt_ptrarr bt <= z < bt_ptrarr bt + 2 ^ 23) by (intros z Hz; clear -Hz PTRfacts; lia).
    (* [comment removed for export] *)
    assert (IMGR : forall z, ia_img_lo IA <= z < ia_img_hi IA -> ~ qhdr bt z -> ~ (IB bt + 120 <= z < IB bt + 128) -> z <> IB bt + 680 -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z)).
    { intros z Hz N1 N3 N4. apply AG; [| clear -Hz I1 I2; ulia]. (lazymatch goal with |- ?G => let G' := eval unfold PIN in G in change_no_check G' end). intros [X|[X|[X|[X|[X|[X|X]]]]]].
      - exact (N1 X).
      - pose proof (GQspace z X) as ZS. clear -ZS Hz I2 SBH. ulia.
      - exact (N3 X).
      - apply N4. lia.
      - pose proof (PTRZ z X) as ZP. clear -ZP Hz PD4. Zlia.
      - destruct (IDXdyn z X) as (sl & _ & Hz2 & Hz3 & _ & _ & HD). destruct (RNG _ _ (all_ranges_dyn bt st _ HD)) as ((_ & _ & _ & D4 & _) & _). clear -Hz Hz2 Hz3 D4. lia.
      - pose proof (RMSband z X) as ZS. clear -ZS Hz I2. ulia. }
    assert (TPR : forall z, T <= z < T + PG -> 0 <= z < 2 ^ 64 -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z)).
    { intros z Hz Hr. apply AG; [| exact Hr]. (lazymatch goal with |- ?G => let G' := eval unfold PIN in G in change_no_check G' end). intros [X|[X|[X|[X|[X|[X|X]]]]]].
      - unfold qhdr in X. clear -X Hz TPI INI. Zlia.
      - pose proof (GQspace z X) as ZS. clear -ZS Hz TPG. Zlia.
      - clear -X Hz TPI INI. Zlia.
      - clear -X Hz TPI INI. Zlia.
      - pose proof (PTRZ z X) as ZP. clear -ZP Hz D8T. Zlia.
      - destruct (IDXdyn z X) as (sl & _ & Hz2 & Hz3 & _ & _ & HD). pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W INT HD) as D. hnf in D. cbn in D. clear -Hz Hz2 Hz3 D. lia.
      - pose proof (RMSband z X) as ZS. clear -ZS Hz TPB. Zlia. }
    assert (FIXR : forall lo hi, In (lo, hi) (bt_fixed bt) -> hi - lo < KSPACE -> hi - lo <> PG -> (hi <= bt_ptrarr bt \/ bt_ptrarr bt + 2 ^ 23 <= lo) ->
                   forall z, lo <= z < hi -> 0 <= z < 2 ^ 64 -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z)).
    { intros lo hi Hin Hlen Hpg H8 z Hz Hr. apply AG; [| exact Hr].
      destruct (fixed_range bt st Lc FF W lo hi Hin) as ((D1 & D2 & D3 & D4 & D5) & _).
      pose proof (space_vs_fixed bt st Lc FF W lo hi Hin Hlen) as SP.
      (lazymatch goal with |- ?G => let G' := eval unfold PIN in G in change_no_check G' end); intros [X|[X|[X|[X|[X|[X|X]]]]]].
      - unfold qhdr in X. clear -X Hz D4 INI. lia.
      - pose proof (GQspace z X) as ZS. clear -ZS Hz SP. ulia.
      - clear -X Hz D4 INI. lia.
      - clear -X Hz D4 INI. lia.
      - pose proof (PTRZ z X) as ZP. clear -ZP Hz H8. lia.
      - destruct (IDXdyn z X) as (sl & _ & Hz2 & Hz3 & _ & _ & HD). pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W Hin HD) as D. hnf in D. cbn in D. clear -Hz Hz2 Hz3 D. lia.
      - pose proof (RMSband z X) as ZS. clear -ZS Hz D5. ulia. }
    assert (PTRR : forall z, bt_ptrarr bt <= z < bt_ptrarr bt + 2 ^ 23 -> ~ (bt_ptrarr bt + 8 * Z.of_nat i <= z < bt_ptrarr bt + 8 * Z.of_nat i + 8) -> 0 <= z < 2 ^ 64 -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z)).
    { intros z Hz N5 Hr. apply AG; [| exact Hr]. (lazymatch goal with |- ?G => let G' := eval unfold PIN in G in change_no_check G' end); intros [X|[X|[X|[X|[X|[X|X]]]]]].
      - unfold qhdr in X. clear -X Hz PD4 INI. Zlia.
      - pose proof (GQspace z X) as ZS. clear -ZS Hz SP8'. Zlia.
      - clear -X Hz PD4 INI. Zlia.
      - clear -X Hz PD4 INI. Zlia.
      - exact (N5 X).
      - destruct (IDXdyn z X) as (sl & _ & Hz2 & Hz3 & _ & _ & HD). pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W IN8 HD) as D. hnf in D. cbn in D. clear -Hz Hz2 Hz3 D. lia.
      - pose proof (RMSband z X) as ZS. clear -ZS Hz PD5. Zlia. }
    assert (DYNR : forall lo hi, In (lo, hi) (dyn_ranges st) -> forall z, lo <= z < hi -> ~ (idx_lo st <= z < idx_hi st) -> 0 <= z < 2 ^ 64 -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z)).
    { intros lo hi Hin z Hz N6 Hr. apply AG; [| exact Hr].
      destruct (RNG _ _ (all_ranges_dyn bt st _ Hin)) as ((D1 & D2 & D3 & D4 & D5) & _).
      pose proof (space_vs_dyn bt st Lc FF W lo hi Hin) as SP.
      (lazymatch goal with |- ?G => let G' := eval unfold PIN in G in change_no_check G' end); intros [X|[X|[X|[X|[X|[X|X]]]]]].
      - unfold qhdr in X. clear -X Hz D4 INI. lia.
      - pose proof (GQspace z X) as ZS. clear -ZS Hz SP. ulia.
      - clear -X Hz D4 INI. lia.
      - clear -X Hz D4 INI. lia.
      - pose proof (PTRZ z X) as ZP. pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W IN8 Hin) as D. hnf in D. cbn in D. clear -ZP Hz D. lia.
      - exact (N6 X).
      - pose proof (RMSband z X) as ZS. clear -ZS Hz D5. ulia. }
    assert (SPCR : forall z, SBEG <= z < SBEG + KSPACE + PG -> ~ gq_objs st z -> 0 <= z < 2 ^ 64 -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z)).
    { intros z Hz N2 Hr. apply AG; [| exact Hr]. (lazymatch goal with |- ?G => let G' := eval unfold PIN in G in change_no_check G' end). intros [X|[X|[X|[X|[X|[X|X]]]]]].
      - unfold qhdr in X. clear -X Hz SBH INI I2. ulia.
      - exact (N2 X).
      - clear -X Hz SBH INI I2. ulia.
      - clear -X Hz SBH INI I2. ulia.
      - pose proof (PTRZ z X) as ZP. clear -ZP Hz SP8'. Zlia.
      - destruct (IDXdyn z X) as (sl & _ & Hz2 & Hz3 & _ & _ & HD). pose proof (space_vs_dyn bt st Lc FF W _ _ HD) as SP. clear -Hz Hz2 Hz3 SP. ulia.
      - pose proof (RMSband z X) as ZS. clear -ZS Hz SBH. ulia. }
    assert (BANDR : forall z, SB <= z < AS_HEAPLO -> ~ (sh_lo (sc_map s) <= z < sh_hi (sc_map s) (sc_mapsz s)) -> 0 <= z < 2 ^ 64 -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z)).
    { intros z Hz N7 Hr. apply AG; [| exact Hr]. (lazymatch goal with |- ?G => let G' := eval unfold PIN in G in change_no_check G' end). intros [X|[X|[X|[X|[X|[X|X]]]]]].
      - unfold qhdr in X. clear -X Hz INI I2. ulia.
      - pose proof (GQspace z X) as ZS. clear -ZS Hz SBH. ulia.
      - clear -X Hz INI I2. ulia.
      - clear -X Hz INI I2. ulia.
      - pose proof (PTRZ z X) as ZP. clear -ZP Hz PD5. Zlia.
      - destruct (IDXdyn z X) as (sl & _ & Hz2 & Hz3 & _ & _ & HD). destruct (RNG _ _ (all_ranges_dyn bt st _ HD)) as ((_ & _ & _ & _ & D5) & _). clear -Hz Hz2 Hz3 D5. ulia.
      - exact (N7 X). }
    (* [comment removed for export] *)
    assert (CHKR : forall c' a', 1 <= c' <= 30 -> carved bt st c' a' ->
               ~ (c' = BATCHCLASS /\ exists b, In b (a_gq st) /\ ba_addr b = a') ->
               forall z, a' <= z < a' + csize c' -> 0 <= z < 2 ^ 64 -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z)).
    { intros c' a' Hc' CV' NB z Hz Hr. destruct (carved_range bt st Lc FF W c' a' Hc' CV') as (D1 & D2 & D3 & D4 & D5).
      apply SPCR; [clear -Hz D3 D4; ulia | | exact Hr].
      intros Gi. destruct (GQfacts z Gi) as (b & _ & Hb & CVb & Bl1 & Bl2 & Hi2).
      destruct (chunk_cases bt st Lc FF W c' a' BATCHCLASS (ba_addr b) Hc' HC24 CV' CVb) as [[EC EA] | D].
      + apply NB. split; [exact EC|]. exists b. split; [exact Hb | symmetry; exact EA].
      + change (csize BATCHCLASS) with 8192 in D. unfold BATCHSZ in *. clear -D Hz Hi2. lia. }
    destruct (WR1 BATCHCLASS HC24) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PARTB & _). pose proof PARTB as (_ & _ & _ & _ & _ & _ & _ & NBL & _).
    assert (BR : forall b0, In b0 (a_tq st ++ a_gq st) -> 0 <= ba_addr b0 /\ ba_addr b0 + BATCHSZ < 2 ^ 64 /\ Z.of_nat (length (ba_items b0)) <= BATCHCAP).
    { intros b0 Hb0. destruct (batch_facts bt st Lc FF W b0 Hb0) as (_ & BL1 & BL2 & BL3). clear -BL1 BL2 BL3 X14 X15. ulia. }
    assert (BAT : forall b0 z, In b0 (a_tq st) -> ba_addr b0 <= z < ba_addr b0 + BATCHSZ -> 0 <= z < 2 ^ 64 -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z)).
    { intros b0 z Hb0 Hz Hr. assert (Hb2 : In b0 (a_tq st ++ a_gq st)) by (apply in_app_iff; left; exact Hb0).
      destruct (batch_facts bt st Lc FF W b0 Hb2) as (CVb & _ & BL2 & BL3).
      apply (CHKR BATCHCLASS (ba_addr b0) HC24 CVb); [| change (csize BATCHCLASS) with 8192; unfold BATCHSZ in Hz; exact Hz | exact Hr].
      intros (_ & b & Hb & EA). destruct (in_split _ _ Hb0) as (t1 & t2 & ET). rewrite ET, !map_app in WQ5. cbn [map] in WQ5. rewrite <- app_assoc in WQ5. cbn [app] in WQ5.
      apply (NoDup_remove_2 _ _ _ WQ5). apply in_app_iff. right. apply in_app_iff. right. rewrite <- EA. apply in_map. exact Hb. }
    (* [comment removed for export] *)
    assert (HDRR : forall p' n' z, In (p', n') Lc \/ In (p' - 16, n') (quar st) -> foot_hdr p' n' z -> 0 <= z < 2 ^ 64 -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z)).
    { intros p' n' z Hown Hf Hr. pose proof (rz_range n') as RZ'.
      destruct (hdr_zone bt st Lc FF W p' n' z Hown Hf) as [(HP' & W1 & W2 & W3 & CV' & HC' & N1' & W4) | (HP' & sc' & Hs' & Eu' & En' & W1 & N1')].
      - apply (CHKR (blk_class n') (prim_alloc_beg p' n') HC' CV'); [| clear -W1 W2 W3 W4 N1' RZ'; unfold prim_alloc_beg in *; lia | exact Hr].
        intros (EC & b & Hb & EA). apply (NBL (ba_addr b) ltac:(exists b; split; [apply in_app_iff; right; exact Hb | reflexivity]) eq_refl). rewrite EA, <- EC.
        destruct Hown as [Hown1|Hown1].
        * left. pose proof (live_chunk bt st Lc FF W p' n' Hown1 HP') as Gv. cbn zeta in Gv. destruct Gv as (_ & _ & G3 & _). exact G3.
        * right; left. pose proof (quar_chunk bt st Lc FF W (p' - 16) n' Hown1 HP') as Gv. cbn zeta in Gv. replace (p' - 16 + 16) with p' in Gv by lia.
          destruct Gv as (_ & _ & G3 & _). exact G3.
      - destruct (sec_facts bt st Lc FF W sc' Hs') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
        apply (DYNR _ _ (sec_dyn st sc' Hs')); [rewrite Eu', En' in *; clear -W1 A5 A6 N1'; ulia | | exact Hr].
        intros X. destruct (IDXfacts z X) as (sl & _ & Hsl & Hz2).
        destruct (sec_cases bt st Lc FF W sc' sl Hs' Hsl) as [<- | D]; [rewrite Eu', En' in *; clear -W1 A5 Hz2; unfold PG in *; lia|].
        destruct (sec_facts bt st Lc FF W sl Hsl) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8). rewrite Eu', En' in *. clear -W1 A5 A6 N1' Hz2 D C5 C6 C7. unfold PG in *. lia. }
    assert (CHvsFAd : forall c' a' c0, 1 <= c' <= 30 -> carved bt st c' a' -> 1 <= c0 <= 30 -> a' + csize c' <= fa_beg SBEG c0 \/ fa_beg SBEG c0 + 2 ^ 29 <= a').
    { intros c' a' c0 Hc' CVa Hc0. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (E1' & E2' & E3' & E4' & E5' & _).
      destruct (carved_range bt st Lc FF W c' a' Hc' CVa) as (D1 & D2 & _).
      pose proof (region_facts bt st Lc FF W c' Hc') as RF. cbn zeta in RF. destruct RF as (F1 & F2 & F3 & F4 & F5 & _).
      unfold region_beg, fa_beg, region_beg, KFAOFF, KREGION in *.
      destruct (Z.lt_trichotomy c0 c') as [LT|[->|GT]]; [| left; clear -D1 D2 F2 F3; lia |].
      * right. assert (c0 * 2 ^ 32 + 2 ^ 32 <= c' * 2 ^ 32) by (replace (c0 * 2 ^ 32 + 2 ^ 32) with ((c0 + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; lia). clear -H D1 D2 F2 F3. lia.
      * left. assert (c' * 2 ^ 32 + 2 ^ 32 <= c0 * 2 ^ 32) by (replace (c' * 2 ^ 32 + 2 ^ 32) with ((c' + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; lia).
        destruct (WR1 c' Hc') as (R1' & _ & R3' & _). unfold KREGION_EXHAUST, KUSERMAP in R3'. clear -H D1 D2 F2 F3 R1' R3'. lia. }
    clear WR2 WC WQ1 WQ2 WQ3 WQ4 S2 LV1 LV3 WK WD WM' PW' R6a R6b IN6 G PARTB.
    pose proof P as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19).
    try ceil; unfold AS_HEAPLO, AS_LO, PG, FAKE_SIZE, KSPACE in X1, X2, X3, X4, X5, X6, X8, X9, X10, X11, X12, X13, X14, X15, Z2, Z4, Z6, Z8, Z10, Z12, Z14, Z16.
    (lazymatch goal with |- ?G => let G' := eval unfold Rep in G in change_no_check G' end).
    (* [comment removed for export] *)
    split. { eapply cells_hold_frame; [exact P1 | exact YC |]. intros c0 z Hc0 Hz. rewrite Forall_forall in DC.
             destruct (img_kinds bt st Lc FF W z ltac:(left; exists c0; split; [exact Hc0 | exact Hz])) as [LT _].
             assert (ND : ~ img_dyn IA z) by exact (DC c0 Hc0 z Hz). unfold img_dyn in ND. unfold qhdr, IB in *.
             apply (IMGR z LT); [intros X; apply ND; right; right; left; lia | intros X; apply ND; left; lia | intros X; apply ND; left; lia]. }
    (* [comment removed for export] *)
    split. { destruct P2 as (I1' & I2' & I3 & I4 & I5 & I6 & IL & IP & IW). (lazymatch goal with |- ?G => let G' := eval unfold rep_instance in G in change_no_check G' end).
             change (a_nres st') with (a_nres st). change (a_sec st') with SR. change (a_gq st') with gq'.
             assert (AGI : forall z, ((IB bt + 112 <= z < IB bt + 120) \/ (IB bt + 880 <= z < IB bt + 888) \/ (IB bt + 920 <= z < IB bt + 985)) -> 0 <= z < 2 ^ 64 -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z)).
             { intros z Hz Hr. apply IMGR; [clear -Hz INI; lia | (lazymatch goal with |- ?G => let G' := eval unfold qhdr in G in change_no_check G' end); clear -Hz; lia | clear -Hz; lia | clear -Hz; lia]. }
             split; [frZ AGI I1'|]. split; [(lazymatch goal with |- ?G => let G' := eval unfold SR in G in change_no_check G' end); rewrite (swap_remove_length (a_sec st) i s Hnth); exact CNCH|]. split; [exact CMTX|]. split; [frB AGI I4|]. split; [frB AGI I5|]. split; [frB AGI I6|].
             split; [exact NLIST|].
             split. { intros j sj Hsj. destruct (nth_error_swap_remove (a_sec st) i j s sj Hnth Hsj) as (JL & [[-> HL] | [NEj Hj]]).
                      - exact (proj1 (CMOVE sj ltac:((lazymatch goal with |- ?G => let G' := eval unfold len in G in change_no_check G' end); lia) HL)).
                      - pose proof (IP j sj Hj) as C. eapply (cellZ_frame _ _ _ _ _ _ C); [clear -PD1; lia | clear -JL PTRfacts PD1 PD2 PD3; unfold len in *; ulia |]. intros z Hz. cbn in Hz.
                        apply PTRR; [clear -Hz JL PTRfacts; unfold len in *; lia | clear -Hz NEj; lia | clear -Hz JL PTRfacts PD1 PD2 PD3; unfold len in *; ulia]. }
             frW DEF IW. }
    (* [comment removed for export] *)
    split. { destruct P3 as (T1 & T2 & T3 & T4 & T5 & T6 & TL & TP & TW & TC1 & TC2 & TC3 & TC4). (lazymatch goal with |- ?G => let G' := eval unfold rep_thread in G in change_no_check G' end).
             change (a_tq st') with (a_tq st). change (a_cinit st') with (a_cinit st). change (a_cache st') with (a_cache st).
             assert (AGT : forall z, T <= z < T + PG -> 0 <= z < 2 ^ 64 -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z)) by exact TPR.
             assert (AGC : forall z, bt_tctx bt <= z < bt_tctx bt + 160 -> 0 <= z < 2 ^ 64 -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z)).
             { intros z Hz Hr. apply (FIXR _ _ INC); [ulia | ulia | | clear -Hz; lia | exact Hr].
               pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ INC) (all_ranges_fixed bt st _ IN8) ltac:(intros E; injection E; intros; lia)) as D. hnf in D. cbn in D. exact D. }
             unfold T_QC, T_PC, PC_SZ, T_UNW, PG in *.
             split; [frZ AGT T1|]. split; [frZ AGT T2|]. split; [frZ AGT T3|]. split; [frB AGT T4|]. split; [frZ AGT T5|]. split; [frB AGT T6|].
             split. { eapply rep_list_frame; [exact TL | lia | lia |]. intros z Hz Hr. apply AGT; [clear -Hz; lia | exact Hr]. }
             split. { intros c' Hc'. pose proof (cache_len bt st Lc FF W c' Hc') as CL'.
                      eapply rep_pclass_frame; [exact (TP c' Hc') | (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); ulia | (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); ulia | exact CL' |].
                      unfold T_PC, PC_SZ in *. intros z Hz Hr. apply AGT; [clear -Hz Hc'; lia | exact Hr]. }
             split; [frW DEF TW|]. split; [frZ AGC TC1|]. split; [frZ AGC TC2|]. split; [frZ AGT TC3 | frZ AGT TC4]. }
    (* [comment removed for export] *)
    split. { intros c0 Hc0. destruct (P4 c0 Hc0) as [G0 F0]. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF.
             destruct RF as (E1' & E2' & E3' & E4' & E5' & E6' & E7' & E8' & E9' & E10' & _).
             change (a_reg st' c0) with (a_reg st c0).
             eapply rep_region_frame; [exact DEF | exact G0 | exact F0 | ulia | ulia | ulia | ulia | ulia |].
             intros z Hz Hr. unfold foot_region in Hz. destruct Hz as [[Hz _] | Hz].
             - apply SPCR; [clear -Hz E9' E10'; ulia | intros Zi; pose proof (GQspace z Zi) as ZS; clear -ZS Hz E9'; ulia | exact Hr].
             - apply SPCR; [clear -Hz E1' E2' E5' E6' E7' E8'; ulia | | exact Hr].
               intros Zi. destruct (GQfacts z Zi) as (bl & _ & _ & CVl & Bl1 & Bl2 & Hi2).
               destruct (CHvsFAd BATCHCLASS (ba_addr bl) c0 HC24 CVl Hc0) as [D | D]; change (csize BATCHCLASS) with 8192 in D; unfold BATCHSZ in Hi2; clear -D Hz Hi2 E6' E7'; lia. }
    (* [comment removed for export] *)
    split. { change (a_tq st') with (a_tq st). eapply rep_batches_frame; [exact DEF | exact P5 | intros b0 Hb0; exact (BR b0 ltac:(apply in_app_iff; left; exact Hb0)) |].
             intros b0 z Hb0 Hz Hr. unfold foot_batch in Hz. apply (BAT b0 z Hb0); [| exact Hr].
             destruct (BR b0 ltac:(apply in_app_iff; left; exact Hb0)) as (_ & _ & Q3). clear -Hz Q3. ulia. }
    (* [comment removed for export] *)
    split; [exact NBAT|].
    (* [comment removed for export] *)
    split. { change (rep_secondary bt st' M') with (forall j sj, nth_error SR j = Some sj ->
                 cellZ SG M' (sc_map sj) 8 (sc_map sj) /\ cellZ SG M' (sc_map sj + 8) 8 (sc_mapsz sj) /\ cellZ SG M' (sc_map sj + 16) 8 (sec_needed (sc_n sj))
                 /\ cellZ SG M' (sc_map sj + 24) 8 (Z.of_nat j) /\ writableZ SG M' (sc_map sj) (sc_map sj + sc_mapsz sj)).
             intros j sj Hsj. destruct (nth_error_swap_remove (a_sec st) i j s sj Hnth Hsj) as (JL & CASE).
             assert (Hoj : exists oj, nth_error (a_sec st) oj = Some sj) by (destruct CASE as [[_ HL] | [_ Hj]]; [exists (length (a_sec st) - 1)%nat; exact HL | exists j; exact Hj]).
             destruct Hoj as (oj & Hoj). pose proof (nth_error_In _ _ Hoj) as Hinj.
             destruct (P7 oj sj Hoj) as (C1 & C2 & C3 & C4 & CW). destruct (sec_facts bt st Lc FF W sj Hinj) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
             assert (RJ : 0 <= sc_map sj /\ sc_map sj + 32 < 2 ^ 64 /\ sc_map sj + 32 <= sc_map sj + sc_mapsz sj) by (clear -A1 A2 A5 A6 A7; ulia).
             assert (AGs : forall z, sc_map sj <= z < sc_map sj + 24 -> 0 <= z < 2 ^ 64 -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z)).
             { intros z Hz Hr. apply (DYNR _ _ (sec_dyn st sj Hinj)); [clear -Hz RJ; lia | | exact Hr].
               intros X. destruct (IDXfacts z X) as (sl & _ & Hsl & Hz2).
               destruct (sec_cases bt st Lc FF W sj sl Hinj Hsl) as [<- | D]; [clear -Hz Hz2; lia|].
               destruct (sec_facts bt st Lc FF W sl Hsl) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8). clear -Hz Hz2 D RJ Q5 Q6 Q7. unfold PG in *. lia. }
             split; [eapply (cellZ_frame _ _ _ _ _ _ C1); [clear -RJ; lia | clear -RJ; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros z Hz; cbn in Hz; apply AGs; clear -Hz RJ; lia]|].
             split; [eapply (cellZ_frame _ _ _ _ _ _ C2); [clear -RJ; lia | clear -RJ; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros z Hz; cbn in Hz; apply AGs; clear -Hz RJ; lia]|].
             split; [eapply (cellZ_frame _ _ _ _ _ _ C3); [clear -RJ; lia | clear -RJ; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros z Hz; cbn in Hz; apply AGs; clear -Hz RJ; lia]|].
             split; [| frW DEF CW].
             destruct CASE as [[-> HL] | [NEj Hj]].
             - exact (proj2 (CMOVE sj ltac:((lazymatch goal with |- ?G => let G' := eval unfold len in G in change_no_check G' end); lia) HL)).
             - assert (oj = j) by (apply (proj1 (NoDup_nth_error (a_sec st)) NDS0 oj j (nth_error_lt _ _ _ Hoj)); rewrite Hoj, Hj; reflexivity). subst oj.
               eapply (cellZ_frame _ _ _ _ _ _ C4); [clear -RJ; lia | clear -RJ; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. intros z Hz. cbn in Hz.
               apply (DYNR _ _ (sec_dyn st sj Hinj)); [clear -Hz RJ; lia | | clear -Hz RJ; lia].
               intros X. destruct (IDXfacts z X) as (sl & HLs & Hsl & Hz2).
               destruct (sec_cases bt st Lc FF W sj sl Hinj Hsl) as [<- | D].
               + assert (j = (length (a_sec st) - 1)%nat) by (apply (proj1 (NoDup_nth_error (a_sec st)) NDS0 j _ (nth_error_lt _ _ _ Hj)); rewrite Hj, HLs; reflexivity). lia.
               + destruct (sec_facts bt st Lc FF W sl Hsl) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8). clear -Hz Hz2 D RJ Q5 Q6 Q7. unfold PG in *. lia. }
    (* [comment removed for export] *)
    split. { destruct P8 as [HLh HQh]. split.
             - intros p' n' Hin'. destruct (live_range bt st Lc FF W p' n' Hin') as (A1 & A2 & A3 & A4). pose proof (rz_range n') as RZ'.
               eapply rep_hdr_frame; [exact DEF | exact (HLh p' n' Hin') | clear -A1 A3 RZ'; ulia | clear -A2 A3; ulia |]. intros z Hz Hr. exact (HDRR p' n' z (or_introl Hin') Hz Hr).
             - intros m0 n' Hq'. apply QSUB in Hq'. destruct Hq' as [Hq0 NErm]. destruct (HQh m0 n' Hq0) as [Hh HW]. split; [| frW DEF HW].
               destruct (quar_item_range bt st Lc FF W m0 n' Hq0) as (QB1 & QB2 & QB3). pose proof (rz_range n') as RZn.
               eapply rep_hdr_frame; [exact DEF | exact Hh | clear -QB1 QB2 QB3 RZn; ulia | clear -QB1 QB2 QB3 RZn; ulia |]. intros z Hz Hr.
               apply (HDRR (m0 + 16) n' z); [right; replace (m0 + 16 - 16) with m0 by lia; exact Hq0 | exact Hz | exact Hr]. }
    (* [comment removed for export] *)
    assert (IMGR0 : forall z, ia_img_lo IA <= z < ia_img_hi IA -> ~ (IB bt + 112 <= z < IB bt + 985) -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z)).
    { intros z Hz N0. apply IMGR; [exact Hz | (lazymatch goal with |- ?G => let G' := eval unfold qhdr in G in change_no_check G' end); clear -N0; lia | clear -N0; lia | clear -N0; lia]. }
    split. { change (rep_depot bt st' M') with (rep_depot bt st M'). eapply rep_depot_frame; [exact DEF | exact P9 | uilia | uilia | uilia | uilia | | |].
             - intros id Hid. destruct (node_addr_range bt st Lc FF W id Hid) as (_ & A1 & A2 & _). clear -A1 A2. ulia.
             - intros z Hz Hr. destruct (img_kinds bt st Lc FF W z ltac:(right; right; left; exact Hz)) as [LT _]. apply (IMGR0 z LT).
               unfold foot_depot_static in Hz. unfold DEPOT_NIDS, DEPOT_MAP1 in Hz. unfold IB, DEPOT_TAB, SSOBJ in *. clear -Hz J1 J2. Zlia.
             - intros id z Hid Hz Hr. unfold foot_node in Hz. destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & A1 & A2 & A3).
               pose proof (node_addr_block bt st id Hid) as Hbk. set (bb := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *. clearbody bb.
               destruct HIn as [Eb | Hnb].
               + apply (FIXR _ _ INN); [clear; ulia | clear; ulia | | clear -Hz Hbk Eb; rewrite Eb; lia | exact Hr].
                 pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ INN) (all_ranges_fixed bt st _ IN8) ltac:(intros E; injection E; intros; lia)) as D. hnf in D. cbn in D. exact D.
               + apply (DYNR _ _ (node_dyn st bb Hnb)); [clear -Hz Hbk; lia | | exact Hr].
                 intros X. destruct (IDXfacts z X) as (sl & _ & Hsl & Hz2). destruct (sec_facts bt st Lc FF W sl Hsl) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
                 destruct (sec_vs_node bt st Lc FF W sl bb Hsl Hnb) as [HSN|HSN]; clear -HSN Hz Hbk Hz2 Q5 Q6 Q7; unfold PG in *; lia. }
    (* [comment removed for export] *)
    split. { change (rep_fake bt st' FF M') with (rep_fake bt st FF M'). pose proof (dtls_facts bt st Lc FF W) as [DT1 DT2]. eapply rep_fake_frame; [exact DEF | exact P10 | ulia | ulia | uilia | uilia | clear -DT1; ulia | clear -DT2; ulia | | |].
             - intros f k0 Hf. destruct (fake_frame_facts bt st Lc FF W f k0 Hf) as (A1 & A2 & A3 & A4 & _). clear -A1 A2 A4 X5 X6. ulia.
             - intros z Hz Hr. unfold foot_fake_static in Hz.
               assert (FS8 : bt_fs bt + FAKE_SIZE <= bt_ptrarr bt \/ bt_ptrarr bt + 2 ^ 23 <= bt_fs bt).
               { pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ INFS) (all_ranges_fixed bt st _ IN8) ltac:(intros E; injection E; intros; ulia)) as D. hnf in D. cbn in D. exact D. }
               destruct Hz as [Hz|[Hz|[Hz|[Hz|Hz]]]].
               1-3: apply (FIXR _ _ INFS); [clear; ulia | clear; ulia | exact FS8 | clear -Hz; ulia | exact Hr].
               + destruct (img_kinds bt st Lc FF W z ltac:(do 3 right; left; exact Hz)) as [LT _]. apply (IMGR0 z LT). unfold IB in *. clear -Hz J5. Zlia.
               + destruct (dtls_cell_facts bt st Lc FF W z Hz) as (DF1 & DF2 & DF3 & DF4 & DF5 & DF6 & DF7).
                 pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & IN6' & R6a' & R6b' & _) & _).
                 apply AG; [| exact Hr]. (lazymatch goal with |- ?G => let G' := eval unfold PIN in G in change_no_check G' end). intros [X|[X|[X|[X|[X|[X|X]]]]]].
                 * apply DF3. unfold qhdr in X. clear -X INI. lia.
                 * pose proof (GQspace z X) as ZS. apply (DF6 _ _ IN6'); [clear -R6a' R6b'; unfold KSPACE, PG in *; lia | clear -ZS R6a' R6b'; unfold KSPACE, PG in *; lia].
                 * apply DF3. clear -X INI. lia.
                 * apply DF3. clear -X INI. lia.
                 * pose proof (PTRZ z X) as ZP. apply (DF6 _ _ IN8); [clear; (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); lia | exact ZP].
                 * destruct (IDXdyn z X) as (sl & _ & Hz2 & Hz3 & _ & _ & HD). apply (DF7 _ _ HD). clear -Hz2 Hz3. lia.
                 * pose proof (RMSband z X) as ZS. apply DF4. clear -ZS. ulia.
             - intros f k0 z Hf Hz Hr. unfold foot_fword in Hz. destruct (fake_frame_facts bt st Lc FF W f k0 Hf) as (A1 & A2 & A3 & A4 & _).
               apply (FIXR _ _ INFS); [clear; ulia | clear; ulia | | clear -Hz A1 A2 A4; ulia | exact Hr].
               pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ INFS) (all_ranges_fixed bt st _ IN8) ltac:(intros E; injection E; intros; ulia)) as D. hnf in D. cbn in D. exact D. }
    (* [comment removed for export] *)
    split. { change (rep_ialloc bt st' M') with (rep_ialloc bt st M'). eapply rep_ialloc_frame; [exact P11 | uilia | uilia | uilia | uilia |].
             intros z Hz Hr. destruct (img_kinds bt st Lc FF W z ltac:(do 4 right; left; exact Hz)) as [LT _]. apply (IMGR0 z LT).
             unfold ialloc_cells in Hz. unfold IB, IA_FLAG, IA_INST, IASZ in *. clear -Hz J3 J4. Zlia. }
    (* [comment removed for export] *)
    split. { destruct P12 as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6). (lazymatch goal with |- ?G => let G' := eval unfold rep_shadow in G in change_no_check G' end).
             change (a_reg st') with (a_reg st). change (a_sec st') with SR.
             assert (SHR : forall lo1 hi1 g, lo1 / 8 <= g < hi1 / 8 -> 0 <= lo1 -> hi1 <= CEIL + 8 -> SB <= SB + g < AS_HEAPLO /\ 0 <= SB + g /\ SB + g + 1 < 2 ^ 64).
             { intros lo1 hi1 g Hg Hg0 Hg1. clear -Hg Hg0 Hg1 B6 B7. Zlia. }
             assert (SHSEP : forall X Y g, X / 8 <= g < Y / 8 -> (sc_map s + sc_mapsz s <= X \/ Y <= sc_map s) -> ~ (sh_lo (sc_map s) <= SB + g < sh_hi (sc_map s) (sc_mapsz s))).
             { intros X Y g Hg SEP Hr. unfold sh_lo, sh_hi in Hr. clear -Hg SEP Hr SA3 SA4. unfold PG in *. Z.div_mod_to_equations. lia. }
             assert (RMREG : forall c0, 1 <= c0 <= 30 -> sc_map s + sc_mapsz s <= region_beg SBEG c0 \/ fa_beg SBEG c0 + 2 ^ 29 <= sc_map s).
             { intros c0 Hc0. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (D1 & D2 & D3 & D4 & D5 & _).
               destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st s Hs)) as [SP | SP]; [left; clear -SP D1; lia | right; clear -SP D5; unfold KSPACE, PG in *; lia]. }
             split. { intros c0 g Hc0 Hg NL'. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (D1 & D2 & D3 & D4 & D5 & _).
                      destruct (SHR _ _ g Hg ltac:(clear -D1 X14; ulia) ltac:(clear -D2 D3 D4 D5 X15; ulia)) as (QQ1 & QQ2 & QQ3).
                      assert (EXQ : existsb (fun mn : Z * Z => ((fst mn + 16) / 8 <=? g) && (g <? (fst mn + 16 + snd mn + 7) / 8)) (quar st')
                                    = existsb (fun mn : Z * Z => ((fst mn + 16) / 8 <=? g) && (g <? (fst mn + 16 + snd mn + 7) / 8)) (quar st)).
                      { apply (existsb_minus _ (quar st) (quar st') (Some (m, n))).
                        - intros x. rewrite (QSUB x). split; intros [A B]; (split; [exact A|]); [intros E; apply B; injection E as ->; reflexivity | intros ->; exact (B eq_refl)].
                        - intros x E. injection E as <-. (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). destruct (((m + 16) / 8 <=? g) && (g <? (m + 16 + n + 7) / 8)) eqn:EB; [| reflexivity]. exfalso.
                          apply andb_prop in EB. destruct EB as [F1 F2]. apply Z.leb_le in F1. apply Z.ltb_lt in F2.
                          destruct (RMREG c0 Hc0) as [SEP | SEP]; rewrite <- Hus in F1, F2; rewrite <- Hsn in F2; clear -F1 F2 Hg SEP SA5 SA6 D2 D3 D5 SA3 SA4; unfold PG in *; Z.div_mod_to_equations; lia. }
                      rewrite EXQ. pose proof (SH1 c0 g Hc0 Hg NL') as BY. eapply (byteZ_frame _ _ _ _ _ BY); [exact QQ2 | exact QQ3 | apply BANDR; [exact QQ1 | | lia]].
                      apply (SHSEP _ _ g Hg). destruct (RMREG c0 Hc0) as [SEP | SEP]; [left; exact SEP | right; clear -SEP D2 D3 D5; lia]. }
             split. { intros c0 g Hc0 Hg. pose proof (SH2 c0 g Hc0 Hg) as BY.
                      pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (D1 & D2 & D3 & D4 & D5 & D6 & _).
                      destruct (SHR _ _ g Hg ltac:(clear -D1 D2 D3 D4 X14; ulia) ltac:(clear -D5 D6 X15; ulia)) as (QQ1 & QQ2 & QQ3).
                      eapply (byteZ_frame _ _ _ _ _ BY); [exact QQ2 | exact QQ3 | apply BANDR; [exact QQ1 | | lia]].
                      apply (SHSEP _ _ g Hg). destruct (RMREG c0 Hc0) as [SEP | SEP]; [left; clear -SEP D1 D2 D3 D4; lia | right; clear -SEP D6; lia]. }
             split. { intros sc g Hsc Hg NUG. apply INSR in Hsc. destruct Hsc as [Hsc NEs]. pose proof (SH3 sc g Hsc Hg NUG) as BY. destruct (sec_facts bt st Lc FF W sc Hsc) as (A1 & A2 & _).
                      destruct (SHR _ _ g Hg ltac:(clear -A1; ulia) ltac:(clear -A2; ulia)) as (QQ1 & QQ2 & QQ3).
                      eapply (byteZ_frame _ _ _ _ _ BY); [exact QQ2 | exact QQ3 | apply BANDR; [exact QQ1 | | lia]].
                      apply (SHSEP _ _ g Hg). destruct (sec_cases bt st Lc FF W s sc Hs Hsc) as [E | D]; [exfalso; exact (NEs (eq_sym E)) | exact D]. }
             split. { intros sc g Hsc HQ' HU. apply INSR in Hsc. destruct Hsc as [Hsc NEs]. pose proof (proj1 (proj1 (QSUB _) HQ')) as HQ.
                      pose proof (SH4 sc g Hsc HQ HU) as BY. destruct (sec_facts bt st Lc FF W sc Hsc) as (A1 & A2 & A3 & A4 & A5 & A6 & _).
                      unfold user_granule in HU.
                      destruct (SHR (sc_user sc) (sc_user sc + sc_n sc + 7) g ltac:(clear -HU; lia) ltac:(clear -A1 A5; ulia) ltac:(clear -A2 A6; ulia)) as (QQ1 & QQ2 & QQ3).
                      eapply (byteZ_frame _ _ _ _ _ BY); [exact QQ2 | exact QQ3 | apply BANDR; [exact QQ1 | | lia]].
                      intros Hr. unfold sh_lo, sh_hi in Hr.
                      destruct (sec_cases bt st Lc FF W s sc Hs Hsc) as [E | D]; [exact (NEs (eq_sym E))|].
                      clear -HU Hr D A3 A4 A5 A6 SA3 SA4. unfold PG in *. Z.div_mod_to_equations. lia. }
             split. { intros c0 g Hc0 Hg. exact (def_keep Mmid M' _ DEF (SH5 c0 g Hc0 Hg)). }
             intros sc g Hsc Hg. apply INSR in Hsc. exact (def_keep Mmid M' _ DEF (SH6 sc g (proj1 Hsc) Hg)). }
    (* [comment removed for export] *)
    split. { destruct P13 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12). (lazymatch goal with |- ?G => let G' := eval unfold rep_ledger in G in change_no_check G' end).
             change (a_dep st') with (a_dep st).
             assert (HOL : forall a, holes bt st' a <-> holes bt st a) by (intros a; (lazymatch goal with |- ?G => let G' := eval unfold holes in G in change_no_check G' end); change (a_reg st') with (a_reg st); am_tauto).
             assert (COM : forall a, committed bt st' a <-> committed bt st a) by (intros a; (lazymatch goal with |- ?G => let G' := eval unfold committed in G in change_no_check G' end); change (a_reg st') with (a_reg st); change (a_nres st') with (a_nres st); am_tauto).
             split. { destruct L1 as (F6l & PF & FOK & FPW & FH). exists F6l.
                      split. { apply (Permutation_cons_inv (a := (Z_to_bv 64 (sc_map s), Z_to_bv 64 (sc_mapsz s)))).
                               eapply Permutation_trans; [exact PM|]. eapply Permutation_trans; [exact PF|].
                               (lazymatch goal with |- ?G => let G' := eval unfold dyn_maps in G in change_no_check G' end). change (a_sec st') with SR. change (a_dep st') with (a_dep st).
                               set (f := fun s0 : schunk => (Z_to_bv 64 (sc_map s0), Z_to_bv 64 (sc_mapsz s0))).
                               set (DD := map (fun b : Z => (Z_to_bv 64 b, Z_to_bv 64 (2 ^ 20))) (dp_nodeblocks (a_dep st)) ++ map (fun b : Z => (Z_to_bv 64 b, Z_to_bv 64 (2 ^ 23))) (dp_storeblocks (a_dep st))).
                               apply Permutation_sym. transitivity (F6l ++ bt_maps0 bt ++ f s :: map f SR ++ DD).
                               { rewrite !(app_assoc F6l (bt_maps0 bt)). apply Permutation_middle. }
                               apply Permutation_app_head. apply Permutation_app_head. change (f s :: map f SR ++ DD) with (map f (s :: SR) ++ DD).
                               apply Permutation_app_tail. exact (Permutation_map f PERM). }
                      split; [exact FOK|]. split; [exact FPW|]. intros a Ha. rewrite (HOL a). exact (FH a Ha). }
             split; [intros a; rewrite (NA a), (L2 a), (HOL a), (COM a); am_tauto|].
             split; [intros a; rewrite (LZ a), (L3 a), (HOL a), (COM a); am_tauto|].
             split; [exact FL'|]. unfold alloc_top in L10 |- *. rewrite E1, E2, E3, E4, E6, E5. repeat (split; [assumption|]). exact NP'. }
    (* [comment removed for export] *)
    split. { apply (rep_budget_sec_free bt st st' Lc Lc FF mdl mdl' s qt qg W P14 Hs).
             - (* [comment removed for export] *)
               intros p0 n0 Hin0. split; [exact Hin0|]. intros E. injection E as -> ->.
               apply (proj1 (S6 s Hs) Hin0). rewrite Hus, Hsn. replace (m + 16 - 16) with m by (clear; lia). exact Hq.
             - reflexivity.
             - reflexivity.
             - reflexivity.
             - (lazymatch goal with |- ?G => let G' := eval unfold st' in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_aa op_sec_free set_gq] in G in change_no_check G' end). rewrite ESEN. reflexivity.
             - reflexivity.
             - change (a_sec st') with SR. exact (Permutation_sym PERM).
             - (lazymatch goal with |- ?G => let G' := eval unfold st' in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_aa op_sec_free set_gq] in G in change_no_check G' end). rewrite ESEN. exact MI.
             - exact EAG. }
    (* [comment removed for export] *)
    split. { intros p' n' Hin'. destruct (P15 p' n' Hin') as [W1 W2]. split; [frW DEF W1 | frW DEF W2]. }
    split. { intros f k0 Hf. frW DEF (P16 f k0 Hf). }
    assert (RTC : forall z, ia_rtc_sb IA <= z < ia_rtc_sb IA + 8 \/ ia_rtc_uar IA <= z < ia_rtc_uar IA + 4 -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z)).
    { intros z Hz. destruct (img_kinds bt st Lc FF W z ltac:(do 5 right; (lazymatch goal with |- ?G => let G' := eval unfold rtc_cells in G in change_no_check G' end); exact Hz)) as [LT _]. apply (IMGR0 z LT).
      unfold IB in *. clear -Hz J6 J7. Zlia. }
    split; [eapply (cellZ_frame _ _ _ _ _ _ P17); [ulia | ulia | intros z Hz; apply RTC; left; cbn in Hz; lia] |].
    split; [eapply (cellZ_frame _ _ _ _ _ _ P18); [ulia | ulia | intros z Hz; apply RTC; right; cbn in Hz; lia] |].
    apply (rep_last_keep bt st _ Mmid M' DEF P19). intros _ E0. rewrite E0 in RMIN. destruct RMIN.
  Qed.
End RC5.
