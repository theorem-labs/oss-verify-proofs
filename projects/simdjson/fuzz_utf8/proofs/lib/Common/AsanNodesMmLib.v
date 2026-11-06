(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AgentNodes Nodes AllocSim AsanAcct AsanAcctShape AsanPlacement BackingAlgebra MmapSim RefNodes. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import NoReserve.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AsanCeil. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import VmGap.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Import AX2. Import AX2S. Import AP. Import APS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section WithFP1.
Context {fx : FPState}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition RES_hull_def (SEGS : list Segment) (A : AP.atable) : Prop :=
  Forall (fun iv : word * word => img_lo A <= bv_unsigned (fst iv)
                                  /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A)
         (segments_reserved SEGS).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_ivs_covered : forall z l, in_ivs z l = covered l z.
Proof.
  intros z l. unfold in_ivs, covered, in_iv, in_rng, B, S. reflexivity.
Qed.

Lemma in_ivs_cons : forall z iv l,
  in_ivs z (iv :: l) = (((bv_unsigned (fst iv) <=? z) && (z <? bv_unsigned (fst iv) + bv_unsigned (snd iv))) || in_ivs z l)%bool.
Proof. reflexivity. Qed.

Lemma in_ivs_app : forall z l1 l2, in_ivs z (l1 ++ l2) = (in_ivs z l1 || in_ivs z l2)%bool.
Proof. intros. unfold in_ivs. apply existsb_app. Qed.

Lemma in_ivs_true' : forall z l, in_ivs z l = true <-> exists iv, In iv l /\ bv_unsigned (fst iv) <= z < bv_unsigned (fst iv) + bv_unsigned (snd iv).
Proof.
  intros z l. unfold in_ivs. rewrite existsb_exists. split.
  - intros [iv [Hin Hb]]. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. eauto.
  - intros [iv [Hin Hb]]. exists iv. split; [exact Hin|]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma in_ivs_false : forall z l,
  in_ivs z l = false <-> forall iv, In iv l -> ~ (bv_unsigned (fst iv) <= z < bv_unsigned (fst iv) + bv_unsigned (snd iv)).
Proof.
  intros z l. split.
  - intros H iv Hin Hz. assert (T : in_ivs z l = true) by (apply (proj2 (in_ivs_true' z l)); eauto). congruence.
  - intros H. destruct (in_ivs z l) eqn:E; [|reflexivity]. exfalso.
    apply in_ivs_true' in E as [iv [Hin Hz]]. exact (H iv Hin Hz).
Qed.

Lemma sum_sizes_live : forall l, sum_sizes l = live_bytes l.
Proof. induction l as [|[a s] l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma sum_sizes_app : forall l1 l2, sum_sizes (l1 ++ l2) = sum_sizes l1 + sum_sizes l2.
Proof. intros. rewrite !sum_sizes_live. apply live_bytes_app. Qed.

(* [comment removed for export] *)
Lemma region_free_sem : forall l (lo n : word) z,
  region_free l lo n = true -> 0 < bv_unsigned n ->
  bv_unsigned lo <= z < bv_unsigned lo + bv_unsigned n -> in_ivs z l = false.
Proof.
  intros l lo n z Hrf Hn Hz. apply (proj2 (in_ivs_false z l)). intros [b s] Hin Hin2. cbn [fst snd] in Hin2.
  pose proof (region_free_In l lo n b s Hrf Hin) as Hov. lia.
Qed.

Lemma region_free_app : forall l1 l2 lo n,
  region_free (l1 ++ l2) lo n = (region_free l1 lo n && region_free l2 lo n)%bool.
Proof. induction l1 as [|[a s] l1 IH]; intros; cbn; [reflexivity|]. rewrite IH, andb_assoc. reflexivity. Qed.

(* [comment removed for export] *)
Lemma map_contains_intro : forall l (lo n : word) b s,
  In (b, s) l -> bv_unsigned b <= bv_unsigned lo -> bv_unsigned lo + bv_unsigned n <= bv_unsigned b + bv_unsigned s ->
  map_contains l lo n = true.
Proof.
  intros l lo n b s Hin H1 H2. unfold map_contains. apply existsb_exists. exists (b, s). split; [exact Hin|].
  cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

(* [comment removed for export] *)
Lemma map_has_intro : forall l (lo n : word), In (lo, n) l -> map_has l lo n = true.
Proof.
  intros l lo n Hin. unfold map_has. apply existsb_exists. exists (lo, n). split; [exact Hin|].
  cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma eager_used_sem : forall m,
  model_ivs_wf m ->
  eager_used m = sum_count (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (vm_maps (m_vmmaps m)).
Proof.
  intros m Hwf. pose proof (vm_backing_used_sem m Hwf) as H. rewrite vm_backing_used_split in H. lia.
Qed.

Lemma mat_pages_le_A_bytes : forall A m,
  MInv A m -> A_wf A -> Z.of_nat (length (m_vm_materialized m)) * page_size <= A_bytes A.
Proof.
  intros A m [N1 N2 N3 N4 N5] Hwf. apply allowed_pages_bound; assumption.
Qed.

Lemma vm_backing_used_le : forall A m,
  MInv A m -> A_wf A -> vm_backing_used m <= eager_used m + A_bytes A.
Proof.
  intros A m HM Hwf. rewrite vm_backing_used_split. pose proof (mat_pages_le_A_bytes A m HM Hwf). lia.
Qed.

Lemma vm_backing_used_limit : forall A m,
  MInv A m -> A_wf A -> vm_backing_used m <= vm_limit (m_vmmaps m).
Proof.
  intros A m HM Hwf. pose proof (vm_backing_used_le A m HM Hwf). pose proof (minv_budget _ _ HM). lia.
Qed.

(* [comment removed for export] *)
Lemma sum_count_negb_covered_mono : forall C C' l,
  (forall x, covered C x = true -> covered C' x = true) ->
  sum_count (fun x => negb (covered C' x)) l <= sum_count (fun x => negb (covered C x)) l.
Proof.
  intros C C' l H. apply sum_count_mono. intros x Hx. apply negb_true_iff in Hx. apply negb_true_iff.
  destruct (covered C x) eqn:E; [|reflexivity]. rewrite (H x E) in Hx. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma iv_subtract_pieces : forall a sz lo hi q,
  iv_wf (a, sz) -> In q (iv_subtract a sz lo hi) ->
  bv_unsigned a <= bv_unsigned (fst q) /\ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned a + bv_unsigned sz
  /\ (bv_unsigned (fst q) + bv_unsigned (snd q) <= lo \/ hi <= bv_unsigned (fst q)).
Proof.
  intros a sz lo hi q Hwf Hin. unfold iv_wf, B, S in Hwf. cbn [fst snd] in Hwf.
  pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
  unfold iv_subtract in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - destruct (bv_unsigned a <? lo) eqn:El; [|destruct Hin]. apply Z.ltb_lt in El.
    destruct Hin as [<-|[]]. cbn [fst snd]. rewrite u64_lit by lia. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:Er; [|destruct Hin]. apply Z.ltb_lt in Er.
    destruct Hin as [<-|[]]. cbn [fst snd]. rewrite !u64_lit by lia. lia.
Qed.

Lemma maps_subtract_pieces : forall l lo hi q,
  ivs_wf l -> In q (maps_subtract l lo hi) ->
  exists r, In r l /\ bv_unsigned (fst r) <= bv_unsigned (fst q)
            /\ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst r) + bv_unsigned (snd r)
            /\ (bv_unsigned (fst q) + bv_unsigned (snd q) <= lo \/ hi <= bv_unsigned (fst q)).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi q Hwf Hin; [destruct Hin|].
  apply ivs_wf_cons_inv in Hwf as [Ha Hl]. cbn [maps_subtract] in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - exists (a, sz). split; [left; reflexivity|]. cbn [fst snd]. exact (iv_subtract_pieces a sz lo hi q Ha Hin).
  - destruct (IH lo hi q Hl Hin) as (r & Hr & H). exists r. split; [right; exact Hr | exact H].
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_disjoint : forall (a sz : word) lo hi,
  lo < hi -> 0 < bv_unsigned sz -> (bv_unsigned a + bv_unsigned sz <= lo \/ hi <= bv_unsigned a) ->
  iv_subtract a sz lo hi = [(a, sz)].
Proof.
  intros a sz lo hi Hlh Hsz Hd. pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs. unfold iv_subtract.
  destruct Hd as [Hd|Hd].
  - destruct (Z.ltb_spec (bv_unsigned a) lo) as [El|El]; [|exfalso; lia].
    rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned.
    destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); [exfalso; lia | reflexivity].
  - destruct (Z.ltb_spec (bv_unsigned a) lo) as [El|El]; [exfalso; lia|].
    destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)) as [Er|Er]; [|exfalso; lia].
    cbn [app]. rewrite Z.max_l by lia. replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
    rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma maps_subtract_keeps : forall l (b s : word) lo hi,
  lo < hi -> 0 < bv_unsigned s -> In (b, s) l ->
  (bv_unsigned b + bv_unsigned s <= lo \/ hi <= bv_unsigned b) ->
  In (b, s) (maps_subtract l lo hi).
Proof.
  induction l as [|[a sz] l IH]; intros b s lo hi Hlh Hs Hin Hd; [destruct Hin|].
  cbn [maps_subtract]. apply in_app_iff. destruct Hin as [Heq|Hin].
  - injection Heq as -> ->. left. rewrite (iv_subtract_disjoint b s lo hi Hlh Hs Hd). left. reflexivity.
  - right. apply IH; assumption.
Qed.

(* [comment removed for export] *)

Lemma page_in_ranges_cons : forall p iv l,
  page_in_ranges p (iv :: l)
  = (((bv_unsigned (fst iv) <=? bv_unsigned p) && (bv_unsigned p + page_size <=? bv_unsigned (fst iv) + bv_unsigned (snd iv)))
     || page_in_ranges p l)%bool.
Proof. reflexivity. Qed.

Lemma page_in_ranges_app : forall p l1 l2,
  page_in_ranges p (l1 ++ l2) = (page_in_ranges p l1 || page_in_ranges p l2)%bool.
Proof. intros. unfold page_in_ranges. apply existsb_app. Qed.

Lemma page_in_ranges_true : forall p l,
  page_in_ranges p l = true <->
  exists iv, In iv l /\ bv_unsigned (fst iv) <= bv_unsigned p /\ bv_unsigned p + page_size <= bv_unsigned (fst iv) + bv_unsigned (snd iv).
Proof.
  intros p l. unfold page_in_ranges. rewrite existsb_exists. split.
  - intros [iv [Hin Hb]]. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. eauto.
  - intros (iv & Hin & H1 & H2). exists iv. split; [exact Hin|]. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

Lemma page_in_ranges_false : forall p l,
  page_in_ranges p l = false <->
  forall iv, In iv l -> ~ (bv_unsigned (fst iv) <= bv_unsigned p /\ bv_unsigned p + page_size <= bv_unsigned (fst iv) + bv_unsigned (snd iv)).
Proof.
  intros p l. split.
  - intros H iv Hin Hc. assert (T : page_in_ranges p l = true) by (apply (proj2 (page_in_ranges_true p l)); exists iv; tauto). congruence.
  - intros H. destruct (page_in_ranges p l) eqn:E; [|reflexivity]. exfalso.
    apply page_in_ranges_true in E as (iv & Hin & H1 & H2). exact (H iv Hin (conj H1 H2)).
Qed.

(* [comment removed for export] *)
Lemma page_in_ranges_covers : forall p l z,
  page_in_ranges p l = true -> bv_unsigned p <= z < bv_unsigned p + page_size -> in_ivs z l = true.
Proof.
  intros p l z Hp Hz. apply page_in_ranges_true in Hp as (iv & Hin & H1 & H2).
  apply (proj2 (in_ivs_true' z l)). exists iv. split; [exact Hin | lia].
Qed.

(* [comment removed for export] *)
Lemma page_in_ranges_subtract_out : forall (p : word) l lo hi,
  ivs_wf l -> lo <= hi ->
  (bv_unsigned p + page_size <= lo \/ hi <= bv_unsigned p) ->
  page_in_ranges p (maps_subtract l lo hi) = page_in_ranges p l.
Proof.
  intros p l lo hi Hwf Hlh Hout. pose proof (u64_range p) as Rp. unfold page_size in *.
  induction l as [|[a sz] l IH]; [reflexivity|].
  apply ivs_wf_cons_inv in Hwf as [Ha Hl]. cbn [maps_subtract]. rewrite page_in_ranges_app, page_in_ranges_cons, (IH Hl). f_equal.
  cbn [fst snd]. unfold iv_wf, B, S in Ha. cbn [fst snd] in Ha.
  pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
  unfold iv_subtract. rewrite page_in_ranges_app.
  destruct (Z.ltb_spec (bv_unsigned a) lo) as [El|El]; destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)) as [Er|Er];
    cbn [page_in_ranges existsb fst snd app orb]; unfold page_size; rewrite ?u64_lit by lia; rewrite ?orb_false_r.
  - (* [comment removed for export] *)
    destruct Hout as [Hout|Hout].
    + destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + Z.min (bv_unsigned sz) (lo - bv_unsigned a)));
      destruct (Z.leb_spec (Z.max (bv_unsigned a) hi) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (Z.max (bv_unsigned a) hi + (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)));
      destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
    + destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + Z.min (bv_unsigned sz) (lo - bv_unsigned a)));
      destruct (Z.leb_spec (Z.max (bv_unsigned a) hi) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (Z.max (bv_unsigned a) hi + (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)));
      destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
  - (* [comment removed for export] *)
    destruct Hout as [Hout|Hout];
    destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + Z.min (bv_unsigned sz) (lo - bv_unsigned a)));
      destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
  - (* [comment removed for export] *)
    destruct Hout as [Hout|Hout];
    destruct (Z.leb_spec (Z.max (bv_unsigned a) hi) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (Z.max (bv_unsigned a) hi + (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)));
      destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
  - (* [comment removed for export] *)
    destruct Hout as [Hout|Hout];
    destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
Qed.

(* [comment removed for export] *)
Lemma page_in_ranges_subtract_in : forall (p : word) l lo hi,
  ivs_wf l -> lo <= bv_unsigned p < hi ->
  page_in_ranges p (maps_subtract l lo hi) = false.
Proof.
  intros p l lo hi Hwf Hp. pose proof (u64_range p) as Rp.
  destruct (page_in_ranges p (maps_subtract l lo hi)) eqn:E; [|reflexivity]. exfalso.
  pose proof (page_in_ranges_covers p _ (bv_unsigned p) E ltac:(unfold page_size; lia)) as C.
  rewrite in_ivs_covered in C.
  destruct (maps_subtract_sem l lo hi Hwf ltac:(lia)) as (_ & _ & Cv). rewrite Cv in C.
  apply andb_prop in C as [_ C]. apply negb_true_iff in C. unfold in_rng in C.
  apply andb_false_iff in C as [C|C]; [apply Z.leb_gt in C | apply Z.ltb_ge in C]; lia.
Qed.

(* [comment removed for export] *)
Lemma page_in_ranges_cons_in : forall (p a n : word) l,
  bv_unsigned a <= bv_unsigned p -> bv_unsigned p + page_size <= bv_unsigned a + bv_unsigned n ->
  page_in_ranges p ((a, n) :: l) = true.
Proof.
  intros p a n l H1 H2. rewrite page_in_ranges_cons. cbn [fst snd]. apply orb_true_iff. left.
  apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

Lemma page_in_ranges_cons_out : forall (p a n : word) l,
  (bv_unsigned p + page_size <= bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned p) ->
  0 < bv_unsigned n ->
  page_in_ranges p ((a, n) :: l) = page_in_ranges p l.
Proof.
  intros p a n l H Hn. rewrite page_in_ranges_cons. cbn [fst snd]. unfold page_size in *.
  destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned n)); cbn; try reflexivity. exfalso. lia.
Qed.

(* [comment removed for export] *)
Lemma page_base_facts : forall a : word,
  bv_unsigned (page_base a) <= bv_unsigned a /\ bv_unsigned a < bv_unsigned (page_base a) + 4096
  /\ bv_unsigned (page_base a) mod 4096 = 0.
Proof.
  intros a. unfold page_base, page_base_of, page_size. pose proof (u64_range a) as Ha.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (H : 0 <= bv_unsigned a / 4096 * 4096 <= bv_unsigned a) by lia.
  rewrite u64_lit by lia. split; [lia|]. split; [lia|]. rewrite Z.mod_mul by lia. reflexivity.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma page_of_byte_in_aligned : forall (x : word) lo hi,
  lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= bv_unsigned x < hi ->
  lo <= bv_unsigned (page_base x) /\ bv_unsigned (page_base x) + 4096 <= hi.
Proof.
  intros x lo hi Hlo Hhi Hx. pose proof (page_base_facts x) as (P1 & P2 & P3).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma page_of_byte_out_aligned : forall (x : word) lo hi,
  lo mod 4096 = 0 -> hi mod 4096 = 0 -> (bv_unsigned x < lo \/ hi <= bv_unsigned x) ->
  bv_unsigned (page_base x) + 4096 <= lo \/ hi <= bv_unsigned (page_base x).
Proof.
  intros x lo hi Hlo Hhi Hx. pose proof (page_base_facts x) as (P1 & P2 & P3).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zfill_in : forall (a n : word) m (x : word),
  bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n -> zfill a n m x = Some (Z_to_bv 8 0).
Proof.
  intros a n m x Hx. unfold zfill, zmem.
  rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma unfill_in : forall (a n : word) m (x : word),
  bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n -> unfill a n m x = None.
Proof.
  intros a n m x Hx. unfold unfill.
  rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma mrestrict_at : forall (H : word -> bool) M (x : word),
  mrestrict H M x = if H x then None else M x.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma v_addi_pc : forall p, 0 <= p -> p + 4 < 2 ^ 64 -> v_addi (Z_to_bv 64 p) 4 = Z_to_bv 64 (p + 4).
Proof. intros p H0 H4. unfold v_addi. rewrite u64_lit by lia. reflexivity. Qed.

Lemma is_ecall_at_sound : forall SEGS cs, is_ecall_at SEGS cs = true ->
  exists w, fetch_word SEGS (Z_to_bv 64 (pc cs)) = Some w /\ is_ecall w = true /\ 0 <= pc cs /\ pc cs + 4 < 2 ^ 64.
Proof.
  intros SEGS cs H. unfold is_ecall_at in H.
  apply andb_prop in H as [H Hf]. apply andb_prop in H as [H0 H4]. apply Z.leb_le in H0. apply Z.ltb_lt in H4.
  destruct (fetch_word SEGS (Z_to_bv 64 (pc cs))) as [w|] eqn:Hw; [|discriminate].
  exists w. unfold two64 in H4. auto.
Qed.

Lemma page_up_eq : forall len, page_up len = page_round_up_Z len.
Proof. intros. unfold page_up, page_round_up_Z, page_size. f_equal. f_equal. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma env_agree_le' : forall b b' E E', env_agree b' E E' -> (b <= b')%nat -> env_agree b E E'.
Proof. intros b b' E E' [H1 H2] Hle. split; [|exact H2]. intros n Hn. apply H1. lia. Qed.

Lemma env_agree_refl' : forall b E, env_agree b E E.
Proof. intros. split; [intros; reflexivity | reflexivity]. Qed.

Lemma env_agree_trans' : forall b E1 E2 E3, env_agree b E1 E2 -> env_agree b E2 E3 -> env_agree b E1 E3.
Proof. intros b E1 E2 E3 [A1 B1] [A2 B2]. split; [intros n Hn; rewrite A1 by lia; apply A2; lia | congruence]. Qed.

Lemma ext1_agree'' : forall E v a, env_agree v E (ext1 E v a).
Proof.
  intros E v a. split; [|reflexivity]. intros n Hn. cbn [ext1 ev].
  destruct (Nat.eqb_spec n v); [lia | reflexivity].
Qed.

Lemma nth_sr_vars_lt' : forall b sr r, AP.sr_vars_lt b sr = true -> (r < 32)%nat -> AP.expr_vars_lt b (nth r sr (ELit 0)) = true.
Proof.
  intros b sr. induction sr as [|x t IH]; intros r H Hr; [destruct r; reflexivity|].
  cbn [AP.sr_vars_lt] in H. apply andb_prop in H as [H1 H2]. destruct r as [|r]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.

Lemma elenZ_lit'' : forall E z, 0 <= z < 2 ^ 64 -> elenZ E (ELit z) = z.
Proof. intros E z Hz. unfold elenZ. cbn [edenot]. rewrite u64_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma aluop_eqb_refl : forall o, aluop_eqb o o = true.
Proof. intros []; reflexivity. Qed.
Lemma mulop_eqb_refl : forall o, mulop_eqb o o = true.
Proof. intros []; reflexivity. Qed.
Lemma expr_eqb_refl : forall e, expr_eqb e e = true.
Proof.
  induction e; cbn; rewrite ?aluop_eqb_refl, ?mulop_eqb_refl, ?IHe1, ?IHe2, ?IHe, ?Z.eqb_refl, ?Nat.eqb_refl, ?Bool.eqb_reflx; reflexivity.
Qed.
Lemma amap_eqb_refl : forall m, amap_eqb m m = true.
Proof. intros [b l k]. unfold amap_eqb. cbn. rewrite !expr_eqb_refl. destruct k; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma seps_filter : forall f l, seps l -> seps (List.filter f l).
Proof.
  intros f l H. induction H as [|p l Hf Hl IH]; cbn; [constructor|].
  destruct (f p); [|exact IH]. constructor; [|exact IH].
  apply Forall_forall. intros q Hq. apply filter_In in Hq as [Hq _]. exact (proj1 (Forall_forall _ _) Hf q Hq).
Qed.

Lemma sum_sizes_filter_le : forall f l, sum_sizes (List.filter f l) <= sum_sizes l.
Proof.
  intros f l. induction l as [|[b s] l IH]; cbn; [lia|]. pose proof (u64_range s). destruct (f (b, s)); cbn; lia.
Qed.

Lemma A_bytes_app' : forall l1 l2, A_bytes (l1 ++ l2) = A_bytes l1 + A_bytes l2.
Proof. intros l1 l2. induction l1; cbn [A_bytes app]; [lia|]. rewrite IHl1. lia. Qed.

Lemma A_bytes_flat_map_split : forall {T} (f : T -> list (Z * Z)) (g : T -> bool) l r,
  A_bytes (flat_map f (List.filter g l ++ (List.filter (fun x => negb (g x)) l ++ r))) = A_bytes (flat_map f (l ++ r)).
Proof.
  intros T f g l r. rewrite !flat_map_app, !A_bytes_app'. induction l as [|x l IH]; cbn; [lia|].
  destruct (g x); cbn; rewrite !A_bytes_app'; lia.
Qed.

Lemma in_flat_map_split : forall {T U} (f : T -> list U) (g : T -> bool) l r y,
  In y (flat_map f (List.filter g l ++ (List.filter (fun x => negb (g x)) l ++ r))) <-> In y (flat_map f (l ++ r)).
Proof.
  intros T U f g l r y. rewrite !in_flat_map. split.
  - intros (x & Hx & Hy). exists x. split; [|exact Hy]. apply in_app_iff in Hx as [Hx|Hx]; [apply filter_In in Hx as [Hx _]; apply in_app_iff; left; exact Hx|].
    apply in_app_iff in Hx as [Hx|Hx]; [apply filter_In in Hx as [Hx _]; apply in_app_iff; left; exact Hx|]. apply in_app_iff; right; exact Hx.
  - intros (x & Hx & Hy). exists x. split; [|exact Hy]. apply in_app_iff in Hx as [Hx|Hx].
    + destruct (g x) eqn:E; [apply in_app_iff; left; apply filter_In; auto|].
      apply in_app_iff; right. apply in_app_iff; left. apply filter_In. rewrite E. auto.
    + apply in_app_iff; right. apply in_app_iff; right. exact Hx.
Qed.

Lemma sum_count_filter_le : forall (P P' : Z -> bool) (f : word * word -> bool) l,
  (forall q, In q l -> f q = true -> forall x, B q <= x < B q + S q -> P' x = P x) ->
  sum_count P' (List.filter f l) <= sum_count P l.
Proof.
  intros P P' f l H. induction l as [|q l IH]; cbn; [lia|].
  assert (IH' := IH ltac:(intros q' Hq'; apply H; right; exact Hq')).
  destruct (f q) eqn:E; cbn; [|unfold iv_count in *; pose proof (zcount_nonneg P (B q) (Z.to_nat (S q))); lia].
  unfold iv_count in *. rewrite (zcount_ext P' P); [lia|].
  intros x Hx. apply (H q (or_introl eq_refl) E). pose proof (S_range q). rewrite Z2Nat.id in Hx by lia. lia.
Qed.

Lemma filter_map_ext : forall {T U} (h : T -> U) (f : U -> bool) (f' : T -> bool) l,
  (forall x, In x l -> f (h x) = f' x) -> List.filter f (map h l) = map h (List.filter f' l).
Proof.
  intros T U h f f' l H. induction l as [|x l IH]; cbn; [reflexivity|].
  rewrite (H x (or_introl eq_refl)). rewrite (IH ltac:(intros y Hy; apply H; right; exact Hy)).
  destruct (f' x); reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


Lemma mmap_flags_core_22 : mmap_flags_core (Z_to_bv 64 34) = 34%Z.       Proof. vm_compute. reflexivity. Qed.
Lemma mmap_flags_core_32 : mmap_flags_core (Z_to_bv 64 50) = 50%Z.       Proof. vm_compute. reflexivity. Qed.
Lemma mmap_flags_core_4022 : mmap_flags_core (Z_to_bv 64 16418) = 34%Z.  Proof. vm_compute. reflexivity. Qed.
Lemma mmap_flags_core_4032 : mmap_flags_core (Z_to_bv 64 16434) = 50%Z.  Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_22 : mmap_noreserve_b (Z_to_bv 64 34) = false.   Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_32 : mmap_noreserve_b (Z_to_bv 64 50) = false.   Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_4022 : mmap_noreserve_b (Z_to_bv 64 16418) = true. Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_4032 : mmap_noreserve_b (Z_to_bv 64 16434) = true. Proof. vm_compute. reflexivity. Qed.

Lemma with_mmap_backing_plain : forall flags a n m,
  mmap_noreserve_b flags = false -> with_mmap_backing flags a n m = m.
Proof. intros flags a n m H. unfold with_mmap_backing. now rewrite H. Qed.

Lemma with_mmap_backing_lazy : forall flags a n m,
  mmap_noreserve_b flags = true -> with_mmap_backing flags a n m = vm_add_lazy a n m.
Proof. intros flags a n m H. unfold with_mmap_backing. now rewrite H. Qed.

Lemma with_mmap_backing_halted : forall flags a n m,
  m_halted (with_mmap_backing flags a n m) = m_halted m.
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

Lemma with_mmap_backing_fs : forall flags a n m,
  m_fs (with_mmap_backing flags a n m) = m_fs m.
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

Lemma with_mmap_backing_vmmaps : forall flags a n m,
  m_vmmaps (with_mmap_backing flags a n m) = m_vmmaps m.
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

(* [comment removed for export] *)
Lemma mmap_gates_core34 : forall flags,
  mmap_flags_core flags = 34%Z ->
  mmap_modeled_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = true
  /\ mmap_modeled_b (Z_to_bv 64 0) flags (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b (Z_to_bv 64 0) flags (Z_to_bv 64 0) = true.
Proof.
  intros flags Hc. unfold mmap_modeled_b, mmap_noaccess_b. rewrite Hc.
  repeat split; vm_compute; reflexivity.
Qed.

Lemma mmap_gates_core50 : forall flags prot,
  mmap_flags_core flags = 50%Z ->
  mmap_modeled_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_noaccess_b (Z_to_bv 64 0) flags (Z_to_bv 64 0) = true
  /\ mmap_fixed_noaccess_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_rw_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = true.
Proof.
  intros flags prot Hc. unfold mmap_modeled_b, mmap_noaccess_b, mmap_fixed_noaccess_b, mmap_fixed_rw_b.
  rewrite Hc. repeat split; try (vm_compute; reflexivity).
  all: destruct (bv_unsigned prot =? _)%Z; vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma region_free_not_contains : forall l (lo n : word),
  (0 < bv_unsigned n)%Z ->
  region_free l lo n = true -> map_contains l lo n = false.
Proof.
  intros l lo n Hn Hfree. unfold map_contains.
  apply Bool.not_true_iff_false. intros H. apply existsb_exists in H as ([b s] & Hin & H).
  cbn [fst snd] in H. apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (State.region_free_In _ _ _ _ _ Hfree Hin) as Hov.
  unfold iv_overlap in Hov. apply andb_false_iff in Hov as [Hov|Hov]; apply Z.ltb_ge in Hov; lia.
Qed.

Lemma mmap_errnos_ENOMEM : forall e, In e mmap_errnos -> e = ENOMEM.
Proof. intros e [<-|[]]. reflexivity. Qed.
Lemma mprotect_errnos_ENOMEM : forall e, In e mprotect_errnos -> e = ENOMEM.
Proof. intros e [<-|[]]. reflexivity. Qed.

Lemma errno_ret_ENOMEM : errno_ret ENOMEM = Z_to_bv 64 (two64 - 12).
Proof. apply bv_eq. reflexivity. Qed.
End WithFP1.


Section OurSpecNodes.
Context {fx : FPState}.
Variable segs : list Segment.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stepacc_ecall_epend : forall regs pc mem rom w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom)
  = MachineOk (@mkAccessReport machine_state (epend regs pc mem rom (getr regs 17)) []).
Proof.
  intros regs pc mem rom w Hfetch Hecall.
  unfold RiscvSemantics.step_accesses. cbn [ms_pc ms_pc_val mkst].
  rewrite Hfetch. cbv beta iota.
  unfold RiscvSemantics.decode_exec_accesses. rewrite Hecall. cbv beta iota.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma node_instr_noacc : forall ms model ms',
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' []) ->
  ShapeAlg.node_ok segs (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
  intros ms model ms' Hh Hsvc Hstep.
  assert (Hacc : mi_account_step segs ms model = MachineOk (ms', model)).
  { unfold mi_account_step. rewrite Hstep. cbn [accessed_ranges access_value].
    rewrite materialize_model_accesses_nil. reflexivity. }
  apply node_ok_of_transparent; [| apply transparent_instr; exact Hsvc].
  split.
  - intros []. apply (sstep_instr segs ms model ms' model Hh Hsvc Hacc).
  - intros e st Hss. exists tt.
    inversion Hss; subst;
      match goal with
      | H : mi_account_step segs ms model = _ |- _ => rewrite Hacc in H; try discriminate; injection H as <- <-; split; reflexivity
      | H : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in H; discriminate
      end.
Qed.

Lemma srz_sys_lazy : forall regs pc mem rom model w T,
  m_halted model = None ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  srealizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros regs pc mem rom model w T Hh HF HE Hc.
  eapply srz_silent1; [| exact Hc].
  apply node_instr_noacc; [exact Hh | reflexivity | eapply stepacc_ecall_epend; eassumption].
Qed.

(* [comment removed for export] *)
Lemma node_chk_ev_mat : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
  (forall i, ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model (effs i)) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     spec_step_ok (sys_input segs ms x8) model (Ok eff m' ev) ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, syscall_effect_accesses (effs i) = []) ->
  ShapeAlg.node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hns Hinv Hnu Hh' Hacc. split.
  - intros i. apply (sstep_cfg_syscall segs ACFG ms model x8 (effs i) (ms' i) (ms' i) (evs i) Hh Hsvc).
    + apply check_syscall_ok_iff. apply Hok.
    + apply Hns.
    + apply Hh'.
    + rewrite (Hacc i). apply materialize_model_accesses_nil.
  - intros e st Hss.
    destruct (sstep_cfg_sys_inv_acfg segs ms model x8 e st Hsvc Hss)
      as [(eff & m' & ev & [Hsp Hok'] & Hh2 & Hm) | [(eff & m' & ev & code' & [Hsp Hok'] & Hh2 & _)
         | [(eff & m' & ev & sig & [Hsp Hok'] & Hk & _) | ([Hsp _] & -> & ->)]]].
    + apply check_syscall_ok_iff in Hsp. destruct (Hinv _ _ _ Hsp Hok') as (i & -> & -> & ->).
      rewrite (Hacc i), materialize_model_accesses_nil in Hm. destruct Hm as [-> ->].
      exists i. split; reflexivity.
    + apply check_syscall_ok_iff in Hsp. destruct (Hinv _ _ _ Hsp Hok') as (i & -> & -> & ->).
      rewrite Hh' in Hh2. discriminate.
    + apply check_syscall_ok_iff in Hsp. destruct (Hinv _ _ _ Hsp Hok') as (i & -> & -> & ->).
      rewrite (m_killed_of_m_halted_none _ (Hh' i)) in Hk. discriminate.
    + exfalso. apply (check_syscall_err_iff _ (mkEffect (Z_to_bv 64 0) [] [])) in Hsp. exact (Hnu _ Hsp).
Qed.

Lemma node_chk_ev_mat_mm : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event) (i0 : I),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  injected_family_off ACFG (sys_input segs ms x8) = true ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
  (forall i, refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = false) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     (refusal_b (sys_input segs ms x8) model (eff_ret eff) = true /\ m_halted m' = m_halted model)
     \/ exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, syscall_effect_accesses (effs i) = []) ->
  ShapeAlg.node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs i0 Hh Hsvc Hoff Hok Hnr Hinv Hnu Hh' Hacc.
  apply (node_chk_ev_mat ms model x8 I effs ms' evs Hh Hsvc Hok).
  - intros i. apply spurious_refusal_not_refusal. apply Hnr.
  - intros eff m' ev Hc Hstep. destruct (Hinv eff m' ev Hc) as [[Hr Hhm] | X]; [exfalso | exact X].
    rewrite Hh in Hhm.
    exact (spec_step_ok_refuted _ model eff m' ev (effs i0) (ms' i0) (evs i0) Hoff
             (proj1 (check_syscall_ok_iff _ _ _ _ _) (Hok i0)) (Hnr i0) Hr Hhm Hstep).
  - exact Hnu.
  - exact Hh'.
  - exact Hacc.
Qed.

Lemma refusal_b_mmap : forall ms x8 model r, bv_unsigned x8 = 222%Z ->
  refusal_b (sys_input segs ms x8) model r = errno_ret_in mmap_errnos r.
Proof.
  intros ms x8 model r Hno. rewrite errno_ret_in_eq. apply refusal_b_222. rewrite in_sysno_sys_input. exact Hno.
Qed.

Lemma refusal_b_mprotect : forall ms x8 model r, bv_unsigned x8 = 226%Z ->
  refusal_b (sys_input segs ms x8) model r = errno_ret_in mprotect_errnos r.
Proof.
  intros ms x8 model r Hno. rewrite errno_ret_in_eq. apply refusal_b_226. rewrite in_sysno_sys_input. exact Hno.
Qed.

Lemma family_off_mmap : forall ms x8, bv_unsigned x8 = 222%Z -> injected_family_off ACFG (sys_input segs ms x8) = true.
Proof. intros ms x8 Hno. apply acfg_family_off_222. rewrite in_sysno_sys_input. exact Hno. Qed.

Lemma family_off_mprotect : forall ms x8, bv_unsigned x8 = 226%Z -> injected_family_off ACFG (sys_input segs ms x8) = true.
Proof. intros ms x8 Hno. apply acfg_family_off_226. rewrite in_sysno_sys_input. exact Hno. Qed.

Lemma grant_na_not_mmap_errno : forall hint model a n,
  (0 <= n)%Z -> grant_ok_na hint model a n = true -> errno_ret_in mmap_errnos a = false.
Proof. intros hint model a n Hn Hg. exact (grant_na_not_errno hint model a n Hn Hg). Qed.

(* [comment removed for export] *)
Lemma epend_len : forall regs pc mem rom (len : Z),
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  bv_unsigned (ms_gpr (epend regs pc mem rom (getr regs 17)) 1) = len
  /\ ms_gpr (epend regs pc mem rom (getr regs 17)) 1 <> Z_to_bv 64 0.
Proof.
  intros regs pc mem rom len H11 Hlen. rewrite ms_gpr_epend1, H11. split.
  - apply u64_lit. lia.
  - intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma errno_ret_in_nil' : forall r, errno_ret_in [] r = false.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma srz_family : forall c (I : Type) (nx : I -> config) (B : TSet) (i0 : I),
  ShapeAlg.node_ok segs c I (fun _ => []) nx ->
  (forall i, srealizes segs (nx i) B) ->
  srealizes segs c B.
Proof. intros c I nx B i0 Hn HB. exact (srz_silent_family segs c I nx B i0 Hn HB). Qed.

Lemma mmap_rw_check : forall ms x8 model eff flags,
  bv_unsigned x8 = 222%Z ->
  ms_gpr ms 1 <> Z_to_bv 64 0 -> ms_gpr ms 2 = Z_to_bv 64 3 ->
  ms_gpr ms 3 = flags -> mmap_flags_core flags = 34%Z ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] zs [] [] [] =>
        if errno_ret_in mmap_errnos r
        then match zs with [] => CheckOk model [] | _ => CheckReject end
        else if grant_ok_na_pin model r nZ && mmap_noreserve_backed_ok flags model nZ
                && listNN_eqb zs [(r, Z_to_bv 64 nZ)]
        then CheckOk (with_mmap_backing flags r (Z_to_bv 64 nZ) (mmap_model r (Z_to_bv 64 nZ) model)) []
        else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff flags Hno H1 H2 H3 Hcore H4 H5 nZ.
  destruct (mmap_gates_core34 flags Hcore) as (Gm & _ & _).
  rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
  assert (E1 : w_is0 (ms_gpr ms 1) = false) by (unfold w_is0; apply bv_eqb_neq; exact H1).
  rewrite E1, H2, H3, H5, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl), Gm. cbn [negb]. cbv beta iota zeta. fold nZ.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
  destruct us; [|reflexivity]. destruct cs; [|reflexivity]. destruct ci; [|reflexivity].
  match goal with |- context [errno_ret_in ?l r] => destruct (errno_ret_in l r); [reflexivity|] end.
  unfold grant_ok_na_pin, mmap_model.
  destruct (mmap_noreserve_backed_ok flags model nZ); rewrite ?andb_true_r, ?andb_false_r; [reflexivity|].
  cbn [andb]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma vm_base_ok_of_pin : forall model a nZ,
  grant_ok_na_pin model a nZ = true -> vm_base_ok (m_vmmaps model) nZ a = true.
Proof. intros model a nZ H. exact H. Qed.

(* [comment removed for export] *)
Lemma srz_mmap_rw1 : forall regs (pc : word) mem rom model w (len : Z) (flags : word) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = flags -> mmap_flags_core flags = 34%Z ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  (exists a, grant_ok_na_pin model a nZ = true /\ mmap_noreserve_backed_ok flags model nZ = true) ->
  (forall a, grant_ok_na_pin model a nZ = true -> mmap_noreserve_backed_ok flags model nZ = true ->
     srealizes segs (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (zfill a n mem) rom)
                          (with_mmap_backing flags a n (mmap_model a n model))) KB) ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w len flags KB HF HE Hh H17 H11 Hlen H12 H13 Hcore H14 H15 nZ n (a0 & Ha0 & Hb0) HB.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  destruct (epend_len regs pc mem rom len H11 Hlen) as [Hl1 Hne1]. fold ms in Hl1, Hne1.
  pose proof (fun eff => mmap_rw_check ms (getr regs 17) model eff flags Hno Hne1
                           ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                           ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13) Hcore
                           ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                           ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15)) as Hchk.
  cbv zeta in Hchk. rewrite Hl1 in Hchk. fold nZ n in Hchk.
  rewrite Hb0 in Hchk.
  assert (Hn0 : (0 <= nZ)%Z) by (unfold nZ; apply page_round_up_Z_nonneg; lia).
  assert (HnZpos : (0 < nZ)%Z) by (unfold nZ; apply page_round_up_Z_pos'; lia).
  (* [comment removed for export] *)
  pose (IB := {a : word | grant_ok_na_pin model a nZ = true}).
  pose (effs := fun i : IB => match i with
                           | exist _ a _ => mkEffectU a [] [(a, n)] [] [] [] end).
  pose (ms' := fun i : IB => match i with
                          | exist _ a _ => with_mmap_backing flags a n (mmap_model a n model) end).
  eapply (srz_family (mkCfg ms model) IB
            (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) KB
            (exist _ a0 Ha0)).
  - apply (node_chk_ev_mat_mm ms model (getr regs 17) IB effs ms' (fun _ => []) (exist _ a0 Ha0) Hh eq_refl
             (family_off_mmap ms _ Hno)).
    + intros [a Ha]; cbn [effs ms']; rewrite Hchk.
      rewrite (grant_na_pin_not_errno model a nZ Hn0 Ha), Ha. cbn [andb].
      rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros [a Ha]; cbn [effs eff_ret]. rewrite (refusal_b_mmap ms _ model a Hno).
      exact (grant_na_pin_not_errno model a nZ Hn0 Ha).
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      { left. cbn [eff_ret]. rewrite (refusal_b_mmap ms _ model r Hno). split; [exact Er|]. destruct zs; [|discriminate]. injection Hc as <- <-. reflexivity. }
      right.
      destruct (grant_ok_na_pin model r nZ) eqn:Hg; [|discriminate].
      cbn [andb] in Hc.
      destruct (listNN_eqb zs [(r, n)]) eqn:Hl; [|discriminate].
      apply listNN_eqb_eq in Hl. subst zs. injection Hc as <- <-.
      exists (exist _ r Hg). repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct zs; discriminate|].
      destruct (grant_ok_na_pin model r nZ && true && listNN_eqb zs [(r, n)])%bool; discriminate.
    + intros [a Ha]; cbn [ms']; rewrite with_mmap_backing_halted; unfold mmap_model; rewrite with_vmmaps_halted; exact Hh.
    + intros [a Ha]; reflexivity.
  - intros [a Ha]. cbn [effs ms']. unfold ms. rewrite adv_zeros1_epend. apply HB; [exact Ha | exact Hb0].
Qed.

(* [comment removed for export] *)
Lemma mmap_none_check : forall ms x8 model eff flags,
  bv_unsigned x8 = 222%Z ->
  ms_gpr ms 1 <> Z_to_bv 64 0 -> ms_gpr ms 2 = Z_to_bv 64 0 ->
  ms_gpr ms 3 = flags -> mmap_flags_core flags = 34%Z ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] [] us [] [] =>
        if errno_ret_in mmap_errnos r
        then match us with [] => CheckOk model [] | _ => CheckReject end
        else if grant_ok_na_pin model r nZ && listNN_eqb us [(r, Z_to_bv 64 nZ)]
        then CheckOk (with_mmap_backing flags r (Z_to_bv 64 nZ) (noaccess_model r (Z_to_bv 64 nZ) model)) []
        else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff flags Hno H1 H2 H3 Hcore H4 H5 nZ.
  destruct (mmap_gates_core34 flags Hcore) as (_ & Gm & Gn).
  rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
  assert (E1 : w_is0 (ms_gpr ms 1) = false) by (unfold w_is0; apply bv_eqb_neq; exact H1).
  rewrite E1, H2, H3, H5, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl), Gm, Gn. cbn [negb]. cbv beta iota zeta. fold nZ.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity]. destruct zs; [|reflexivity].
  destruct cs; [|destruct us; reflexivity]. destruct ci; [|destruct us; reflexivity].
  match goal with |- context [errno_ret_in ?l r] => destruct (errno_ret_in l r); [reflexivity|] end.
  unfold grant_ok_na_pin, noaccess_model. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma srz_mmap_none1 : forall regs (pc : word) mem rom model w (len : Z) (flags : word) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = flags -> mmap_flags_core flags = 34%Z ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  (exists a, grant_ok_na_pin model a nZ = true) ->
  (forall a, grant_ok_na_pin model a nZ = true ->
     srealizes segs (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (unfill a n mem) rom)
                          (with_mmap_backing flags a n (noaccess_model a n model))) KB) ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w len flags KB HF HE Hh H17 H11 Hlen H12 H13 Hcore H14 H15 nZ n (a0 & Ha0) HB.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  destruct (epend_len regs pc mem rom len H11 Hlen) as [Hl1 Hne1]. fold ms in Hl1, Hne1.
  pose proof (fun eff => mmap_none_check ms (getr regs 17) model eff flags Hno Hne1
                           ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                           ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13) Hcore
                           ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                           ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15)) as Hchk.
  cbv zeta in Hchk. rewrite Hl1 in Hchk. fold nZ n in Hchk.
  assert (Hn0 : (0 <= nZ)%Z) by (unfold nZ; apply page_round_up_Z_nonneg; lia).
  assert (HnZpos : (0 < nZ)%Z) by (unfold nZ; apply page_round_up_Z_pos'; lia).
  pose (IB := {a : word | grant_ok_na_pin model a nZ = true}).
  pose (effs := fun i : IB => match i with
                           | exist _ a _ => mkEffectU a [] [] [(a, n)] [] [] end).
  pose (ms' := fun i : IB => match i with
                          | exist _ a _ => with_mmap_backing flags a n (noaccess_model a n model) end).
  eapply (srz_family (mkCfg ms model) IB
            (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) KB
            (exist _ a0 Ha0)).
  - apply (node_chk_ev_mat_mm ms model (getr regs 17) IB effs ms' (fun _ => []) (exist _ a0 Ha0) Hh eq_refl
             (family_off_mmap ms _ Hno)).
    + intros [a Ha]; cbn [effs ms']; rewrite Hchk.
      rewrite (grant_na_pin_not_errno model a nZ Hn0 Ha), Ha. cbn [andb].
      rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros [a Ha]; cbn [effs eff_ret]. rewrite (refusal_b_mmap ms _ model a Hno).
      exact (grant_na_pin_not_errno model a nZ Hn0 Ha).
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      { left. cbn [eff_ret]. rewrite (refusal_b_mmap ms _ model r Hno). split; [exact Er|]. destruct us; [|discriminate]. injection Hc as <- <-. reflexivity. }
      right.
      destruct (grant_ok_na_pin model r nZ) eqn:Hg; [|discriminate].
      destruct (listNN_eqb us [(r, n)]) eqn:Hl; [|discriminate].
      apply listNN_eqb_eq in Hl. subst us. injection Hc as <- <-.
      exists (exist _ r Hg). repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct us; discriminate|].
      destruct (grant_ok_na_pin model r nZ && listNN_eqb us [(r, n)])%bool; discriminate.
    + intros [a Ha]; cbn [ms']; rewrite with_mmap_backing_halted; unfold noaccess_model; rewrite with_vmmaps_halted; exact Hh.
    + intros [a Ha]; reflexivity.
  - intros [a Ha]. cbn [effs ms']. unfold ms. rewrite adv_unmaps1_epend. apply HB. exact Ha.
Qed.

End OurSpecNodes.


Section OurSpecNodes2.
Context {fx : FPState}.
Variable segs : list Segment.

Lemma mmap_fixed_gate_open : forall (h : VmMaps) (addr : word) (len : Z),
  (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok h ->
  (two_pow_64 <=? bv_unsigned addr + page_round_up_Z len)%Z = false
  /\ negb (bv_unsigned addr + page_round_up_Z len <=? alloc_top h)%Z = false
  /\ negb (bv_unsigned addr mod page_size =? 0)%Z = false
  /\ negb (0 <? bv_unsigned addr)%Z = false
  /\ (len < 2 ^ 64)%Z /\ (0 < page_round_up_Z len < 2 ^ 64)%Z.
Proof.
  intros h addr len Hal Hpos Hlen Hce Hisp. pose proof alloc_ceiling_val.
  pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr).
  repeat split.
  - apply Z.leb_gt. unfold two_pow_64. lia.
  - rewrite (proj2 (Z.leb_le _ _) (alloc_top_ge_of_ceiling _ _ Hisp Hce)). reflexivity.
  - rewrite (proj2 (Z.eqb_eq _ _) Hal). reflexivity.
  - rewrite (proj2 (Z.ltb_lt _ _) Hpos). reflexivity.
  - lia. - lia. - lia.
Qed.

(* [comment removed for export] *)

Lemma mmap_fixed_rw_free_check : forall ms x8 model eff flags (addr : word) (len : Z),
  bv_unsigned x8 = 222%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  ms_gpr ms 2 = Z_to_bv 64 3 -> ms_gpr ms 3 = flags -> mmap_flags_core flags = 50%Z ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] zs [] [] [] =>
        if errno_ret_in mmap_errnos r
        then match zs with [] => CheckOk model [] | _ => CheckReject end
        else if bv_eqb r addr && listNN_eqb zs [(addr, n)] && mmap_noreserve_backed_ok flags model nZ
        then CheckOk (with_mmap_backing flags addr n (mmap_model addr n model)) []
        else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff flags addr len Hno H0 Hal Hpos H1 Hlen Hce Hisp H2 H3 Hcore H4 H5 nZ n Hrf.
  destruct (mmap_fixed_gate_open (m_vmmaps model) addr len Hal Hpos Hlen Hce Hisp) as (G1 & G2 & G3 & G4 & Hlen' & HnZ).
  destruct (mmap_gates_core50 flags (Z_to_bv 64 3) Hcore) as (Gm & Gn & _ & Gfn & Gfr).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
  assert (E1 : w_is0 (ms_gpr ms 1) = false).
  { unfold w_is0. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E.
    rewrite Hu1 in E. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
  rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
  rewrite E1, H2, H3, H5, H0, Hu1, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl), Gm, Gn, Gfn, Gfr. cbn [negb]. cbv beta iota zeta.
  rewrite G1, G2, G3, G4. fold nZ. fold n.
  assert (Hmc : map_contains (vm_maps (m_vmmaps model)) addr n = false).
  { apply region_free_not_contains; [unfold n; rewrite u64_lit by lia; lia|].
    rewrite RefNodes.region_free_app in Hrf. apply andb_true_iff in Hrf. tauto. }
  rewrite Hmc, andb_false_r, Hrf.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
  Ltac kill_arm zs r := first [ reflexivity | destruct zs; reflexivity
                             | match goal with |- context [errno_ret_in ?l r] =>
                                 destruct (errno_ret_in l r); first [reflexivity | destruct zs; reflexivity] end ].
  destruct us; [|kill_arm zs r].
  destruct cs; [|kill_arm zs r]. destruct ci; [|kill_arm zs r].
  unfold mmap_model. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma srz_mmap_fixed_rw_free1 : forall regs (pc : word) mem rom model w (addr : word) (len : Z) (flags : word) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = flags -> mmap_flags_core flags = 50%Z ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  mmap_noreserve_backed_ok flags model nZ = true ->
  srealizes segs (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (zfill addr n mem) rom)
                       (with_mmap_backing flags addr n (mmap_model addr n model))) KB ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w addr len flags KB HF HE Hh H17 H10 Hal Hpos H11 Hlen Hce Hisp H12 H13 Hcore H14 H15
         nZ n Hrf Hbk HB.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  pose proof (fun eff => mmap_fixed_rw_free_check ms (getr regs 17) model eff flags addr len Hno
                ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
                ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Hce Hisp
                ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13) Hcore
                ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15) Hrf) as Hchk.
  cbv zeta in Hchk. fold nZ in Hchk. fold n in Hchk. rewrite Hbk in Hchk.
  assert (Hne : errno_ret_in mmap_errnos addr = false) by (rewrite errno_ret_in_eq; apply ret_in_errnos_ENOMEM_aligned; exact Hal).
  destruct (mmap_fixed_gate_open (m_vmmaps model) addr len Hal Hpos Hlen Hce Hisp) as (_ & _ & _ & _ & _ & HnZ). fold nZ in HnZ.
  apply (srz_silent1 segs (mkCfg ms model)
           (mkCfg (advance_past_svc (apply_effect ms (mkEffectU addr [] [(addr, n)] [] [] [])))
                  (with_mmap_backing flags addr n (mmap_model addr n model)))).
  - apply (node_chk_ev_mat_mm segs ms model (getr regs 17) unit
             (fun _ => mkEffectU addr [] [(addr, n)] [] [] [])
             (fun _ => with_mmap_backing flags addr n (mmap_model addr n model)) (fun _ => []) tt Hh eq_refl
             (family_off_mmap segs ms _ Hno)).
    + intros []; rewrite Hchk.
      rewrite Hne, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros []; cbn [eff_ret]. rewrite (refusal_b_mmap segs ms _ model addr Hno). exact Hne.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      { left. cbn [eff_ret]. rewrite (refusal_b_mmap segs ms _ model r Hno). split; [exact Er|]. destruct zs; [|discriminate]. injection Hc as <- <-. reflexivity. }
      right.
      destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
      destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
      apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst r zs. cbn [andb] in Hc. injection Hc as <- <-.
      exists tt. repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct zs; discriminate|].
      destruct (bv_eqb r addr && listNN_eqb zs [(addr, n)] && true)%bool; discriminate.
    + intros []; rewrite with_mmap_backing_halted; unfold mmap_model; rewrite with_vmmaps_halted; exact Hh.
    + intros []; reflexivity.
  - unfold ms. rewrite adv_zeros1_epend. exact HB.
Qed.

(* [comment removed for export] *)

Lemma mmap_fixed_none_free_check : forall ms x8 model eff flags (addr : word) (len : Z),
  bv_unsigned x8 = 222%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  ms_gpr ms 2 = Z_to_bv 64 0 -> ms_gpr ms 3 = flags -> mmap_flags_core flags = 50%Z ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] [] us [] [] =>
        if errno_ret_in mmap_errnos r
        then match us with [] => CheckOk model [] | _ => CheckReject end
        else if bv_eqb r addr && listNN_eqb us [(addr, n)]
        then CheckOk (with_mmap_backing flags addr n (noaccess_model addr n model)) []
        else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff flags addr len Hno H0 Hal Hpos H1 Hlen Hce Hisp H2 H3 Hcore H4 H5 nZ n Hrf.
  destruct (mmap_fixed_gate_open (m_vmmaps model) addr len Hal Hpos Hlen Hce Hisp) as (G1 & G2 & G3 & G4 & Hlen' & HnZ).
  destruct (mmap_gates_core50 flags (Z_to_bv 64 0) Hcore) as (Gm & Gn & Gfn & _ & _).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
  assert (E1 : w_is0 (ms_gpr ms 1) = false).
  { unfold w_is0. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E.
    rewrite Hu1 in E. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
  rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
  rewrite E1, H2, H3, H5, H0, Hu1, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl), Gm, Gn, Gfn. cbn [negb]. cbv beta iota zeta.
  rewrite G1, G2, G3, G4. fold nZ. fold n.
  assert (Hmc : map_contains (vm_maps (m_vmmaps model)) addr n = false).
  { apply region_free_not_contains; [unfold n; rewrite u64_lit by lia; lia|].
    rewrite RefNodes.region_free_app in Hrf. apply andb_true_iff in Hrf. tauto. }
  rewrite Hmc, andb_false_r, Hrf.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
  destruct zs; [|reflexivity].
  destruct cs; [|destruct (errno_ret_in mmap_errnos r); [destruct us|]; reflexivity].
  destruct ci; [|destruct (errno_ret_in mmap_errnos r); [destruct us|]; reflexivity].
  unfold noaccess_model. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma srz_mmap_fixed_none_free1 : forall regs (pc : word) mem rom model w (addr : word) (len : Z) (flags : word) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = flags -> mmap_flags_core flags = 50%Z ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  srealizes segs (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (unfill addr n mem) rom)
                       (with_mmap_backing flags addr n (noaccess_model addr n model))) KB ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w addr len flags KB HF HE Hh H17 H10 Hal Hpos H11 Hlen Hce Hisp H12 H13 Hcore H14 H15
         nZ n Hrf HB.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  pose proof (fun eff => mmap_fixed_none_free_check ms (getr regs 17) model eff flags addr len Hno
                ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
                ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Hce Hisp
                ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13) Hcore
                ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15) Hrf) as Hchk.
  cbv zeta in Hchk. fold nZ in Hchk. fold n in Hchk.
  assert (Hne : errno_ret_in mmap_errnos addr = false) by (rewrite errno_ret_in_eq; apply ret_in_errnos_ENOMEM_aligned; exact Hal).
  destruct (mmap_fixed_gate_open (m_vmmaps model) addr len Hal Hpos Hlen Hce Hisp) as (_ & _ & _ & _ & _ & HnZ). fold nZ in HnZ.
  apply (srz_silent1 segs (mkCfg ms model)
           (mkCfg (advance_past_svc (apply_effect ms (mkEffectU addr [] [] [(addr, n)] [] [])))
                  (with_mmap_backing flags addr n (noaccess_model addr n model)))).
  - apply (node_chk_ev_mat_mm segs ms model (getr regs 17) unit
             (fun _ => mkEffectU addr [] [] [(addr, n)] [] [])
             (fun _ => with_mmap_backing flags addr n (noaccess_model addr n model)) (fun _ => []) tt Hh eq_refl
             (family_off_mmap segs ms _ Hno)).
    + intros []; rewrite Hchk. rewrite Hne, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros []; cbn [eff_ret]. rewrite (refusal_b_mmap segs ms _ model addr Hno). exact Hne.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      { left. cbn [eff_ret]. rewrite (refusal_b_mmap segs ms _ model r Hno). split; [exact Er|]. destruct us; [|discriminate]. injection Hc as <- <-. reflexivity. }
      right.
      destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
      destruct (listNN_eqb us [(addr, n)]) eqn:Hl; [|discriminate].
      apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst r us. injection Hc as <- <-.
      exists tt. repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct us; discriminate|].
      destruct (bv_eqb r addr && listNN_eqb us [(addr, n)])%bool; discriminate.
    + intros []; rewrite with_mmap_backing_halted; unfold noaccess_model; rewrite with_vmmaps_halted; exact Hh.
    + intros []; reflexivity.
  - unfold ms. rewrite adv_unmaps1_epend. exact HB.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma srz_mprotect1 : forall regs (pc : word) mem rom model w (addr : word) (len : Z) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 226 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  getr regs 12 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  mprotect_budget_ok model addr n = true ->
  srealizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (zfill addr n mem) rom)
                       (mprotect_model addr n model)) KB ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w addr len KB HF HE Hh H17 H10 Hal H11 Hlen Hnw H12 n Hna Hma Hbud HB.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 226%Z) by (rewrite H17; apply u64_lit; lia).
  pose proof (fun eff => mprotect_check segs ms (getr regs 17) model eff addr len Hno
                           ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal
                           ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Hnw
                           ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12) Hna Hma) as Hchk.
  cbv zeta in Hchk. fold n in Hchk. rewrite Hbud in Hchk.
  assert (Hne : errno_ret_in mprotect_errnos (Z_to_bv 64 0) = false) by reflexivity.
  apply (srz_silent1 segs (mkCfg ms model)
           (mkCfg (advance_past_svc (apply_effect ms (mkEffectU (Z_to_bv 64 0) [] [(addr, n)] [] [] [])))
                  (mprotect_model addr n model))).
  - apply (node_chk_ev_mat_mm segs ms model (getr regs 17) unit
             (fun _ => mkEffectU (Z_to_bv 64 0) [] [(addr, n)] [] [] [])
             (fun _ => mprotect_model addr n model) (fun _ => []) tt Hh eq_refl
             (family_off_mprotect segs ms _ Hno)).
    + intros []; rewrite Hchk. rewrite Hne. cbn [andb].
      unfold w_is0. rewrite bv_eqb_refl. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros []; cbn [eff_ret]. rewrite (refusal_b_mprotect segs ms _ model _ Hno). exact Hne.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|destruct (errno_ret_in mprotect_errnos r); [destruct zs|]; discriminate].
      destruct cs; [|destruct (errno_ret_in mprotect_errnos r); [destruct zs|]; discriminate].
      destruct ci; [|destruct (errno_ret_in mprotect_errnos r); [destruct zs|]; discriminate].
      destruct (errno_ret_in mprotect_errnos r) eqn:Er.
      { left. cbn [eff_ret]. rewrite (refusal_b_mprotect segs ms _ model r Hno). split; [exact Er|]. destruct zs; [|discriminate]. injection Hc as <- <-. reflexivity. }
      right.
      cbn [andb] in Hc. destruct (w_is0 r) eqn:E0; [|discriminate].
      destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
      apply listNN_eqb_eq in Hl. subst zs. injection Hc as <- <-.
      unfold w_is0 in E0. apply bv_eqb_eq in E0. subst r.
      exists tt. repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|destruct (errno_ret_in mprotect_errnos r); [destruct zs|]; discriminate].
      destruct cs; [|destruct (errno_ret_in mprotect_errnos r); [destruct zs|]; discriminate].
      destruct ci; [|destruct (errno_ret_in mprotect_errnos r); [destruct zs|]; discriminate].
      destruct (errno_ret_in mprotect_errnos r); [destruct zs; discriminate|].
      cbn [andb] in Hc. destruct (w_is0 r && listNN_eqb zs [(addr, n)])%bool; discriminate.
    + intros []; unfold mprotect_model; rewrite with_vmmaps_halted; exact Hh.
    + intros []; reflexivity.
  - unfold ms. rewrite adv_zeros1_epend. exact HB.
Qed.

End OurSpecNodes2.
Section WithFP2.
Context {fx : FPState}.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma page_base_aligned' : forall p : word, bv_unsigned p mod 4096 = 0 -> page_base p = p.
Proof.
  intros p Hp. unfold page_base, page_base_of, page_size. apply bv_eq. pose proof (u64_range p).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  rewrite u64_lit; lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma iv_subtract_contained : forall (a sz : word) lo hi,
  bv_unsigned a <= lo -> hi <= bv_unsigned a + bv_unsigned sz -> lo <= hi ->
  iv_subtract a sz lo hi
  = (if bv_unsigned a <? lo then [(a, Z_to_bv 64 (lo - bv_unsigned a))] else [])
    ++ (if hi <? bv_unsigned a + bv_unsigned sz then [(Z_to_bv 64 hi, Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - hi))] else []).
Proof.
  intros a sz lo hi H1 H2 H3. unfold iv_subtract.
  rewrite Z.min_r by lia. rewrite Z.max_r by lia. reflexivity.
Qed.

Lemma map_replace_entry : forall (f : amap -> word * word) l m pcs,
  map f (replace_entry l m pcs) = flat_map (fun m' => if amap_eqb m' m then map f pcs else [f m']) l.
Proof.
  intros f l m pcs. unfold replace_entry. rewrite flat_map_concat_map, concat_map, map_map, <- flat_map_concat_map.
  apply flat_map_ext. intros m'. destruct (amap_eqb m' m); reflexivity.
Qed.

Lemma maps_subtract_map_replace : forall (f : amap -> word * word) l m pcs lo hi,
  (forall m', In m' l -> amap_eqb m' m = false -> iv_subtract (fst (f m')) (snd (f m')) lo hi = [f m']) ->
  (forall m', In m' l -> amap_eqb m' m = true -> iv_subtract (fst (f m')) (snd (f m')) lo hi = map f pcs) ->
  maps_subtract (map f l) lo hi = map f (replace_entry l m pcs).
Proof.
  intros f l m pcs lo hi Hout Hin. rewrite map_replace_entry.
  induction l as [|m' l IH]; [reflexivity|]. cbn [map flat_map maps_subtract].
  destruct (f m') as [a sz] eqn:Ef. cbn [maps_subtract].
  rewrite (IH ltac:(intros x Hx; apply Hout; right; exact Hx) ltac:(intros x Hx; apply Hin; right; exact Hx)). f_equal.
  destruct (amap_eqb m' m) eqn:Heq.
  - rewrite <- (Hin m' (or_introl eq_refl) Heq), Ef. reflexivity.
  - pose proof (Hout m' (or_introl eq_refl) Heq) as X. rewrite Ef in X. cbn [fst snd] in X. exact X.
Qed.

Lemma in_replace_entry : forall l m pcs m',
  In m' (replace_entry l m pcs) -> (In m' l /\ m' <> m) \/ (In m l /\ In m' pcs).
Proof.
  intros l m pcs m' H. unfold replace_entry in H. apply in_flat_map in H as (m0 & Hm0 & Hin).
  destruct (amap_eqb m0 m) eqn:He.
  - apply APS.amap_eqb_eq in He. subst m0. right. auto.
  - destruct Hin as [<-|[]]. left. split; [exact Hm0|]. intros ->. rewrite amap_eqb_refl in He. discriminate.
Qed.

Lemma maps_subtract_in_pieces : forall l (b s : word) lo hi q,
  In (b, s) l -> In q (iv_subtract b s lo hi) -> In q (maps_subtract l lo hi).
Proof.
  induction l as [|[a sz] l IH]; intros b s lo hi q Hin Hq; [destruct Hin|].
  cbn [maps_subtract]. apply in_app_iff. destruct Hin as [Heq|Hin].
  - injection Heq as -> ->. left. exact Hq.
  - right. eapply IH; eassumption.
Qed.

Lemma seps_app_intro : forall l1 l2,
  seps l1 -> seps l2 -> (forall p q, In p l1 -> In q l2 -> iv_disjoint p q) -> seps (l1 ++ l2).
Proof.
  induction l1 as [|p l1 IH]; intros l2 H1 H2 H12; [exact H2|].
  inversion H1 as [|p' l' Hf Hl]; subst. cbn [app]. constructor.
  - apply Forall_app. split; [exact Hf|]. apply Forall_forall. intros q Hq. apply H12; [left; reflexivity | exact Hq].
  - apply IH; [exact Hl | exact H2 |]. intros a b Ha Hb. apply H12; [right; exact Ha | exact Hb].
Qed.

Lemma seps_iv_subtract : forall (a sz : word) lo hi,
  iv_wf (a, sz) -> lo <= hi -> seps (iv_subtract a sz lo hi).
Proof.
  intros a sz lo hi Hwf Hlh. unfold iv_wf, B, S in Hwf. cbn [fst snd] in Hwf.
  pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs. unfold iv_subtract.
  assert (S1 : forall p : word * word, seps [p]) by (intros p; apply seps_cons; [apply Forall_nil | apply seps_nil]).
  destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn [app];
    try apply S1; try apply seps_nil.
  apply seps_cons; [|apply S1]. apply Forall_cons; [|apply Forall_nil].
  unfold iv_disjoint. cbn [fst snd]. rewrite !u64_lit by lia. left. lia.
Qed.

Lemma seps_maps_subtract : forall l lo hi,
  seps l -> ivs_wf l -> lo <= hi -> seps (maps_subtract l lo hi).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi Hs Hwf Hlh; [constructor|].
  apply ivs_wf_cons_inv in Hwf as [Ha Hl]. inversion Hs as [|p' l' Hf Htl]; subst.
  cbn [maps_subtract]. apply seps_app_intro; [apply seps_iv_subtract; assumption | apply IH; assumption |].
  intros p q Hp Hq.
  destruct (iv_subtract_pieces a sz lo hi p Ha Hp) as (P1 & P2 & P3).
  destruct (maps_subtract_pieces l lo hi q Hl Hq) as (r & Hr & Q1 & Q2 & Q3).
  pose proof (proj1 (Forall_forall _ _) Hf r Hr) as D. unfold iv_disjoint in *. cbn [fst snd] in *. lia.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_bounds : forall (a sz : word) lo hi q (ih ce : Z),
  lo mod 4096 = 0 -> hi mod 4096 = 0 ->
  0 < bv_unsigned sz -> bv_unsigned a mod 4096 = 0 -> bv_unsigned sz mod 4096 = 0 ->
  ih <= bv_unsigned a -> bv_unsigned a + bv_unsigned sz <= ce -> ce <= 2 ^ 64 ->
  In q (iv_subtract a sz lo hi) ->
  0 < bv_unsigned (snd q) /\ bv_unsigned (fst q) mod 4096 = 0 /\ bv_unsigned (snd q) mod 4096 = 0
  /\ ih <= bv_unsigned (fst q) /\ bv_unsigned (fst q) + bv_unsigned (snd q) <= ce.
Proof.
  intros a sz lo hi q ih ce Hlo Hhi Hsz Hal Hszl Hih Hce Hce64 Hq.
  pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
  unfold iv_subtract in Hq. apply in_app_iff in Hq as [Hq|Hq].
  - destruct (Z.ltb_spec (bv_unsigned a) lo); [|destruct Hq]. destruct Hq as [<-|[]]. cbn [fst snd].
    rewrite u64_lit by lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    destruct (Z.le_gt_cases (bv_unsigned sz) (lo - bv_unsigned a)); [rewrite Z.min_l by lia | rewrite Z.min_r by lia]; repeat split; try lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  - destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); [|destruct Hq]. destruct Hq as [<-|[]]. cbn [fst snd].
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    destruct (Z.le_gt_cases hi (bv_unsigned a)); [rewrite !Z.max_l by lia | rewrite !Z.max_r by lia]; rewrite !u64_lit by lia; repeat split; try lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma maps_subtract_bounds : forall l lo hi (ih ce : Z),
  lo mod 4096 = 0 -> hi mod 4096 = 0 -> ce <= 2 ^ 64 ->
  Forall (fun iv => 0 < bv_unsigned (snd iv) /\ bv_unsigned (fst iv) mod 4096 = 0 /\ bv_unsigned (snd iv) mod 4096 = 0
                    /\ ih <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= ce) l ->
  Forall (fun iv => 0 < bv_unsigned (snd iv) /\ bv_unsigned (fst iv) mod 4096 = 0 /\ bv_unsigned (snd iv) mod 4096 = 0
                    /\ ih <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= ce) (maps_subtract l lo hi).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi ih ce Hlo Hhi Hce HB; [constructor|].
  apply Forall_cons_iff in HB as [(B1 & B2 & B3 & B4 & B5) HBl]. cbn [fst snd] in B1, B2, B3, B4, B5.
  cbn [maps_subtract]. apply Forall_app. split; [|apply IH; assumption].
  apply Forall_forall. intros q Hq. exact (iv_subtract_bounds a sz lo hi q ih ce Hlo Hhi B1 B2 B3 B4 B5 Hce Hq).
Qed.

Lemma sum_sizes_maps_subtract_le : forall l lo hi, ivs_wf l -> lo <= hi -> sum_sizes (maps_subtract l lo hi) <= sum_sizes l.
Proof.
  intros l lo hi Hwf Hlh. rewrite !sum_sizes_live, !live_bytes_sum_count.
  rewrite (proj1 (proj2 (maps_subtract_sem l lo hi Hwf Hlh))). apply sum_count_mono. intros; reflexivity.
Qed.

Lemma ledger_split_maps_subtract : forall l lo hi K Y, ivs_wf l -> ledger_split l K Y -> ledger_split (maps_subtract l lo hi) K Y.
Proof.
  intros l lo hi K Y Hwf H b s Hin. destruct (maps_subtract_pieces l lo hi (b, s) Hwf Hin) as ([b' s'] & Hr & R1 & R2 & _).
  cbn [fst snd] in R1, R2. destruct (H b' s' Hr); lia.
Qed.

Lemma replace_entry_notin : forall ms m pcs, ~ In m ms -> replace_entry ms m pcs = ms.
Proof.
  intros ms m pcs H. induction ms as [|h t IH]; [reflexivity|]. unfold replace_entry in *. cbn [flat_map].
  destruct (amap_eqb h m) eqn:He.
  - apply APS.amap_eqb_eq in He. subst h. exfalso. apply H. left. reflexivity.
  - cbn [app]. f_equal. apply IH. intros Hin. apply H. right. exact Hin.
Qed.

Lemma maps_subtract_disjoint_id : forall l lo hi,
  lo < hi ->
  (forall iv, In iv l -> 0 < bv_unsigned (snd iv) /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= lo \/ hi <= bv_unsigned (fst iv))) ->
  maps_subtract l lo hi = l.
Proof.
  intros l lo hi Hlh H. induction l as [|[a sz] l IH]; [reflexivity|]. cbn [maps_subtract].
  destruct (H (a, sz) (or_introl eq_refl)) as [P D]. cbn [fst snd] in P, D.
  rewrite (iv_subtract_disjoint a sz lo hi Hlh P D). cbn [app]. f_equal. apply IH. intros iv Hiv. apply H. right. exact Hiv.
Qed.

Lemma maps_match_app_pcs : forall E pcs ms l,
  (forall pc, In pc pcs -> is_fog pc = false) -> maps_match E ms l ->
  maps_match E (pcs ++ ms) (map (amap_den E) pcs ++ l).
Proof.
  intros E pcs ms l Hpf HM. induction pcs as [|pc pcs IH]; [exact HM|]. cbn [app map maps_match].
  rewrite (Hpf pc (or_introl eq_refl)). exists (map (amap_den E) pcs ++ l). split; [reflexivity|].
  apply IH. intros x Hx. apply Hpf. right. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma maps_match_subtract : forall E ms l m pcs lo hi,
  maps_match E ms l -> seps l -> (forall iv, In iv l -> 0 < bv_unsigned (snd iv)) ->
  In m ms -> is_fog m = false -> lo < hi ->
  bv_unsigned (edenot E (am_base m)) <= lo -> hi <= bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) ->
  map (amap_den E) pcs = iv_subtract (edenot E (am_base m)) (edenot E (am_len m)) lo hi ->
  (forall pc, In pc pcs -> is_fog pc = false) ->
  maps_match E (replace_entry ms m pcs) (maps_subtract l lo hi).
Proof.
  intros E ms. induction ms as [|h t IH]; intros l m pcs lo hi HM Hs Hpos Hm Hf Hlh Hc1 Hc2 Hpcs Hpf; [destruct Hm|].
  cbn [maps_match] in HM. unfold replace_entry. cbn [flat_map]. fold (replace_entry t m pcs).
  destruct (is_fog h) eqn:Hfh.
  - assert (He : amap_eqb h m = false).
    { destruct (amap_eqb h m) eqn:He; [|reflexivity]. apply APS.amap_eqb_eq in He. subst h. congruence. }
    rewrite He. cbn [app maps_match]. rewrite Hfh.
    assert (Hmt : In m t) by (destruct Hm as [<-|Hm]; [congruence | exact Hm]).
    destruct HM as [HM | ([a sz] & l' & -> & Hsz & HM)].
    + left. eapply IH; eassumption.
    + right. inversion Hs as [|p l0 Hfa Hl]; subst. cbn [maps_subtract].
      pose proof (proj1 (Forall_forall _ _) Hfa (amap_den E m) (maps_match_In E t l' m HM Hmt Hf)) as D.
      unfold iv_disjoint, amap_den in D. cbn [fst snd] in D.
      rewrite (iv_subtract_disjoint a sz lo hi Hlh (Hpos (a, sz) (or_introl eq_refl)) ltac:(lia)). cbn [app].
      exists (a, sz), (maps_subtract l' lo hi). split; [reflexivity|]. split; [exact Hsz|].
      eapply IH; try eassumption. intros iv Hiv. apply Hpos. right. exact Hiv.
  - destruct HM as (l' & -> & HM). inversion Hs as [|p l0 Hfa Hl]; subst.
    unfold amap_den at 1. cbn [maps_subtract].
    destruct (amap_eqb h m) eqn:He.
    + apply APS.amap_eqb_eq in He. subst h.
      assert (Hnot : ~ In m t).
      { intros Hmt. pose proof (proj1 (Forall_forall _ _) Hfa (amap_den E m) (maps_match_In E t l' m HM Hmt Hf)) as D.
        pose proof (Hpos (amap_den E m) (or_introl eq_refl)) as P. unfold iv_disjoint, amap_den in D, P. cbn [fst snd] in D, P. lia. }
      rewrite (replace_entry_notin t m pcs Hnot). rewrite <- Hpcs.
      rewrite (maps_subtract_disjoint_id l' lo hi Hlh).
      2:{ intros iv Hiv. split; [apply Hpos; right; exact Hiv|].
          pose proof (proj1 (Forall_forall _ _) Hfa iv Hiv) as D. unfold iv_disjoint, amap_den in D. cbn [fst snd] in D. lia. }
      apply maps_match_app_pcs; [exact Hpf | exact HM].
    + assert (Hmt : In m t) by (destruct Hm as [<-|Hm]; [rewrite amap_eqb_refl in He; discriminate | exact Hm]).
      pose proof (proj1 (Forall_forall _ _) Hfa (amap_den E m) (maps_match_In E t l' m HM Hmt Hf)) as D.
      unfold iv_disjoint, amap_den in D. cbn [fst snd] in D.
      pose proof (Hpos _ (or_introl eq_refl)) as P. unfold amap_den in P. cbn [snd] in P.
      rewrite (iv_subtract_disjoint (edenot E (am_base h)) (edenot E (am_len h)) lo hi Hlh P ltac:(lia)). cbn [app maps_match]. rewrite Hfh.
      exists (maps_subtract l' lo hi). split; [reflexivity|].
      eapply IH; try eassumption. intros iv Hiv. apply Hpos. right. exact Hiv.
Qed.
End WithFP2.




(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section BandCover.
Context {fx : FPState}.
Variable A : atable.
(* [comment removed for export] *)
Definition maps_apart (E : env) (ms : list amap) (lo n : Z) : Prop :=
  forall m, In m ms -> is_fog m = false ->
    lo + n <= bv_unsigned (edenot E (am_base m)) \/
    bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= lo.
(* [comment removed for export] *)
Lemma lit_lazy_ivs_In : forall E ms p, In p (lit_lazy_ivs ms) ->
  exists m, In m ms /\ is_fog m = false /\ APS.uE E (am_base m) = fst p /\ APS.uE E (am_len m) = snd p /\ 0 < snd p.
Proof.
  intros E ms p H. unfold lit_lazy_ivs in H. apply in_flat_map in H as [m [Hm Hp]].
  destruct (lit_lazy_iv m) as [[b l]|] eqn:Hl; [|destruct Hp]. destruct Hp as [<-|[]].
  destruct (APS.lit_lazy_iv_sem E m b l Hl) as (F1 & _ & F3 & F4 & _ & F6 & _). exists m. cbn [fst snd]. repeat split; auto.
Qed.
Lemma lit_lazy_ivs_pos : forall ms p, In p (lit_lazy_ivs ms) -> 0 < snd p.
Proof. intros ms p H. destruct (lit_lazy_ivs_In (Env (fun _ => Z_to_bv 64 0) (fun _ => [])) ms p H) as (m & _ & _ & _ & _ & Hp). exact Hp. Qed.
Lemma band_left_le : forall ivs fuel lo, (forall p, In p ivs -> 0 < snd p) -> band_left ivs lo fuel <= lo.
Proof.
  intros ivs fuel. induction fuel as [|f IH]; intros lo HW; cbn [band_left]; [lia|].
  destruct (List.find (fun p => Z.eqb (fst p + snd p) lo) ivs) as [p|] eqn:Hf; [|lia].
  apply find_some in Hf as [Hin Heq]. apply Z.eqb_eq in Heq. pose proof (IH (fst p) HW). pose proof (HW p Hin). lia.
Qed.
Lemma band_right_ge : forall ivs fuel hi, (forall p, In p ivs -> 0 < snd p) -> hi <= band_right ivs hi fuel.
Proof.
  intros ivs fuel. induction fuel as [|f IH]; intros hi HW; cbn [band_right]; [lia|].
  destruct (List.find (fun p => Z.eqb (fst p) hi) ivs) as [p|] eqn:Hf; [|lia].
  apply find_some in Hf as [Hin Heq]. apply Z.eqb_eq in Heq. pose proof (IH (fst p + snd p) HW). pose proof (HW p Hin). lia.
Qed.
Lemma band_left_cover : forall ivs fuel lo x, band_left ivs lo fuel <= x < lo ->
  exists p, In p ivs /\ fst p <= x < fst p + snd p.
Proof.
  intros ivs fuel. induction fuel as [|f IH]; intros lo x Hx; cbn [band_left] in Hx; [lia|].
  destruct (List.find (fun p => Z.eqb (fst p + snd p) lo) ivs) as [p|] eqn:Hf; [|lia].
  apply find_some in Hf as [Hin Heq]. apply Z.eqb_eq in Heq.
  destruct (Z_lt_le_dec x (fst p)) as [Hlt|Hge].
  - apply (IH (fst p) x). lia.
  - exists p. split; [exact Hin | lia].
Qed.
Lemma band_right_cover : forall ivs fuel hi x, hi <= x < band_right ivs hi fuel ->
  exists p, In p ivs /\ fst p <= x < fst p + snd p.
Proof.
  intros ivs fuel. induction fuel as [|f IH]; intros hi x Hx; cbn [band_right] in Hx; [lia|].
  destruct (List.find (fun p => Z.eqb (fst p) hi) ivs) as [p|] eqn:Hf; [|lia].
  apply find_some in Hf as [Hin Heq]. apply Z.eqb_eq in Heq.
  destruct (Z_lt_le_dec x (fst p + snd p)) as [Hlt|Hge].
  - exists p. split; [exact Hin | lia].
  - apply (IH (fst p + snd p) x). lia.
Qed.
Lemma shadow_band_cover : forall E ms L0 L3 x, shadow_band A ms = Some (L0, L3) -> L0 <= x < L3 ->
  exists m, In m ms /\ is_fog m = false /\ APS.uE E (am_base m) <= x < APS.uE E (am_base m) + APS.uE E (am_len m).
Proof.
  intros E ms L0 L3 x HB Hx. unfold shadow_band in HB. destruct (plain A); [discriminate|].
  set (ivs := lit_lazy_ivs ms) in HB.
  destruct (List.find _ ivs) as [p0|] eqn:Hf; [|discriminate]. injection HB as HL0 HL3.
  apply find_some in Hf as [Hin0 Hp0]. apply andb_prop in Hp0 as [_ _].
  assert (P : exists p, In p ivs /\ fst p <= x < fst p + snd p).
  { destruct (Z_lt_le_dec x (fst p0)) as [H1|H1].
    - apply (band_left_cover ivs (length ivs) (fst p0) x). rewrite HL0. lia.
    - destruct (Z_lt_le_dec x (fst p0 + snd p0)) as [H2|H2].
      + exists p0. split; [exact Hin0 | lia].
      + apply (band_right_cover ivs (length ivs) (fst p0 + snd p0) x). rewrite HL3. lia. }
  destruct P as (p & Hp & Hxp). destruct (lit_lazy_ivs_In E ms p Hp) as (m & Hm & Hnf & Hb & Hl & _).
  exists m. rewrite Hb, Hl. auto.
Qed.
Lemma shadow_band_lt : forall ms L0 L3, shadow_band A ms = Some (L0, L3) -> L0 < L3.
Proof.
  intros ms L0 L3 HB. unfold shadow_band in HB. destruct (plain A); [discriminate|].
  set (ivs := lit_lazy_ivs ms) in HB.
  destruct (List.find _ ivs) as [p0|] eqn:Hf; [|discriminate]. injection HB as HL0 HL3.
  apply find_some in Hf as [Hin0 _].
  pose proof (lit_lazy_ivs_pos ms) as HW. fold ivs in HW.
  pose proof (band_left_le ivs (length ivs) (fst p0) HW). pose proof (band_right_ge ivs (length ivs) (fst p0 + snd p0) HW).
  pose proof (HW p0 Hin0). lia.
Qed.
Lemma band_left_In : forall ivs fuel lo, band_left ivs lo fuel = lo \/ exists p, In p ivs /\ band_left ivs lo fuel = fst p.
Proof.
  intros ivs fuel. induction fuel as [|f IH]; intros lo; cbn [band_left]; [left; reflexivity|].
  destruct (List.find (fun p => Z.eqb (fst p + snd p) lo) ivs) as [p|] eqn:Hf; [|left; reflexivity].
  apply find_some in Hf as [Hin _]. destruct (IH (fst p)) as [E1|E1]; right; [exists p; split; [exact Hin | exact E1] | exact E1].
Qed.
Lemma band_right_In : forall ivs fuel hi, band_right ivs hi fuel = hi \/ exists p, In p ivs /\ band_right ivs hi fuel = fst p + snd p.
Proof.
  intros ivs fuel. induction fuel as [|f IH]; intros hi; cbn [band_right]; [left; reflexivity|].
  destruct (List.find (fun p => Z.eqb (fst p) hi) ivs) as [p|] eqn:Hf; [|left; reflexivity].
  apply find_some in Hf as [Hin _]. destruct (IH (fst p + snd p)) as [E1|E1]; right; [exists p; split; [exact Hin | exact E1] | exact E1].
Qed.
Lemma shadow_band_range : forall ms L0 L3, shadow_band A ms = Some (L0, L3) -> 0 <= L0 /\ L0 < L3 /\ L3 < two64.
Proof.
  intros ms L0 L3 HB. pose proof (shadow_band_lt ms L0 L3 HB) as HL.
  unfold shadow_band in HB. destruct (plain A); [discriminate|]. set (ivs := lit_lazy_ivs ms) in HB.
  destruct (List.find _ ivs) as [p0|] eqn:Hf; [|discriminate]. injection HB as HL0 HL3. apply find_some in Hf as [Hin0 _].
  assert (W : forall p, In p ivs -> 0 <= fst p /\ fst p + snd p < two64).
  { intros p Hp. destruct (lit_lazy_ivs_In (Env (fun _ => Z_to_bv 64 0) (fun _ => [])) ms p Hp) as (m & _ & _ & Hb & Hl & _).
    unfold ivs in Hp. unfold lit_lazy_ivs in Hp. apply in_flat_map in Hp as [m' [_ Hp']].
    destruct (lit_lazy_iv m') as [[b l]|] eqn:Hl'; [|destruct Hp']. destruct Hp' as [<-|[]].
    destruct (APS.lit_lazy_iv_sem (Env (fun _ => Z_to_bv 64 0) (fun _ => [])) m' b l Hl') as (_ & _ & _ & _ & B1 & B2 & B3). cbn [fst snd]. lia. }
  split; [|split; [exact HL|]].
  - destruct (band_left_In ivs (length ivs) (fst p0)) as [E1|(p & Hp & E1)]; rewrite <- HL0, E1; [exact (proj1 (W p0 Hin0)) | exact (proj1 (W p Hp))].
  - destruct (band_right_In ivs (length ivs) (fst p0 + snd p0)) as [E1|(p & Hp & E1)]; rewrite <- HL3, E1; [exact (proj2 (W p0 Hin0)) | exact (proj2 (W p Hp))].
Qed.
(* [comment removed for export] *)
Lemma band_apart : forall E ms lo n L0 L3, maps_apart E ms lo n -> 0 < n ->
  shadow_band A ms = Some (L0, L3) -> lo + n <= L0 \/ L3 <= lo.
Proof.
  intros E ms lo n L0 L3 Hap Hn HB. pose proof (shadow_band_lt ms L0 L3 HB) as HL.
  destruct (Z_lt_le_dec (lo + n) (L0 + 1)) as [H1|H1]; [left; lia|].
  destruct (Z_lt_le_dec lo L3) as [H2|H2]; [|right; lia]. exfalso.
  destruct (shadow_band_cover E ms L0 L3 (Z.max lo L0) HB ltac:(lia)) as (m & Hm & Hnf & Hx).
  unfold APS.uE in Hx. destruct (Hap m Hm Hnf); lia.
Qed.
(* [comment removed for export] *)
Lemma in_band_sound : forall SEGS E M k ms b o l,
  know_ok SEGS E M k -> in_band A k ms b o l = true ->
  exists L0 L3, shadow_band A ms = Some (L0, L3) /\ L0 <= estart E (SA b o) /\ estart E (SA b o) + elenZ E l <= L3.
Proof.
  intros SEGS E M k ms b o l HK H. unfold in_band in H.
  destruct (shadow_band A ms) as [[L0 L3]|] eqn:HB; [|discriminate].
  destruct (base_range k b) as [[blo bhi]|] eqn:Hb; [|discriminate].
  destruct (xhi k l) as [lh|] eqn:Hlh; [|discriminate].
  pose proof (base_range_sound SEGS E M k b blo bhi HK Hb) as [B1 B2]. pose proof (xhi_sound SEGS E M k l lh HK Hlh) as L1.
  exists L0, L3. split; [reflexivity|]. unfold estart, elenZ. cbn [a_base a_off].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc end.
  - apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
  - apply andb_prop in H as [H He]. apply andb_prop in H as [H Hw]. apply andb_prop in H as [H1 H0].
    apply Z.leb_le in H1. apply Z.leb_le in H0. apply Z.ltb_lt in Hw.
    destruct (xhi k (eadd (eaddz b o) l)) as [e|] eqn:Xe; [|discriminate]. apply Z.leb_le in He.
    pose proof (xhi_sound SEGS E M k _ e HK Xe) as HXE.
    unfold eadd, eaddz in HXE. rewrite !mkAlu_denot in HXE. rewrite !u_add64 in HXE. rewrite edenot_lit, u_lit64 in HXE.
    pose proof (u64_range (edenot E b)) as Rb1. pose proof (u64_range (edenot E l)) as Rn1.
    unfold two64 in *.
    assert (K1 : (o mod 2 ^ 64 = o /\ 0 <= o) \/ (o mod 2 ^ 64 = o + 2 ^ 64 /\ o < 0)).
    { destruct (Z_lt_le_dec o 0) as [Hn|Hp].
      - right. split; [|lia]. rewrite <- (Z.mod_add o 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
      - left. split; [|lia]. apply Z.mod_small. lia. }
    assert (E1 : (bv_unsigned (edenot E b) + o mod 2 ^ 64) mod 2 ^ 64 = bv_unsigned (edenot E b) + o).
    { destruct K1 as [[-> Hk]|[-> Hk]].
      - apply Z.mod_small. lia.
      - rewrite Z.add_assoc. rewrite <- (Z.mod_add _ (-1) (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia. }
    rewrite E1 in HXE. rewrite Z.mod_small in HXE by lia. lia.
Qed.
End BandCover.

Section Nodes.
Context {fx : FPState}.
Variable SEGS : list Segment.            Variable A : atable.
Variable nx0 : nat.                      Variable LIMIT : Z.
Hypothesis NX0_min : APS.nx0_min_ok nx0.   (* [comment removed for export] *)
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.     Variable FS0 : Fs.Fs.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis RES_len : res_len_ok SEGS A.
Hypothesis RES_hull : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A)
                             (segments_reserved SEGS).
Hypothesis HULL_ok : hull_ok A.                  Hypothesis SHADOW_ok : shadow_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
(* [comment removed for export] *)
Hypothesis argH_sp : forall E M (a : word), SINV E M -> argH E a = true -> APS.uE E e_sp0 <= bv_unsigned a.
(* [comment removed for export] *)
Hypothesis SINV_sp : forall E M, SINV E M -> sp_window_lo <= APS.uE E e_sp0 <= sp_window_hi.
Fixpoint hull_tight_b (l : list (word * word)) (lo hi : Z) : bool :=
  match l with
  | [] => Z.eqb lo hi
  | (b, sz) :: r => (Z.eqb (bv_unsigned b) lo && hull_tight_b r (lo + bv_unsigned sz) hi)%bool
  end.
Hypothesis HULL_tight : hull_tight_b (segments_reserved SEGS) (img_lo A) (img_hi A) = true /\ img_lo A < img_hi A.

#[local] Notation CSOK := (APS.cs_ok SEGS A LIMIT SINV argH FS0).
#[local] Notation HID := (APS.hid A argH).
#[local] Notation VIS := (APS.vis A).
#[local] Notation MR := (APS.Mr A argH).
#[local] Notation ALLOW := (APS.allowA A).
#[local] Notation cfg := (cfg_of SEGS).

(* [comment removed for export] *)
Let HS : nat -> option acs := fun _ => None.
Let XN : nat -> list expr -> acs -> option acs := fun _ _ _ => None.
Let XE : nat -> list expr -> acs -> option (Z * list spiece * acs) := fun _ _ _ => None.
Let XB : nat -> list expr -> acs -> option (acs * acs) := fun _ _ _ => None.
Let RES_len' : length (segments_reserved SEGS) = n_res A := RES_len.
Let HULL_ok' : 0 <= img_lo A /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0 /\ img_hi A <= KHI := HULL_ok.
Let SHADOW_ok' : 0 <= shadow_off A <= 2 ^ 47 := SHADOW_ok.
Let RES_hullH : RES_hull_def SEGS A := RES_hull.

(* [comment removed for export] *)
Let reg_sound' := APS.reg_sound SEGS A LIMIT SINV argH FS0.
Let reg_lit_sound' := APS.reg_lit_sound SEGS A LIMIT SINV argH FS0.
Let kentry_keep_sem' := APS.kentry_keep_sem SEGS.
Let kentry_apart_b_sem' := APS.kentry_apart_b_sem SEGS.
Let regs_ok_set_n' := APS.regs_ok_set_n.
Let in_ivs_map_den' := APS.in_ivs_map_den.
Let kimg_clip_in_hull' := APS.kimg_clip_in_hull A.
Let cs_ok_agree' := APS.cs_ok_agree SEGS A nx0 NX0_min LIMIT SINV argH argH_agree SINV_agree FS0.
Let cs_ok_frame' := APS.cs_ok_frame SEGS A LIMIT SINV argH SINV_frame FS0.
Let hid_agree' := APS.hid_agree A nx0 argH argH_agree.
Let vis_add_sound' := APS.vis_add_sound SEGS A LIMIT HS XN XE XB SHADOW_ok SINV argH argH_high argH_sp FS0 0%nat.   (* [comment removed for export] *)
Let A_wf_allowA' := APS.A_wf_allowA A HS XN XE XB 0%nat.
Let know_ok_unhide' := APS.know_ok_unhide SEGS A.
Let hid_hull' := APS.hid_hull A HULL_ok argH argH_high.
Let H_off_segments_cs' := APS.H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH argH_high.
Let maps_match_exact' := APS.maps_match_exact nx0 HS XN XE XB.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mmap_len_sound : forall E cs R FULL model ne nlo nhi,
  CSOK E cs R FULL model -> mmap_len cs = Some (ne, nlo, nhi) ->
  let len := bv_unsigned (edenot E (reg cs 11)) in
  getr R (Z_to_bv 5 11) = Z_to_bv 64 len
  /\ 0 < len < 2 ^ 64
  /\ edenot E ne = Z_to_bv 64 (page_round_up_Z len)
  /\ 0 < nlo /\ nlo <= page_round_up_Z len <= nhi
  /\ page_round_up_Z len mod 4096 = 0
  /\ (forall E', edenot E' (reg cs 11) = edenot E (reg cs 11) -> env_agree (nxt cs) E E' -> edenot E' ne = edenot E ne).
Proof.
  intros E cs R FULL model ne nlo nhi HC HML len.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (reg_sound' E cs R FULL model 11 HC ltac:(lia)) as R11. change (Z.of_nat 11) with 11 in R11.
  pose proof (u64_range (edenot E (reg cs 11))) as Hr.
  rewrite mmap_len_eq in HML. (* [comment removed for export] *) unfold mmap_len_ref in HML.
  destruct (reg_lit cs 11) as [lz|] eqn:H11.
  - destruct (Z.ltb_spec 0 lz); [|discriminate]. injection HML as <- <- <-.
    destruct (reg_lit_sound' E cs R FULL model 11 lz HC ltac:(lia) H11) as [R11' Hlz]. change (Z.of_nat 11) with 11 in R11'.
    assert (Hlen : len = lz).
    { unfold len. rewrite <- R11, R11'. apply u64_lit. unfold two64 in Hlz. lia. }
    rewrite Hlen. pose proof (page_round_up_Z_bounds lz ltac:(lia)) as PB. unfold page_size in PB.
    rewrite page_up_eq.
    split; [exact R11'|]. split; [unfold two64 in Hlz; lia|]. split; [reflexivity|]. split; [lia|]. split; [lia|].
    split; [apply page_round_up_Z_aligned'|]. intros E' _ _. reflexivity.
  - destruct (xlo (kn cs) (reg cs 11)) as [lo|] eqn:Hxl; [|discriminate].
    destruct (xhi (kn cs) (reg cs 11)) as [hi|] eqn:Hxh; [|discriminate].
    match type of HML with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
    apply andb_prop in Hc as [Hlo Hhi]. apply Z.ltb_lt in Hlo. apply Z.leb_le in Hhi.
    pose proof (xlo_sound SEGS E _ (kn cs) _ lo HK Hxl) as B1.
    pose proof (xhi_sound SEGS E _ (kn cs) _ hi HK Hxh) as B2.
    destruct (Z.leb_spec 12 (ealign (kn cs) (reg cs 11))) as [Hal|Hnal].
    2:{ (* [comment removed for export] *)
        pose proof (page_round_up_Z_bounds len ltac:(unfold len; lia)) as PB. unfold page_size in PB.
        assert (Hne : edenot E (page_up_e (kn cs) (reg cs 11)) = Z_to_bv 64 (page_round_up_Z len)).
        { unfold page_up_e. rewrite mkMd_denot.
          rewrite (mkSrl_denot SEGS E _ (kn cs) _ 12 (Z_to_bv 64 12) HK) by (rewrite u_lit64; reflexivity).
          apply bv_eq. rewrite u_mul64, u_srl64, mkAlu_denot, u_add64, !u_lit64, edenot_lit, u_lit64.
          unfold page_round_up_Z, page_size, two64. unfold len in *.
          change (2 ^ (12 mod 2 ^ 64 mod 64)) with 4096. change (bv_unsigned (edenot E (ELit 4095))) with 4095.
          rewrite (Z.mod_small 4096) by lia. rewrite (Z.mod_small (bv_unsigned (edenot E (reg cs 11)) + 4095)) by lia.
          replace (bv_unsigned (edenot E (reg cs 11)) + 4096 - 1) with (bv_unsigned (edenot E (reg cs 11)) + 4095) by lia.
          rewrite (Z.mul_comm 4096). reflexivity. }
        assert (Hup : page_round_up_Z len <= page_up hi).
        { unfold len in *. rewrite page_up_eq. unfold page_round_up_Z, page_size.
          apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia. }
        assert (SYM : expr_vars_lt (nxt cs) (page_up_e (kn cs) (reg cs 11)) = true ->
                      Some (page_up_e (kn cs) (reg cs 11), lo, page_up hi) = Some (ne, nlo, nhi) ->
                      getr R (Z_to_bv 5 11) = Z_to_bv 64 len /\ 0 < len < 2 ^ 64 /\ edenot E ne = Z_to_bv 64 (page_round_up_Z len)
                      /\ 0 < nlo /\ nlo <= page_round_up_Z len <= nhi /\ page_round_up_Z len mod 4096 = 0
                      /\ (forall E', edenot E' (reg cs 11) = edenot E (reg cs 11) -> env_agree (nxt cs) E E' -> edenot E' ne = edenot E ne)).
        { intros Hvl X. injection X as <- <- <-.
          split; [rewrite R11; symmetry; apply Z_to_bv_bv_unsigned|].
          split; [unfold len in *; lia|]. split; [exact Hne|].
          split; [lia|]. split; [unfold len in *; lia|].
          split; [apply page_round_up_Z_aligned'|].
          intros E' _ Hag. symmetry. eapply edenot_agree'; [exact Hag | exact Hvl]. }
        destruct (xlo (kn cs) (page_up_e (kn cs) (reg cs 11))) as [a|] eqn:Hxa;
          [destruct (xhi (kn cs) (page_up_e (kn cs) (reg cs 11))) as [b|] eqn:Hxb|];
          [destruct (Z.eqb_spec a b) as [Hab|Hab] | |];
          try (destruct (expr_vars_lt (nxt cs) (page_up_e (kn cs) (reg cs 11))) eqn:Hvl; [exact (SYM eq_refl HML)|discriminate]).
        (* [comment removed for export] *)
        injection HML as <- <- <-.
        pose proof (xlo_sound SEGS E _ (kn cs) _ a HK Hxa) as Ba. pose proof (xhi_sound SEGS E _ (kn cs) _ b HK Hxb) as Bb.
        rewrite Hne, u64_lit in Ba, Bb by (unfold len in *; lia).
        assert (Hpt : page_round_up_Z len = a) by lia.
        split; [rewrite R11; symmetry; apply Z_to_bv_bv_unsigned|].
        split; [unfold len in *; lia|]. split; [rewrite edenot_lit, Hpt; reflexivity|].
        split; [lia|]. split; [unfold len in *; lia|].
        split; [apply page_round_up_Z_aligned'|].
        intros E' _ _. reflexivity. }
    injection HML as <- <- <-.
    destruct (ealign_sound SEGS E _ (kn cs) (reg cs 11) HK) as [_ Hdiv].
    assert (Hmod : len mod 4096 = 0).
    { unfold len. destruct Hdiv as [q Hq]. rewrite Hq.
      replace (2 ^ ealign (kn cs) (reg cs 11)) with (2 ^ (ealign (kn cs) (reg cs 11) - 12) * 4096)
        by (rewrite <- (Z.pow_add_r 2 _ 12) by lia; f_equal; lia).
      rewrite Z.mul_assoc. apply Z.mod_mul. lia. }
    assert (Hpr : page_round_up_Z len = len).
    { unfold page_round_up_Z, page_size.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). unfold len in *. lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    rewrite Hpr.
    split; [rewrite R11; symmetry; apply Z_to_bv_bv_unsigned|].
    split; [unfold len in *; lia|]. split; [symmetry; apply Z_to_bv_bv_unsigned|].
    split; [lia|]. split; [unfold len in *; lia|]. split; [exact Hmod|].
    intros E' HE' _. exact HE'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv5_of_nat : forall n, (n < 32)%nat -> Z_to_bv 5 (Z.of_nat n) = Z_to_bv 5 (Z.of_nat n). Proof. reflexivity. Qed.
Lemma bv5_10 : (10%bv : bv 5) = Z_to_bv 5 (Z.of_nat 10). Proof. apply bv_eq. reflexivity. Qed.
Lemma bv5_11 : (11%bv : bv 5) = Z_to_bv 5 (Z.of_nat 11). Proof. apply bv_eq. reflexivity. Qed.
Lemma bv5_12 : (12%bv : bv 5) = Z_to_bv 5 (Z.of_nat 12). Proof. apply bv_eq. reflexivity. Qed.
Lemma bv5_13 : (13%bv : bv 5) = Z_to_bv 5 (Z.of_nat 13). Proof. apply bv_eq. reflexivity. Qed.
Lemma bv5_14 : (14%bv : bv 5) = Z_to_bv 5 (Z.of_nat 14). Proof. apply bv_eq. reflexivity. Qed.
Lemma bv5_15 : (15%bv : bv 5) = Z_to_bv 5 (Z.of_nat 15). Proof. apply bv_eq. reflexivity. Qed.
Lemma bv5_17 : (17%bv : bv 5) = Z_to_bv 5 (Z.of_nat 17). Proof. apply bv_eq. reflexivity. Qed.

Lemma some_inj : forall {T} (a b : T), Some a = Some b -> a = b.
Proof. intros T a b H. injection H as H1. exact H1. Qed.

Lemma CEIL_eq : alloc_ceiling = CEIL.
Proof. reflexivity. Qed.
Lemma KHI_eq : kHighMemBeg = KHI.
Proof. reflexivity. Qed.
Lemma FLOOR_eq : bottomup_floor = FLOOR.
Proof. rewrite bottomup_floor_val. reflexivity. Qed.

Lemma Z_to_bv64_m1 : forall m1, m1 = two64 - 1 -> Z_to_bv 64 m1 = Z_to_bv 64 (-1).
Proof. intros m1 ->. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. Qed.

(* [comment removed for export] *)
Lemma reserved_free_above : forall model (lo n : word),
  vm_reserved (m_vmmaps model) = segments_reserved SEGS ->
  img_hi A <= bv_unsigned lo ->
  region_free (vm_reserved (m_vmmaps model)) lo n = true.
Proof.
  intros model lo n Hres Hlo. rewrite Hres. apply RefNodes.region_free_intro. intros b s Hin.
  pose proof (proj1 (Forall_forall _ _) RES_hullH _ Hin) as [H1 H2]. cbn [fst snd] in H1, H2. right. lia.
Qed.

(* [comment removed for export] *)
Lemma reserved_free_of_hull : forall model (lo n : word),
  vm_reserved (m_vmmaps model) = segments_reserved SEGS ->
  (bv_unsigned lo + bv_unsigned n <= img_lo A \/ img_hi A <= bv_unsigned lo) ->
  region_free (vm_reserved (m_vmmaps model)) lo n = true.
Proof.
  intros model lo n Hres Hlo. rewrite Hres. apply RefNodes.region_free_intro. intros b s Hin.
  pose proof (proj1 (Forall_forall _ _) RES_hullH _ Hin) as [H1 H2]. cbn [fst snd] in H1, H2. lia.
Qed.

(* [comment removed for export] *)
Lemma vis_add_inv : forall cs b n k cs2,
  vis_add A LIMIT cs b n k = Some cs2 ->
  exists nhi, xhi (kn cs) n = Some nhi /\
  cs2 = ACS (mk_ss (pc cs) (s_regs (a_ss cs)) (shadow_facts A (kn cs) (a_maps cs) b n ++ k) (nxt cs))
            (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
            ((b, n) :: a_vis cs) (a_ghost cs) (a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs).
Proof.
  intros cs b n k cs2 Hv. rewrite vis_add_eq in Hv. (* [comment removed for export] *) unfold vis_add_ref in Hv.
  destruct (split_lit b) as [bb bk]. destruct (shadow_of A (kn cs) b n) as [[sb sk] sn] eqn:Hsh.
  destruct (xhi (kn cs) n) as [nhi|]; [|discriminate].
  match type of Hv with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
  injection Hv as <-. exists nhi. split; [reflexivity|]. unfold shadow_facts. rewrite Hsh. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma in_allow_ext : forall E cs cs', a_vis cs' = a_vis cs -> in_allow A E cs' = in_allow A E cs.
Proof. intros E cs cs' H. apply functional_extensionality. intros z. unfold in_allow, in_vis, in_sh. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition kind_none (k : mkind) : bool := match k with KNONE | KNONELAZY => true | _ => false end.
Definition kind_lazy (k : mkind) : bool := match k with KRWLAZY | KNONELAZY => true | _ => false end.

Record grant_post (kd : mkind) (a n : word) (model model' : Model) : Prop := GP {
  gp_maps : vm_maps (m_vmmaps model') = (a, n) :: vm_maps (m_vmmaps model);
  gp_res : vm_reserved (m_vmmaps model') = vm_reserved (m_vmmaps model);
  gp_noacc : vm_noaccess (m_vmmaps model') = (if kind_none kd then (a, n) :: vm_noaccess (m_vmmaps model) else vm_noaccess (m_vmmaps model));
  gp_lazy : m_vm_lazy model' = (if kind_lazy kd then (a, n) :: m_vm_lazy model else m_vm_lazy model);
  gp_mat : m_vm_materialized model' = m_vm_materialized model;
  gp_limit : vm_limit (m_vmmaps model') = vm_limit (m_vmmaps model);
  gp_brk : vm_brk (m_vmmaps model') = vm_brk (m_vmmaps model);
  gp_sbrk : vm_start_brk (m_vmmaps model') = vm_start_brk (m_vmmaps model);
  gp_mbase : vm_mmap_base (m_vmmaps model') = vm_mmap_base (m_vmmaps model);
  gp_halted : m_halted model' = m_halted model;
  gp_fds : m_fds model' = m_fds model;
  gp_fs : m_fs model' = m_fs model;
  gp_tid : m_tid model' = m_tid model;
  gp_isp : vm_init_sp (m_vmmaps model') = vm_init_sp (m_vmmaps model)  (* [comment removed for export] *) }.

Definition grant_mem (kd : mkind) (a n : word) (FULL FULL' : word -> option byte) : Prop :=
  (forall x : word, bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x -> FULL' x = FULL x)
  /\ (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n ->
        FULL' x = if kind_none kd then None else Some (Z_to_bv 8 0)).

(* [comment removed for export] *)
Lemma gp_atop : forall kd a n model model', grant_post kd a n model model' ->
  alloc_top (m_vmmaps model') = alloc_top (m_vmmaps model).
Proof. intros kd a n model model' GPo. unfold alloc_top. rewrite (gp_isp _ _ _ _ _ GPo). reflexivity. Qed.

(* [comment removed for export] *)
Lemma vis_grant_out : forall kd (a n : word) model model' E cs cs1 (x : word),
  grant_post kd a n model model' ->
  a_vis cs1 = a_vis cs ->
  0 < bv_unsigned n -> bv_unsigned a mod 4096 = 0 -> bv_unsigned n mod 4096 = 0 ->
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x) ->
  VIS E cs1 model' x = VIS E cs model x.
Proof.
  intros kd a n model model' E cs cs1 x GPo Hvis Hn Hal Hnl Hx.
  unfold vis. rewrite (gp_maps _ _ _ _ _ GPo), (gp_noacc _ _ _ _ _ GPo), (gp_lazy _ _ _ _ _ GPo), (gp_atop _ _ _ _ _ GPo).
  rewrite (in_allow_ext E cs cs1 Hvis).
  rewrite in_ivs_cons. cbn [fst snd].
  assert (T : ((bv_unsigned a <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned a + bv_unsigned n))%bool = false).
  { apply andb_false_iff. destruct Hx; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia. }
  rewrite T. cbn [orb].
  assert (P : page_in_ranges (page_base x) ((a, n) :: m_vm_lazy model) = page_in_ranges (page_base x) (m_vm_lazy model)).
  { apply page_in_ranges_cons_out; [|exact Hn].
    pose proof (page_of_byte_out_aligned x (bv_unsigned a) (bv_unsigned a + bv_unsigned n) Hal ltac:(rewrite Z.add_mod, Hal, Hnl by lia; reflexivity) Hx).
    unfold page_size. lia. }
  destruct (kind_none kd); destruct (kind_lazy kd); rewrite ?in_ivs_cons; cbn [fst snd]; rewrite ?T, ?P; cbn [orb]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma vis_grant_out2 : forall kd (a n : word) model model' E cs cs2 (x : word) base ne,
  grant_post kd a n model model' ->
  (a_vis cs2 = a_vis cs \/ a_vis cs2 = (base, ne) :: a_vis cs) ->
  edenot E base = a -> bv_unsigned (edenot E ne) <= bv_unsigned n ->
  0 < bv_unsigned n -> bv_unsigned a mod 4096 = 0 -> bv_unsigned n mod 4096 = 0 ->
  (plain A = true -> m_vm_lazy model = [] /\ kind_lazy kd = false) ->
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x) ->
  (plain A = false -> ~ (sh_lo A E (base, ne) <= bv_unsigned x < sh_hi A E (base, ne))) ->
  VIS E cs2 model' x = VIS E cs model x.
Proof.
  intros kd a n model model' E cs cs2 x base ne GPo Hvis Hbase Hne Hn Hal Hnl Hplain Hx Hsh.
  unfold vis. rewrite (gp_maps _ _ _ _ _ GPo), (gp_noacc _ _ _ _ _ GPo), (gp_lazy _ _ _ _ _ GPo), (gp_atop _ _ _ _ _ GPo).
  rewrite in_ivs_cons. cbn [fst snd].
  assert (T : ((bv_unsigned a <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned a + bv_unsigned n))%bool = false).
  { apply andb_false_iff. destruct Hx; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia. }
  rewrite T. cbn [orb].
  assert (P : page_in_ranges (page_base x) ((a, n) :: m_vm_lazy model) = page_in_ranges (page_base x) (m_vm_lazy model)).
  { apply page_in_ranges_cons_out; [|exact Hn].
    pose proof (page_of_byte_out_aligned x (bv_unsigned a) (bv_unsigned a + bv_unsigned n) Hal ltac:(rewrite Z.add_mod, Hal, Hnl by lia; reflexivity) Hx).
    unfold page_size. lia. }
  assert (AL : plain A = false -> in_allow A E cs2 (bv_unsigned x) = in_allow A E cs (bv_unsigned x)).
  { intros Hpl. destruct Hvis as [Hv|Hv].
    - exact (f_equal (fun f => f (bv_unsigned x)) (in_allow_ext E cs cs2 Hv)).
    - unfold in_allow, in_vis, in_sh. rewrite Hv. cbn [existsb fst snd].
      assert (T1 : ((uE E base <=? bv_unsigned x) && (bv_unsigned x <? uE E base + uE E ne))%bool = false).
      { unfold uE. rewrite Hbase. apply andb_false_iff. destruct Hx; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia. }
      assert (T2 : ((sh_lo A E (base, ne) <=? bv_unsigned x) && (bv_unsigned x <? sh_hi A E (base, ne)))%bool = false).
      { specialize (Hsh Hpl). apply andb_false_iff.
        destruct (Z.le_gt_cases (sh_lo A E (base, ne)) (bv_unsigned x)); [right; apply Z.ltb_ge; lia | left; apply Z.leb_gt; lia]. }
      rewrite T1, T2. cbn [orb]. reflexivity. }
  destruct (plain A) eqn:Hpl.
  - destruct (Hplain eq_refl) as [Hlz Hkl]. rewrite Hlz in P |- *. rewrite Hkl. cbn [page_in_ranges negb orb andb] in *.
    destruct (kind_none kd); rewrite ?in_ivs_cons; cbn [fst snd]; rewrite ?T; cbn [orb andb negb];
      rewrite ?Bool.orb_true_l, ?Bool.andb_true_r; reflexivity.
  - rewrite (AL eq_refl).
    destruct (kind_none kd); destruct (kind_lazy kd); rewrite ?in_ivs_cons; cbn [fst snd]; rewrite ?T, ?P; cbn [orb]; reflexivity.
Qed.

Lemma hid_grant_out2 : forall kd (a n : word) model model' E cs cs2 (x : word) base ne,
  grant_post kd a n model model' ->
  (a_vis cs2 = a_vis cs \/ a_vis cs2 = (base, ne) :: a_vis cs) ->
  edenot E base = a -> bv_unsigned (edenot E ne) <= bv_unsigned n ->
  0 < bv_unsigned n -> bv_unsigned a mod 4096 = 0 -> bv_unsigned n mod 4096 = 0 ->
  (plain A = true -> m_vm_lazy model = [] /\ kind_lazy kd = false) ->
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x) ->
  (plain A = false -> ~ (sh_lo A E (base, ne) <= bv_unsigned x < sh_hi A E (base, ne))) ->
  HID E cs2 model' x = HID E cs model x.
Proof.
  intros kd a n model model' E cs cs2 x base ne GPo Hvis Hbase Hne Hn Hal Hnl Hplain Hx Hsh.
  unfold hid. rewrite (vis_grant_out2 kd a n model model' E cs cs2 x base ne GPo Hvis Hbase Hne Hn Hal Hnl Hplain Hx Hsh). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_win_sem : forall cs' W base ne kd ms E' R' FULL' model' (a n : word) (x : word),
  AP.mmap_win A cs' = Some W -> a_maps cs' = AM base ne kd :: ms ->
  CSOK E' cs' R' FULL' model' ->
  edenot E' base = a -> edenot E' ne = n -> bv_unsigned a mod 4096 = 0 ->
  ws_out E' W x ->
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)
  /\ (plain A = false -> ~ (sh_lo A E' (base, ne) <= bv_unsigned x < sh_hi A E' (base, ne))).
Proof.
  intros cs' W base ne kd ms E' R' FULL' model' a n x Hw Hms HC' Hbase Hne Hal Hout.
  unfold AP.mmap_win in Hw. rewrite Hms in Hw. cbn [am_base am_len] in Hw.
  assert (MAPW : In (SA base 0, ne) W -> bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x).
  { intros Hin. specialize (Hout _ Hin). cbn [fst snd] in Hout. unfold estart, elenZ in Hout. cbn [a_base a_off] in Hout.
    rewrite Hbase, Hne in Hout. lia. }
  destruct (plain A) eqn:Hpl.
  - injection Hw as <-. split; [apply MAPW; left; reflexivity | intros; congruence].
  - destruct (shadow_of A (kn cs') base ne) as [[sb sk] sn] eqn:Hsh.
    destruct (flat_x (kn cs') sb sk sn) eqn:Hfl; [|discriminate]. injection Hw as <-.
    split; [apply MAPW; left; reflexivity|]. intros _.
    specialize (Hout (SA sb sk, sn) ltac:(right; left; reflexivity)). cbn [fst snd] in Hout.
    destruct (shadow_of_val SEGS A SHADOW_ok E' _ (kn cs') base ne sb sk sn (co_know _ _ _ _ _ _ _ _ _ _ _ HC') Hsh Hfl) as [Hs Hl].
    rewrite Hs, Hl, Hbase, Hne in Hout.
    pose proof SHADOW_ok as SO. unfold shadow_ok in SO.
    pose proof (u64_range a) as Ra. pose proof (u64_range n) as Rn.
    assert (Hd8 : 0 <= bv_unsigned a / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    rewrite Z.mod_small in Hout by lia.
    unfold sh_lo, sh_hi, uE. cbn [fst snd]. rewrite Hbase, Hne.
    assert (D8 : (bv_unsigned a + bv_unsigned n) / 8 = bv_unsigned a / 8 + bv_unsigned n / 8).
    { assert (M8 : bv_unsigned a mod 8 = 0).
      { pose proof (Z.div_mod (bv_unsigned a) 4096 ltac:(lia)) as X. rewrite Hal, Z.add_0_r in X.
        rewrite X. replace (4096 * (bv_unsigned a / 4096)) with ((512 * (bv_unsigned a / 4096)) * 8) by lia. apply Z_mod_mult. }
      pose proof (Z.div_mod (bv_unsigned a) 8 ltac:(lia)) as Y. rewrite M8, Z.add_0_r in Y.
      rewrite Y at 1. rewrite Z.mul_comm, Z.div_add_l by lia. lia. }
    lia.
Qed.

Lemma grant_wf : forall kd a n model model',
  grant_post kd a n model model' -> model_ivs_wf model ->
  bv_unsigned a + bv_unsigned n <= 2 ^ 64 -> model_ivs_wf model'.
Proof.
  intros kd a n model model' GPo (W1 & W2 & W3 & Wsp) Hb. unfold model_ivs_wf.
  rewrite (gp_maps _ _ _ _ _ GPo), (gp_noacc _ _ _ _ _ GPo), (gp_lazy _ _ _ _ _ GPo).
  assert (iv_wf (a, n)) by (unfold iv_wf, B, S; cbn; lia).
  split; [apply ivs_wf_cons; assumption|].
  split; [destruct (kind_none kd); try apply ivs_wf_cons; assumption|].
  split; [destruct (kind_lazy kd); try apply ivs_wf_cons; assumption|].
  unfold init_sp_ok in *. rewrite (gp_isp _ _ _ _ _ GPo). exact Wsp.
Qed.

(* [comment removed for export] *)
Lemma grant_eager_le : forall kd a n model model',
  grant_post kd a n model model' -> model_ivs_wf model -> bv_unsigned a + bv_unsigned n <= 2 ^ 64 ->
  eager_used model' <= eager_used model + (if (kind_none kd || kind_lazy kd)%bool then 0 else bv_unsigned n).
Proof.
  intros kd a n model model' GPo Hwf Hb.
  pose proof (grant_wf kd a n model model' GPo Hwf Hb) as Hwf'.
  rewrite (eager_used_sem model' Hwf'), (eager_used_sem model Hwf).
  rewrite (gp_maps _ _ _ _ _ GPo).
  set (C := vm_noaccess (m_vmmaps model) ++ m_vm_lazy model).
  set (C' := vm_noaccess (m_vmmaps model') ++ m_vm_lazy model').
  cbn [sum_count].
  assert (MONO : sum_count (fun x => negb (covered C' x)) (vm_maps (m_vmmaps model))
                 <= sum_count (fun x => negb (covered C x)) (vm_maps (m_vmmaps model))).
  { apply sum_count_negb_covered_mono. intros x Hx. subst C C'.
    rewrite (gp_noacc _ _ _ _ _ GPo), (gp_lazy _ _ _ _ _ GPo). rewrite covered_app in Hx. rewrite covered_app.
    apply orb_true_iff in Hx. apply orb_true_iff.
    destruct Hx as [Hx|Hx]; [left|right]; [destruct (kind_none kd) | destruct (kind_lazy kd)]; try exact Hx;
      unfold covered in *; cbn [existsb]; rewrite Hx; apply orb_true_r. }
  assert (HEAD : iv_count (fun x => negb (covered C' x)) (a, n) <= (if (kind_none kd || kind_lazy kd)%bool then 0 else bv_unsigned n)).
  { destruct (kind_none kd || kind_lazy kd)%bool eqn:Hk.
    - unfold iv_count, B, S. cbn [fst snd]. rewrite zcount_false; [lia|]. intros x Hx.
      pose proof (u64_range n). rewrite Z2Nat.id in Hx by lia. apply negb_false_iff.
      subst C'. rewrite (gp_noacc _ _ _ _ _ GPo), (gp_lazy _ _ _ _ _ GPo). rewrite covered_app.
      assert (IN : in_iv (a, n) x = true).
      { unfold in_iv, in_rng, B, S. cbn [fst snd]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
      apply orb_prop in Hk as [Hk|Hk]; rewrite Hk; unfold covered; cbn [existsb]; rewrite IN; cbn [orb];
        [reflexivity | apply orb_true_r].
    - unfold iv_count, S. cbn [snd]. pose proof (u64_range n).
      pose proof (zcount_le_len (fun x => negb (covered C' x)) (B (a, n)) (Z.to_nat (bv_unsigned n))). lia. }
  lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma maps_apart_of_region_free : forall E ms model (a n : word),
  maps_match E ms (vm_maps (m_vmmaps model)) ->
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) a n = true ->
  maps_apart E ms (bv_unsigned a) (bv_unsigned n).
Proof.
  intros E ms model a n Hmaps Hrf m Hin Hnf.
  rewrite region_free_app in Hrf. apply andb_prop in Hrf as [_ Hrf].
  exact (RefNodes.region_free_In _ a n (edenot E (am_base m)) (edenot E (am_len m)) Hrf (maps_match_In E ms _ m Hmaps Hin Hnf)).
Qed.

Lemma inside_maps_apart : forall E M k ms b o l lo n,
  know_ok SEGS E M k -> maps_apart E ms lo n ->
  inside_maps k ms b o l = true ->
  estart E (SA b o) + elenZ E l <= lo \/ lo + n <= estart E (SA b o).
Proof.
  intros E M k ms b o l lo n HK Hap. induction ms as [|m ms IH]; intros H; [discriminate|].
  cbn [inside_maps] in H. apply orb_prop in H as [H|H].
  - apply andb_prop in H as [Hnf H]. apply negb_true_iff in Hnf.
    pose proof (xinside_sound SEGS E M k b o l (am_base m) 0 (am_len m) HK H) as [I1 I2].
    unfold estart in I1, I2 |- *. cbn [a_base a_off] in *. unfold elenZ in *.
    destruct (Hap m (or_introl eq_refl) Hnf); lia.
  - apply IH; [|exact H]. intros m' Hm'. apply Hap. right. exact Hm'.
Qed.

Lemma in_band_apart : forall E M k ms b o l lo n,
  know_ok SEGS E M k -> maps_apart E ms lo n -> 0 < n ->
  in_band A k ms b o l = true ->
  estart E (SA b o) + elenZ E l <= lo \/ lo + n <= estart E (SA b o).
Proof.
  intros E M k ms b o l lo n HK Hap Hn H.
  destruct (in_band_sound A SEGS E M k ms b o l HK H) as (L0 & L3 & HB & H1 & H2).
  destruct (band_apart A E ms lo n L0 L3 Hap Hn HB); lia.
Qed.

(* [comment removed for export] *)
Lemma safe_range_apart : forall E M k ms b o l lo n,
  know_ok SEGS E M k -> maps_apart E ms lo n ->
  lo + n <= uE E e_sp0 - STK_BELOW ->
  (lo + n <= img_lo A \/ img_hi A <= lo) -> 0 < n ->   (* [comment removed for export] *)
  safe_range A k ms b o l = true ->
  estart E (SA b o) + elenZ E l <= lo \/ lo + n <= estart E (SA b o).
Proof.
  intros E M k ms b o l lo n HK Hap Hsp Hhull Hn H. unfold safe_range in H. apply orb_prop in H as [H|H].
  2: { (* [comment removed for export] *) eapply in_band_apart; eassumption. }
  apply orb_prop in H as [H|H].
  - destruct (xhi k l) as [lh|] eqn:Hlh; [|discriminate].
    pose proof (xhi_sound SEGS E M k l lh HK Hlh) as L1.
    apply orb_prop in H as [H|H].
    + (* [comment removed for export] *)
      pose proof (on_stack_side_sound SEGS E M k b o HK H) as S1. right. lia.
    + (* [comment removed for export] *)
      destruct (base_range k b) as [[blo bhi]|] eqn:Hb; [|discriminate].
      pose proof (base_range_sound SEGS E M k b blo bhi HK Hb) as [B1 B2].
      apply andb_prop in H as [H1 H2]; apply Z.leb_le in H1; apply Z.leb_le in H2.
      unfold estart, elenZ in *. cbn [a_base a_off] in *. lia.
  - eapply inside_maps_apart; eassumption.
Qed.

Lemma grant_keep_apart : forall E M k ms K lo n,
  know_ok SEGS E M k -> maps_apart E ms lo n ->
  lo + n <= uE E e_sp0 - STK_BELOW -> (lo + n <= img_lo A \/ img_hi A <= lo) -> 0 < n ->   (* [comment removed for export] *)
  grant_keep_b A k ms K = true ->
  match K with KImg _ _ => False | _ => True end ->
  kfoot_apart E K lo n.
Proof.
  intros E M k ms K lo n HK Hap Hsp Hhull Hn H HnI. unfold kfoot_apart, kfoot.
  destruct K as [[b o] w v|[b o] l|[b o] l kb|ilo ihi|e m|e rlo rhi|[b o] l|a1 n1 a2 n2|[b o] l fc|[b o] l]; cbn [grant_keep_b] in H;
    try exact I; [apply andb_prop in H as [Hw H]; apply Nat.leb_le in Hw| | | destruct HnI | | |];
    pose proof (safe_range_apart E M k ms b o _ lo n HK Hap Hsp Hhull Hn H) as D; try lia.
  rewrite elenZ_lit'' in D by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma kn_grant_filter_ok : forall E M M' k ms lo n,
  know_ok SEGS E M k -> maps_apart E ms lo n ->
  0 < n -> lo + n <= uE E e_sp0 - STK_BELOW -> (lo + n <= img_lo A \/ img_hi A <= lo) ->   (* [comment removed for export] *)
  (forall x : word, bv_unsigned x < lo \/ lo + n <= bv_unsigned x -> M' x = M x) ->
  know_ok SEGS E M' (kn_grant_filter A k ms).
Proof.
  intros E M M' k ms lo n HK Hap Hn Hsp Hhull Hout. unfold kn_grant_filter.
  pose proof (kimg_clip_in_hull' (List.filter (grant_keep_b A k ms) k)) as Hhull'.
  unfold know_ok. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) Hhull' K Hin) as HKh.
  apply kimg_clip_incl in Hin. apply filter_In in Hin as [Hin Hkeep].
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  eapply kentry_keep_sem'; [exact HKK | | exact Hout].
  destruct K as [| | |ilo ihi| | | | | |];
    try (eapply grant_keep_apart; [exact HK | exact Hap | exact Hsp | exact Hhull | exact Hn | exact Hkeep | exact I]).
  (* [comment removed for export] *)
  unfold kfoot_apart, kfoot. cbn in HKh. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma regs_ok_regupd_same : forall E sr R n (v : word),
  regs_ok E sr R -> (0 < n < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = v ->
  regs_ok E sr (regupd R (Z_to_bv 5 (Z.of_nat n)) v).
Proof.
  intros E sr R n v HR Hn Hv r.
  assert (Hne : Z_to_bv 5 (Z.of_nat n) <> 0%bv).
  { intros Hz. apply (f_equal bv_unsigned) in Hz. rewrite Z_to_bv_unsigned in Hz. unfold bv_wrap in Hz.
    change (bv_modulus 5) with 32%Z in Hz. rewrite Z.mod_small in Hz by lia.
    replace (bv_unsigned (0%bv : bv 5)) with 0%Z in Hz by reflexivity. lia. }
  destruct (bv_eqb r (Z_to_bv 5 (Z.of_nat n))) eqn:Hr.
  - apply (proj1 (bv_eqb_eq _ _)) in Hr. subst r. rewrite getr_same by exact Hne. rewrite <- Hv. apply HR.
  - assert (Hr' : r <> Z_to_bv 5 (Z.of_nat n)) by (intros ->; rewrite bv_eqb_refl in Hr; discriminate).
    rewrite getr_other by exact Hr'. apply HR.
Qed.

(* [comment removed for export] *)
Lemma hull_tight_free : forall l lo hi (a n : word) (x : Z),
  hull_tight_b l lo hi = true ->
  region_free l a n = true -> 0 < bv_unsigned n ->
  bv_unsigned a <= x < bv_unsigned a + bv_unsigned n -> lo <= x < hi -> False.
Proof.
  induction l as [|[b sz] r IH]; intros lo hi a n x Ht Hrf Hn Hx Hlh; cbn [hull_tight_b] in Ht.
  - apply Z.eqb_eq in Ht. lia.
  - apply andb_prop in Ht as [Hb Ht]. apply Z.eqb_eq in Hb.
    cbn [region_free forallb] in Hrf. apply andb_prop in Hrf as [Hov Hrf].
    pose proof (u64_range sz) as Rs.
    destruct (Z_lt_le_dec x (lo + bv_unsigned sz)) as [Hlt|Hge].
    + (* [comment removed for export] *)
      unfold iv_overlap in Hov. cbn [fst snd] in Hov. apply negb_true_iff in Hov.
      apply andb_false_iff in Hov as [Hov|Hov]; [apply Z.ltb_ge in Hov | apply Z.ltb_ge in Hov]; lia.
    + eapply (IH (lo + bv_unsigned sz) hi a n x Ht Hrf Hn Hx). lia.
Qed.

Lemma region_free_hull : forall model (a n : word),
  vm_reserved (m_vmmaps model) = segments_reserved SEGS ->
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) a n = true -> 0 < bv_unsigned n ->
  bv_unsigned a + bv_unsigned n <= img_lo A \/ img_hi A <= bv_unsigned a.
Proof.
  intros model a n Hres Hrf Hn. rewrite region_free_app in Hrf. apply andb_prop in Hrf as [Hrf _]. rewrite Hres in Hrf.
  pose proof HULL_ok' as (HU0 & _). destruct HULL_tight as [HT HNE].
  destruct (Z_lt_le_dec (bv_unsigned a + bv_unsigned n) (img_lo A + 1)) as [|H1]; [lia|].
  destruct (Z_lt_le_dec (bv_unsigned a) (img_hi A)) as [H2|]; [|lia].
  exfalso.
  (* [comment removed for export] *)
  destruct (Z_lt_le_dec (bv_unsigned a) (img_lo A)) as [H3|H3].
  - eapply (hull_tight_free _ _ _ a n (img_lo A) HT Hrf Hn); lia.
  - eapply (hull_tight_free _ _ _ a n (bv_unsigned a) HT Hrf Hn); lia.
Qed.

(* [comment removed for export] *)
Lemma grant_new_facts : forall E cs R FULL model (a n : word) nZ,
  CSOK E cs R FULL model ->
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) a n = true ->
  bv_unsigned n = nZ -> 0 < nZ -> bv_unsigned a + nZ <= alloc_top (m_vmmaps model) ->
  forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + nZ ->
    in_ivs (bv_unsigned x) (vm_maps (m_vmmaps model)) = false
    /\ in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)) = false
    /\ argH E x = false /\ in_hull A (bv_unsigned x) = false.
Proof.
  intros E cs R FULL model a n nZ HC Hrf Un HnZ Htop x Hx.
  pose proof (region_free_hull model a n (co_res _ _ _ _ _ _ _ _ _ _ _ HC) Hrf ltac:(lia)) as Hh0.
  rewrite region_free_app in Hrf. apply andb_prop in Hrf as [_ Hrf2].
  pose proof (region_free_sem _ a n (bv_unsigned x) Hrf2 ltac:(rewrite Un; lia) ltac:(rewrite Un; lia)) as M0.
  assert (N0 : in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)) = false).
  { destruct (in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model))) eqn:En; [|reflexivity]. exfalso.
    apply (co_nasub _ _ _ _ _ _ _ _ _ _ _ HC) in En. congruence. }
  assert (Hh : in_hull A (bv_unsigned x) = false).
  { unfold in_hull. apply andb_false_iff. destruct Hh0; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia. }
  repeat split; try assumption.
  destruct (argH E x) eqn:Ea; [|reflexivity]. exfalso. pose proof (argH_sp _ _ _ (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) Ea) as S.
  pose proof (co_isp _ _ _ _ _ _ _ _ _ _ _ HC) as I. unfold alloc_top in Htop. rewrite I in Htop.
  unfold APS.uE in S. unfold stack_max_size in Htop. lia.
Qed.

(* [comment removed for export] *)
Lemma grant_cs1_ok : forall E cs R FULL model kd (a n : word) nZ model' FULL' sr' R' knew be ne nhi (eager : bool) ylo' nx',
  CSOK E cs R FULL model ->
  bv_unsigned n = nZ -> 0 < nZ -> nZ mod 4096 = 0 -> bv_unsigned a mod 4096 = 0 ->
  bv_unsigned a + nZ <= alloc_top (m_vmmaps model) ->     (* [comment removed for export] *)
  (* [comment removed for export] *)
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) a n = true ->
  grant_post kd a n model model' -> grant_mem kd a n FULL FULL' ->
  regs_ok E sr' R' ->
  edenot E be = a -> edenot E ne = n ->
  know_ok SEGS E (MR E cs model' FULL') knew ->
  (kind_none kd || kind_lazy kd = negb eager)%bool -> is_tok_kind kd = false ->
  (plain A = true -> kind_lazy kd = false) ->     (* [comment removed for export] *)
  nZ <= nhi ->
  (eager = true -> a_eager cs + a_abytes cs + nhi <= LIMIT) ->
  ylo' <= a_ylo cs ->      (* [comment removed for export] *)
  (forall m, In m (a_maps cs) -> is_hole m = true ->      (* [comment removed for export] *)
     bv_unsigned a + nZ <= uE E (am_base m) \/ uE E (am_base m) + uE E (am_len m) <= bv_unsigned a) ->
  let cs1 := add_entry cs sr' (knew ++ kn_grant_filter A (kn cs) (a_maps cs)) nx' (AM be ne kd) nhi eager ylo' in
  CSOK E cs1 R' FULL' model'
  /\ (forall x : word, bv_unsigned x < bv_unsigned a \/ bv_unsigned a + nZ <= bv_unsigned x ->
        MR E cs1 model' FULL' x = MR E cs model FULL x)
  /\ MR E cs1 model' FULL' = MR E cs model' FULL'.
Proof.
  intros E cs R FULL model kd a n nZ model' FULL' sr' R' knew be ne nhi eager ylo' nx'
         HC Un HnZpos HnZal Hal Htop Hrf GPo [GM1 GM2] Hregs Hbase HneE Hknew Hkind Hkfog Hplain Hnhi Hbudget Hylo Hholes cs1.
  pose proof (u64_range a) as Ra.
  pose proof HULL_ok' as (HU0 & HU1 & HU2 & HU3).
  pose proof (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) as Hmaps.
  pose proof (maps_apart_of_region_free E (a_maps cs) model a n Hmaps Hrf) as Hapart. rewrite Un in Hapart.
  pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as Hwf.
  pose proof (region_free_hull model a n (co_res _ _ _ _ _ _ _ _ _ _ _ HC) Hrf ltac:(lia)) as Hhull. rewrite Un in Hhull.
  pose proof (co_isp _ _ _ _ _ _ _ _ _ _ _ HC) as Hisp0.
  assert (Hsp : bv_unsigned a + nZ <= APS.uE E e_sp0 - STK_BELOW).
  { unfold alloc_top, stack_max_size in Htop. rewrite Hisp0 in Htop. unfold APS.uE, STK_BELOW. lia. }
  assert (HaC' : bv_unsigned a + nZ <= 0x7FFFFF800000).   (* [comment removed for export] *)
  { pose proof (SINV_sp _ _ (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC)) as [_ Shi]. unfold sp_window_hi in Shi. unfold STK_BELOW in Hsp. lia. }
  pose proof (grant_new_facts E cs R FULL model a n nZ HC Hrf Un HnZpos Htop) as NEW.
  (* [comment removed for export] *)
  assert (VISOUT : forall x : word, bv_unsigned x < bv_unsigned a \/ bv_unsigned a + nZ <= bv_unsigned x ->
                    VIS E cs1 model' x = VIS E cs model x).
  { intros x Hx. eapply vis_grant_out; [exact GPo | reflexivity | rewrite Un; lia | exact Hal | rewrite Un; exact HnZal | rewrite Un; exact Hx]. }
  assert (HIDOUT : forall x : word, bv_unsigned x < bv_unsigned a \/ bv_unsigned a + nZ <= bv_unsigned x ->
                    HID E cs1 model' x = HID E cs model x).
  { intros x Hx. unfold hid. rewrite (VISOUT x Hx). reflexivity. }
  assert (MROUT : forall x : word, bv_unsigned x < bv_unsigned a \/ bv_unsigned a + nZ <= bv_unsigned x ->
                   MR E cs1 model' FULL' x = MR E cs model FULL x).
  { intros x Hx. unfold Mr, mrestrict. rewrite (HIDOUT x Hx). rewrite (GM1 x) by (rewrite Un; exact Hx). reflexivity. }
  assert (MRSAME : MR E cs1 model' FULL' = MR E cs model' FULL').
  { unfold Mr. rewrite (hid_ext A argH E cs cs1 model') by reflexivity. reflexivity. }
  split; [| split; [exact MROUT | exact MRSAME]].
  (* [comment removed for export] *)
  pose proof (grant_wf kd a n model model' GPo Hwf ltac:(rewrite Un; lia)) as Hwf'.
  destruct HC as [Xregs Xlog Xknow Xhalt Xfds Xfs Xtid Xres Xlimit Xmaps Xholes Xseps Xwf Xbounds Xlazyb Xnasub Xnone Xkinds Xtotsz Xisp Xbrk Xsbrk Xeager Xabytes Xminv Xzero Xsinv Xplain].
  constructor.
  all: unfold cs1, add_entry; cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn s_regs s_log s_know s_next mk_ss].
  all: try change (ALLOW E (ACS ?s ?m ?t ?y ?e (a_vis cs) (a_ghost cs) ?ab ?br ?fd ?ti)) with (ALLOW E cs).
  - (* [comment removed for export] *) exact Hregs.
  - (* [comment removed for export] *) reflexivity.
  - (* [comment removed for export] *) apply Forall_app. split.
    + unfold cs1, add_entry in MRSAME. cbn [kn a_ss s_know mk_ss] in MRSAME. rewrite MRSAME. exact Hknew.
    + eapply kn_grant_filter_ok; [exact Xknow | exact Hapart | lia | exact Hsp | exact Hhull | exact MROUT].
  - (* [comment removed for export] *) rewrite (gp_halted _ _ _ _ _ GPo). exact Xhalt.
  - (* [comment removed for export] *) unfold fds_ok in *. rewrite (gp_fds _ _ _ _ _ GPo), (gp_fs _ _ _ _ _ GPo). exact Xfds.
  - (* [comment removed for export] *) rewrite (gp_fs _ _ _ _ _ GPo). exact Xfs.
  - (* [comment removed for export] *) rewrite (gp_tid _ _ _ _ _ GPo). exact Xtid.
  - (* [comment removed for export] *) rewrite (gp_res _ _ _ _ _ GPo). exact Xres.
  - (* [comment removed for export] *) rewrite (gp_limit _ _ _ _ _ GPo). exact Xlimit.
  - (* [comment removed for export] *) rewrite (gp_maps _ _ _ _ _ GPo). rewrite <- Hbase, <- HneE. apply maps_match_cons; [exact Hkfog | exact Xmaps].
  - (* [comment removed for export] *)
    rewrite (gp_res _ _ _ _ _ GPo), (gp_maps _ _ _ _ _ GPo). apply Forall_cons.
    + intros Hh. exfalso. unfold is_hole in Hh. cbn [am_kind] in Hh. destruct kd; cbn in Hkfog, Hh; discriminate.
    + apply Forall_forall. intros m Hm Hk. destruct (proj1 (Forall_forall _ _) Xholes m Hm Hk) as [F1 F2]. split; [|lia].
      intros iv Hiv. apply in_app_iff in Hiv as [Hiv|[<-|Hiv]].
      * apply F1. apply in_app_iff. left. exact Hiv.
      * cbn [fst snd]. rewrite Un. pose proof (Hholes m Hm Hk). lia.
      * apply F1. apply in_app_iff. right. exact Hiv.
  - (* [comment removed for export] *) rewrite (gp_maps _ _ _ _ _ GPo). constructor; [|exact Xseps].
    apply Forall_forall. intros [b s] Hin. unfold iv_disjoint. cbn [fst snd]. rewrite Un.
    rewrite region_free_app in Hrf. apply andb_prop in Hrf as [_ Hrf2].
    pose proof (RefNodes.region_free_In _ a n b s Hrf2 Hin). rewrite Un in *. lia.
  - (* [comment removed for export] *) exact Hwf'.
  - (* [comment removed for export] *) rewrite (gp_maps _ _ _ _ _ GPo). unfold alloc_top in *. rewrite (gp_isp _ _ _ _ _ GPo).
    apply Forall_cons; [|exact Xbounds]. cbn [fst snd]. rewrite Un.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. lia.
  - (* [comment removed for export] *)
    rewrite (gp_lazy _ _ _ _ _ GPo). unfold alloc_top in *. rewrite (gp_isp _ _ _ _ _ GPo).
    destruct (kind_lazy kd); [|exact Xlazyb]. apply Forall_cons; [|exact Xlazyb]. cbn [fst snd]. rewrite Un. split; lia.
  - (* [comment removed for export] *) intros z Hz. rewrite (gp_maps _ _ _ _ _ GPo). rewrite in_ivs_cons. rewrite (gp_noacc _ _ _ _ _ GPo) in Hz.
    destruct (kind_none kd); [rewrite in_ivs_cons in Hz; apply orb_prop in Hz as [Hz|Hz]; [rewrite Hz; reflexivity|]|];
      rewrite (Xnasub z Hz); apply orb_true_r.
  - (* [comment removed for export] *) apply Forall_cons.
    + cbn [am_kind amap_den am_base am_len]. intros Hk. rewrite (gp_noacc _ _ _ _ _ GPo).
      replace (kind_none kd) with true by (destruct Hk as [-> | ->]; reflexivity). left. unfold amap_den. cbn [am_base am_len]. rewrite Hbase, HneE. reflexivity.
    + apply Forall_forall. intros m Hm Hk. rewrite (gp_noacc _ _ _ _ _ GPo).
      pose proof (proj1 (Forall_forall _ _) Xnone m Hm Hk) as X. destruct (kind_none kd); [right|]; exact X.
  - (* [comment removed for export] *) apply Forall_cons.
    + cbn [am_kind am_base am_len]. intros Hk x Hx. subst kd. rewrite Hbase, HneE, Un in Hx. cbn in Hkind.
      rewrite (gp_noacc _ _ _ _ _ GPo), (gp_lazy _ _ _ _ _ GPo). cbn [kind_none kind_lazy]. split.
      * exact (proj1 (proj2 (NEW x Hx))).
      * destruct (page_of_byte_in_aligned x (bv_unsigned a) (bv_unsigned a + nZ) Hal ltac:(rewrite Z.add_mod, Hal, HnZal by lia; reflexivity) Hx) as [P1 P2].
        apply page_in_ranges_cons_in; unfold page_size; rewrite ?Un; lia.
    + apply Forall_forall. intros m Hm Hk x Hx.
      destruct (proj1 (Forall_forall _ _) Xkinds m Hm Hk x Hx) as [K1 K2].
      rewrite (gp_noacc _ _ _ _ _ GPo), (gp_lazy _ _ _ _ _ GPo). split.
      * destruct (kind_none kd); [|exact K1]. rewrite in_ivs_cons. cbn [fst snd]. rewrite K1, Un.
        pose proof (Hapart m Hm ltac:(unfold is_fog; rewrite Hk; reflexivity)) as D.
        replace ((bv_unsigned a <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned a + nZ))%bool with false; [reflexivity|].
        symmetry. apply andb_false_iff. destruct D; [right; apply Z.ltb_ge | left; apply Z.leb_gt]; lia.
      * destruct (kind_lazy kd); [|exact K2]. rewrite page_in_ranges_cons, K2. apply orb_true_r.
  - (* [comment removed for export] *) rewrite (gp_res _ _ _ _ _ GPo), (gp_maps _ _ _ _ _ GPo).
    rewrite sum_sizes_app in *. cbn [sum_sizes snd]. rewrite Un. cbn [sum_sizes] in Xtotsz. lia.
  - (* [comment removed for export] *) rewrite (gp_isp _ _ _ _ _ GPo). exact Xisp.
  - (* [comment removed for export] *) rewrite (gp_brk _ _ _ _ _ GPo). exact Xbrk.
  - (* [comment removed for export] *) rewrite (gp_brk _ _ _ _ _ GPo), (gp_sbrk _ _ _ _ _ GPo). exact Xsbrk.
  - (* [comment removed for export] *) pose proof (grant_eager_le kd a n model model' GPo Xwf ltac:(rewrite Un; lia)) as EG. rewrite Hkind in EG.
    destruct eager; cbn [negb] in EG; [|lia]. rewrite Un in EG. lia.
  - (* [comment removed for export] *) exact Xabytes.
  - (* [comment removed for export] *) destruct Xminv as [N1 N2 N3 N4 N5]. constructor; rewrite ?(gp_mat _ _ _ _ _ GPo), ?(gp_limit _ _ _ _ _ GPo); try assumption.
    + intros p Hp. rewrite (gp_lazy _ _ _ _ _ GPo). destruct (kind_lazy kd); [rewrite page_in_ranges_cons, (N4 p Hp); apply orb_true_r | exact (N4 p Hp)].
    + pose proof (grant_eager_le kd a n model model' GPo Xwf ltac:(rewrite Un; lia)) as EG. rewrite Hkind in EG.
      destruct eager; cbn [negb] in EG; [|lia]. rewrite Un in EG. rewrite Xlimit. specialize (Hbudget eq_refl). lia.
  - (* [comment removed for export] *) intros x Hh Hm Hna Hlz Hgh.
    destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge]; [|destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + nZ)) as [Hlt2|Hge2]].
    + rewrite (GM1 x) by lia. apply Xzero; [rewrite <- (HIDOUT x) by lia; exact Hh | | | | exact Hgh].
      * rewrite (gp_maps _ _ _ _ _ GPo), in_ivs_cons in Hm. apply orb_prop in Hm as [Hm|Hm]; [|exact Hm].
        apply andb_prop in Hm as [Hm _]. apply Z.leb_le in Hm. cbn [fst] in Hm. lia.
      * rewrite (gp_noacc _ _ _ _ _ GPo) in Hna. destruct (kind_none kd); [rewrite in_ivs_cons in Hna; apply orb_false_iff in Hna as [_ Hna]|]; exact Hna.
      * rewrite (gp_lazy _ _ _ _ _ GPo) in Hlz. destruct (kind_lazy kd); [|exact Hlz].
        rewrite page_in_ranges_cons_out in Hlz; [exact Hlz | | rewrite Un; lia].
        pose proof (page_of_byte_out_aligned x (bv_unsigned a) (bv_unsigned a + nZ) Hal ltac:(rewrite Z.add_mod, Hal, HnZal by lia; reflexivity) ltac:(lia)). unfold page_size. rewrite Un. lia.
    + (* [comment removed for export] *) rewrite (GM2 x) by (rewrite Un; lia).
      rewrite (gp_noacc _ _ _ _ _ GPo) in Hna. destruct (kind_none kd); [|reflexivity].
      rewrite in_ivs_cons in Hna. cbn [fst snd] in Hna. apply orb_false_iff in Hna as [Hna _].
      apply andb_false_iff in Hna as [Hna|Hna]; [apply Z.leb_gt in Hna | apply Z.ltb_ge in Hna; rewrite Un in Hna]; lia.
    + rewrite (GM1 x) by (rewrite Un; lia). apply Xzero; [rewrite <- (HIDOUT x) by lia; exact Hh | | | | exact Hgh].
      * rewrite (gp_maps _ _ _ _ _ GPo), in_ivs_cons in Hm. apply orb_prop in Hm as [Hm|Hm]; [|exact Hm].
        apply andb_prop in Hm as [_ Hm]. apply Z.ltb_lt in Hm. cbn [fst snd] in Hm. rewrite Un in Hm. lia.
      * rewrite (gp_noacc _ _ _ _ _ GPo) in Hna. destruct (kind_none kd); [rewrite in_ivs_cons in Hna; apply orb_false_iff in Hna as [_ Hna]|]; exact Hna.
      * rewrite (gp_lazy _ _ _ _ _ GPo) in Hlz. destruct (kind_lazy kd); [|exact Hlz].
        rewrite page_in_ranges_cons_out in Hlz; [exact Hlz | | rewrite Un; lia].
        pose proof (page_of_byte_out_aligned x (bv_unsigned a) (bv_unsigned a + nZ) Hal ltac:(rewrite Z.add_mod, Hal, HnZal by lia; reflexivity) ltac:(lia)). unfold page_size. rewrite Un. lia.
  - (* [comment removed for export] *)
    eapply SINV_frame; [|exact Xsinv]. intros x Hx. apply GM1. pose proof (argH_sp _ _ _ Xsinv Hx). unfold APS.uE, STK_BELOW in *. rewrite Un. lia.
  - (* [comment removed for export] *) intros HP. rewrite (gp_lazy _ _ _ _ _ GPo), (Hplain HP). exact (Xplain HP).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma kmem_ok : forall E M b ne (lo n : Z),
  estart E (SA b 0) = lo -> elenZ E ne = n -> 0 <= lo < 2 ^ 64 -> 0 <= n -> lo + n <= 2 ^ 64 ->
  (forall x : word, lo <= bv_unsigned x < lo + n -> M x = Some (Z_to_bv 8 0)) ->
  know_ok SEGS E M [KWr (SA b 0) ne; KZero (SA b 0) ne].
Proof.
  intros E M b ne lo n Hs Hn Hlo Hn0 Hhi BYTE.
  assert (Hfl : flat E (SA b 0) (elenZ E ne)) by (unfold flat; rewrite Hs, Hn; lia).
  constructor; [|constructor; [|constructor]]; cbn [kentry_ok]; split; try exact Hfl; rewrite ?Hs, ?Hn.
  - intros d w Hd Hdw. destruct w as [|w']; [reflexivity|].
    apply store_ok_of_all; [rewrite u64_lit by lia; lia|].
    intros x Hx. rewrite u64_lit in Hx by lia. unfold wview. rewrite (BYTE x) by lia. discriminate.
  - intros i Hi. apply BYTE. rewrite u64_lit by lia. lia.
Qed.

Lemma kimg_in_hull_pure : forall k,
  Forall (fun K => match K with KImg _ _ => False | _ => True end) k -> kimg_in_hull A k.
Proof.
  intros k H. unfold kimg_in_hull. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) H K Hin) as HK. destruct K; try exact I. destruct HK.
Qed.

Lemma kdisj_new_pure : forall ms nb ne,
  Forall (fun K => match K with KImg _ _ => False | _ => True end) (kdisj_new A ms nb ne).
Proof.
  intros ms nb ne. unfold kdisj_new, kdisj_new0, kdisj_band. apply Forall_app. split.
  - apply Forall_flat_map. apply Forall_forall. intros m _.
    destruct (is_fog m); [apply Forall_nil|].
    destruct (am_base m); (apply Forall_cons; [exact I | apply Forall_nil]) || apply Forall_nil.
  - (* [comment removed for export] *) destruct (shadow_band A ms) as [[L0 L3]|]; [apply Forall_cons; [exact I | apply Forall_nil] | apply Forall_nil].
Qed.

(* [comment removed for export] *)
Lemma grant_vis_add : forall E cs1 cs2 base ne R FULL model (a n : word) nZ,
  CSOK E cs1 R FULL model ->
  vis_add A LIMIT cs1 base ne ([KWr (SA base 0) ne; KZero (SA base 0) ne] ++ kn cs1) = Some cs2 ->
  kimg_in_hull A (kn cs1) ->
  edenot E base = a -> edenot E ne = n -> bv_unsigned n = nZ -> 0 <= nZ -> bv_unsigned a + nZ <= 2 ^ 64 ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + nZ ->
     in_ivs (bv_unsigned x) (vm_maps (m_vmmaps model)) = true
     /\ in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)) = false
     /\ argH E x = false) ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + nZ -> FULL x = Some (Z_to_bv 8 0)) ->
  CSOK E cs2 R FULL model.
Proof.
  intros E cs1 cs2 base ne R FULL model a n nZ HC1 Hva Hkh Hbase Hne Un HnZ Hhi NEW ZERO.
  pose proof (u64_range a) as Ra.
  eapply vis_add_sound'; [exact Hva | exact HC1 |].
  destruct (vis_add_inv cs1 base ne _ cs2 Hva) as (nhi & Hnhi & Ecs2).
  apply Forall_app. split.
  - (* [comment removed for export] *)
    eapply (kmem_ok E _ base ne (bv_unsigned a) nZ); [unfold estart; cbn [a_base a_off]; rewrite Hbase; lia | unfold elenZ; rewrite Hne; exact Un | lia | lia | lia |].
    intros x Hx. destruct (NEW x Hx) as (N1 & N2 & N3).
    unfold Mr, mrestrict, hid. rewrite N3. cbn [orb].
    unfold vis. rewrite N1, N2. cbn [negb andb].
    assert (Hal : in_allow A E cs2 (bv_unsigned x) = true).
    { unfold in_allow, in_vis. rewrite Ecs2. cbn [a_vis existsb fst snd]. unfold uE. rewrite Hbase, Hne, Un.
      rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
    rewrite Hal. rewrite !orb_true_r. cbn [negb]. apply ZERO. exact Hx.
  - (* [comment removed for export] *)
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC1) as HK1. unfold Mr in HK1 |- *.
    eapply know_ok_unhide'; [apply H_off_segments_cs' | exact Hkh | | | exact HK1].
    + intros y Hy. rewrite Ecs2 in Hy. eapply hid_cons_sub. exact Hy.
    + intros y Hy. apply hid_hull'. exact Hy.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma gap_weight_eq : forall nZ l, gap_weight nZ l = sum_sizes l + Z.of_nat (length l) * (nZ + 4095).
Proof. induction l as [|[b sz] l IH]; cbn -[Z.of_nat Z.add Z.mul]; [lia|]. rewrite IH. rewrite Nat2Z.inj_succ. cbn [snd]. lia. Qed.

(* [comment removed for export] *)
Lemma gap_ok_sound : forall E cs R FULL model nhi nZ,
  CSOK E cs R FULL model -> gap_ok A cs nhi = true -> 0 < nZ <= nhi ->
  exists a : word, grant_ok_na_pin model a nZ = true.
Proof.
  intros E cs R FULL model nhi nZ HC Hg HnZ. unfold gap_ok in Hg. apply Z.leb_le in Hg.
  pose proof (co_totsz _ _ _ _ _ _ _ _ _ _ _ HC) as T.
  assert (L : (length (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) <= n_res A + length (a_maps cs))%nat).
  { rewrite length_app, (co_res _ _ _ _ _ _ _ _ _ _ _ HC), RES_len'. pose proof (maps_match_length E _ _ (co_maps _ _ _ _ _ _ _ _ _ _ _ HC)). lia. }
  assert (GW : gw_sizes (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) <= a_totsz cs).
  { pose proof (gap_weight_sizes nZ (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))) as G1.
    rewrite gap_weight_eq in G1. lia. }
  destruct (free_gap_of_totals (m_vmmaps model) nZ (a_totsz cs) ltac:(lia) GW) as (g & Hal & Hfl & Hc & Hfree & Hpl).
  { rewrite FLOOR_eq, CEIL_eq.
    assert (0 <= a_totsz cs).
    { assert (0 <= sum_sizes (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))); [|lia].
      clear. induction (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) as [|[b sz] l IH]; cbn; [lia|]. pose proof (u64_range sz). lia. }
    set (len1 := length (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))) in *.
    set (len2 := (n_res A + length (a_maps cs))%nat) in *.
    assert (Z.of_nat len1 * (nZ + 4095) <= Z.of_nat len2 * (nhi + 4095)) by nia. nia. }
  pose proof bottomup_floor_val as Hfv. pose proof alloc_ceiling_val as Hcv.
  assert (Hg64 : 0 <= g < 2 ^ 64) by lia.
  pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as (_ & _ & _ & Wsp).
  pose proof (alloc_ceiling_le_alloc_top _ Wsp) as Htop.
  exists (Z_to_bv 64 g). unfold grant_ok_na_pin. rewrite u64_lit by lia.
  rewrite Hfree. unfold page_size in Hal |- *.
  rewrite (proj2 (Z.eqb_eq _ _) Hal). rewrite (proj2 (Z.ltb_lt 0 g)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
Qed.

Lemma gap_ok_available : forall E cs R FULL model nhi nZ,
  CSOK E cs R FULL model -> gap_ok A cs nhi = true -> 0 < nZ <= nhi ->
  vm_gap_available (m_vmmaps model) nZ = true.
Proof.
  intros E cs R FULL model nhi nZ HC Hg HnZ.
  destruct (gap_ok_sound E cs R FULL model nhi nZ HC Hg HnZ) as [a Ha].
  exact (VmGap.vm_gap_available_complete (m_vmmaps model) nZ a ltac:(lia) Ha).
Qed.

Lemma budget_slack : forall E cs R FULL model extra,
  CSOK E cs R FULL model -> budget_ok LIMIT cs extra = true ->
  vm_backing_used model + extra <= vm_limit (m_vmmaps model).
Proof.
  intros E cs R FULL model extra HC Hb. unfold budget_ok in Hb. apply Z.leb_le in Hb.
  pose proof (vm_backing_used_le (ALLOW E cs) model (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) (A_wf_allowA' E cs)).
  pose proof (co_eager _ _ _ _ _ _ _ _ _ _ _ HC). pose proof (co_abytes _ _ _ _ _ _ _ _ _ _ _ HC).
  rewrite (co_limit _ _ _ _ _ _ _ _ _ _ _ HC). lia.
Qed.

Lemma lazy_interior_fresh : forall (a n : word),
  bv_unsigned a mod 4096 = 0 -> bv_unsigned n mod 4096 = 0 -> 0 < bv_unsigned n ->
  bv_unsigned a + bv_unsigned n <= 2 ^ 64 -> lazy_interior a n = [(a, n)].
Proof. intros. apply lazy_interior_aligned; unfold page_size; assumption. Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma refuse_eq : forall cs,
  refuse cs = with_ss cs (mk_ss (pc cs + 4) (sr_upd (s_regs (a_ss cs)) 10 (ELit ENOMEM_RET)) (kn cs) (nxt cs)).
Proof. reflexivity. Qed.

Lemma refuse_pc : forall cs, pc (refuse cs) = pc cs + 4.
Proof. reflexivity. Qed.

Lemma refuse_nxt : forall cs, nxt (refuse cs) = nxt cs.
Proof. reflexivity. Qed.

Lemma refuse_ok : forall E cs R FULL model,
  CSOK E cs R FULL model ->
  CSOK E (refuse cs) (regupd R (Z_to_bv 5 (Z.of_nat 10)) (errno_ret ENOMEM)) FULL model.
Proof.
  intros E cs R FULL model HC. rewrite refuse_eq.
  eapply cs_ok_frame'; [exact HC | apply same_but_materialized_refl | exact (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) | | reflexivity | exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC) | intros; reflexivity].
  cbn [s_regs mk_ss]. apply regs_ok_set_n'; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) | lia |].
  cbn [edenot]. rewrite errno_ret_ENOMEM. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma refuse_cont : forall cs E R FULL model TA,
  CSOK E cs R FULL model -> 0 <= pc cs -> pc cs + 4 < 2 ^ 64 ->
  (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' (refuse cs) R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (cfg R' (pc (refuse cs)) FULL' model') TA) ->
  srealizes SEGS (mkCfg (mkst (regupd R 10 (errno_ret ENOMEM)) (v_addi (Z_to_bv 64 (pc cs)) 4) FULL (seg_rom SEGS)) model) TA.
Proof.
  intros cs E R FULL model TA HC Hp0 Hp4 HKA.
  specialize (HKA E (regupd R (Z_to_bv 5 (Z.of_nat 10)) (errno_ret ENOMEM)) FULL model
                  (conj (env_agree_refl' _ _) (env_agree_refl' _ _)) (refuse_ok E cs R FULL model HC) eq_refl).
  unfold cfg_of in HKA. rewrite refuse_pc, <- bv5_10 in HKA. rewrite (v_addi_pc (pc cs) Hp0 Hp4). exact HKA.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma page_aligned_sound : forall E M k e,
  know_ok SEGS E M k -> page_aligned k e = true -> bv_unsigned (edenot E e) mod 4096 = 0.
Proof.
  intros E M k e HK H.
  assert (GEN : 12 <= ealign k e -> bv_unsigned (edenot E e) mod 4096 = 0).
  { intros Hle. destruct (ealign_sound SEGS E M k e HK) as [Hr [q Hq]]. rewrite Hq.
    replace (2 ^ ealign k e) with (2 ^ (ealign k e - 12) * 4096) by (rewrite <- (Z.pow_add_r 2 _ 12) by lia; f_equal; lia).
    rewrite Z.mul_assoc. apply Z.mod_mul. lia. }
  unfold page_aligned in H. destruct e as [z| | | | | | |]; try (apply GEN; apply Z.leb_le; exact H).
  apply Z.eqb_eq in H. cbn [edenot]. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  rewrite Z.mod_mod_divide; [exact H | exists (2 ^ 52); reflexivity].
Qed.

(* [comment removed for export] *)
Lemma fixed_args_sound : forall E cs R FULL model b off ne nlo nhi,
  CSOK E cs R FULL model -> fixed_args A cs = Some (b, off, ne, nlo, nhi) ->
  split_lit (reg cs 10) = (b, off) /\ mmap_len cs = Some (ne, nlo, nhi)
  /\ bv_unsigned (edenot E (reg cs 10)) mod 4096 = 0
  /\ 0 < bv_unsigned (edenot E (reg cs 10))
  /\ (bv_unsigned (edenot E (reg cs 10)) + nhi <= img_lo A \/ img_hi A <= bv_unsigned (edenot E (reg cs 10)))
  /\ bv_unsigned (edenot E (reg cs 10)) + nhi <= CEIL
  /\ getr R (Z_to_bv 5 (Z.of_nat 10)) = edenot E (reg cs 10)
  /\ flat_x (kn cs) b off ne = true.
Proof.
  intros E cs R FULL model b off ne nlo nhi HC H. unfold fixed_args in H.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  destruct (split_lit (reg cs 10)) as [b0 off0] eqn:Hsp.
  destruct (mmap_len cs) as [[[ne0 nlo0] nhi0]|] eqn:HML; [|discriminate].
  destruct (xlo (kn cs) (reg cs 10)) as [alo|] eqn:Hxl; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [ahi|] eqn:Hxh; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  apply andb_prop in Hc as [Hc Hflat].
  injection H as <- <- <- <- <-.
  apply andb_prop in Hc as [Hc Himg]. apply andb_prop in Hc as [Hc Htop]. apply andb_prop in Hc as [Hpa Hpos].
  apply Z.ltb_lt in Hpos. apply Z.leb_le in Htop.
  pose proof (xlo_sound SEGS E _ (kn cs) _ alo HK Hxl). pose proof (xhi_sound SEGS E _ (kn cs) _ ahi HK Hxh).
  split; [reflexivity|]. split; [reflexivity|]. split; [eapply page_aligned_sound; [exact HK | exact Hpa]|]. split; [lia|].
  split; [apply orb_prop in Himg as [Hi|Hi]; apply Z.leb_le in Hi; [left|right]; lia|]. split; [lia|].
  split; [apply (reg_sound' E cs R FULL model); [exact HC | lia] | exact Hflat].
Qed.

(* [comment removed for export] *)
Lemma fixed_args_in_sound : forall E cs R FULL model b off ne nlo nhi,
  CSOK E cs R FULL model -> fixed_args_in cs = Some (b, off, ne, nlo, nhi) ->
  split_lit (reg cs 10) = (b, off) /\ mmap_len cs = Some (ne, nlo, nhi)
  /\ bv_unsigned (edenot E (reg cs 10)) mod 4096 = 0
  /\ 0 < bv_unsigned (edenot E (reg cs 10))
  /\ bv_unsigned (edenot E (reg cs 10)) + nhi <= ATOP_MAX
  /\ getr R (Z_to_bv 5 (Z.of_nat 10)) = edenot E (reg cs 10)
  /\ flat_x (kn cs) b off ne = true.
Proof.
  intros E cs R FULL model b off ne nlo nhi HC H. unfold fixed_args_in in H.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  destruct (split_lit (reg cs 10)) as [b0 off0] eqn:Hsp.
  destruct (mmap_len cs) as [[[ne0 nlo0] nhi0]|] eqn:HML; [|discriminate].
  destruct (xlo (kn cs) (reg cs 10)) as [alo|] eqn:Hxl; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [ahi|] eqn:Hxh; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  apply andb_prop in Hc as [Hc Hflat].
  injection H as <- <- <- <- <-.
  apply andb_prop in Hc as [Hc Htop]. apply andb_prop in Hc as [Hpa Hpos].
  apply Z.ltb_lt in Hpos. apply Z.leb_le in Htop.
  pose proof (xlo_sound SEGS E _ (kn cs) _ alo HK Hxl). pose proof (xhi_sound SEGS E _ (kn cs) _ ahi HK Hxh).
  repeat split; try lia.
  - eapply page_aligned_sound; [exact HK | exact Hpa].
  - apply (reg_sound' E cs R FULL model); [exact HC | lia].
  - exact Hflat.
Qed.

(* [comment removed for export] *)
Lemma split_flat_estart : forall E M k e b off n,
  know_ok SEGS E M k -> split_lit e = (b, off) -> flat_x k b off n = true ->
  estart E (SA b off) = bv_unsigned (edenot E e)
  /\ estart E (SA b off) + bv_unsigned (edenot E n) <= 2 ^ 64 /\ 0 < bv_unsigned (edenot E n).
Proof.
  intros E M k e b off n HK Hsp Hfl.
  destruct (APS.flat_x_sound SEGS E M k b off n HK Hfl) as (F1 & F2 & F3).
  pose proof (APS.u_of_split E e b off Hsp ltac:(lia)). repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma region_free_of_apart : forall E cs R FULL model b off ne (lo n : word),
  CSOK E cs R FULL model -> no_fog (a_maps cs) = true ->
  forallb (fun m => ranges_apart_x (kn cs) b off ne (am_base m) 0 (am_len m)) (a_maps cs) = true ->
  estart E (SA b off) = bv_unsigned lo -> elenZ E ne = bv_unsigned n ->
  (bv_unsigned lo + bv_unsigned n <= img_lo A \/ img_hi A <= bv_unsigned lo) ->   (* [comment removed for export] *)
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) lo n = true.
Proof.
  intros E cs R FULL model b off ne lo n HC Hnf Hall Hs Hn Himg.
  rewrite region_free_app. apply andb_true_intro. split.
  - apply reserved_free_of_hull; [exact (co_res _ _ _ _ _ _ _ _ _ _ _ HC) | exact Himg].
  - rewrite (proj1 (maps_match_exact' E _ _ Hnf) (co_maps _ _ _ _ _ _ _ _ _ _ _ HC)). apply RefNodes.region_free_intro. intros bm sm Hin.
    apply in_map_iff in Hin as (m & Hm & Hinm). unfold amap_den in Hm. injection Hm as <- <-.
    pose proof (proj1 (forallb_forall _ _) Hall m Hinm) as Hap.
    pose proof (ranges_apart_x_sound SEGS E _ (kn cs) b off ne (am_base m) 0 (am_len m) (co_know _ _ _ _ _ _ _ _ _ _ _ HC) Hap) as D.
    unfold estart in D at 2 3. cbn [a_base a_off] in D. unfold elenZ in D, Hn. rewrite Hs, Hn in D. lia.
Qed.

Definition fixed_cs1 (cs : acs) (kd : mkind) (eager : bool) (ne : expr) (nhi : Z) : acs :=
  let k := kn cs in
  let m := AM (reg cs 10) ne kd in
  let ksh := if mkind_eqb kd KRWLAZY then flat_map (fun p => shadow_facts_in A k m (fst p) (snd p)) (a_vis cs) else [] in
  add_entry cs (s_regs (a_ss cs)) (ksh ++ kn_grant_filter A k (a_maps cs)) (nxt cs) m nhi eager (a_ylo cs).

(* [comment removed for export] *)
Lemma shadow_facts_new_ok : forall E cs R FULL model (a n : word) nZ ne model' FULL',
  CSOK E cs R FULL model ->
  bv_unsigned n = nZ -> edenot E ne = n -> bv_unsigned a + nZ <= CEIL -> edenot E (reg cs 10) = a ->
  grant_post KRWLAZY a n model model' -> grant_mem KRWLAZY a n FULL FULL' ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + nZ ->
     in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)) = false /\ argH E x = false) ->
  know_ok SEGS E (MR E cs model' FULL')
    (flat_map (fun p => shadow_facts_in A (kn cs) (AM (reg cs 10) ne KRWLAZY) (fst p) (snd p)) (a_vis cs)).
Proof.
  intros E cs R FULL model a n nZ ne model' FULL' HC Un Hne HaC Hra GPo [GM1 GM2] NEW.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (u64_range a) as Ra. pose proof SHADOW_ok' as SO.
  unfold know_ok. apply Forall_flat_map. apply Forall_forall. intros p Hp.
  unfold shadow_facts_in.
  destruct (shadow_of A (kn cs) (fst p) (snd p)) as [[sb sk] sn] eqn:Hsh.
  destruct (find_containing_j (kn cs) [AM (reg cs 10) ne KRWLAZY] [KRWLAZY] sb sk sn) as [m|] eqn:Hf; [|constructor].   (* [comment removed for export] *)
  unfold find_containing_j in Hf. cbn [find] in Hf.
  match type of Hf with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  apply andb_prop in Hc as [_ Hins]. cbn [am_base am_len] in Hins.
  pose proof (APS.xinside_j_sound SEGS E _ (kn cs) sb sk sn (reg cs 10) 0 ne HK Hins) as [I1 I2].
  unfold estart in I1, I2. cbn [a_base a_off] in I1, I2. rewrite Z.add_0_r in I1, I2. unfold elenZ in I2. rewrite Hne, Un in I2. rewrite Hra in I1, I2.
  pose proof HaC as HaC'. unfold CEIL in HaC'.
  (* [comment removed for export] *)
  unfold shadow_of in Hsh.
  destruct (split_lit (eadd (mkSrl (kn cs) (fst p) 3) (ELit (shadow_off A)))) as [sb' sk'] eqn:Hss. injection Hsh as -> -> <-.
  assert (Usn : bv_unsigned (edenot E (mkSrl (kn cs) (snd p) 3)) = bv_unsigned (edenot E (snd p)) / 8).
  { rewrite (mkSrl_denot SEGS E _ (kn cs) (snd p) 3 (Z_to_bv 64 3) HK) by (rewrite u64_lit by lia; reflexivity).
    rewrite u_srl64. rewrite u64_lit by lia. reflexivity. }
  rewrite Usn in I2.
  set (S0 := bv_unsigned (edenot E sb) + sk) in *.
  pose proof (u64_range (edenot E (fst p))) as Rb. pose proof (u64_range (edenot E (snd p))) as Rn.
  pose proof (u64_range (edenot E (mkSrl (kn cs) (snd p) 3))) as Rsn.
  assert (HS0 : S0 = shadow_off A + bv_unsigned (edenot E (fst p)) / 8).
  { pose proof (APS.split_lit_denot E _ sb sk Hss) as D. unfold eadd in D. rewrite mkAlu_denot in D. cbn [edenot] in D.
    apply (f_equal bv_unsigned) in D. rewrite u_add64 in D.
    rewrite (mkSrl_denot SEGS E _ (kn cs) (fst p) 3 (Z_to_bv 64 3) HK) in D by (rewrite u64_lit by lia; reflexivity).
    rewrite u_srl64 in D. fold S0 in D.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    rewrite !u64_lit in D by (unfold CEIL in *; lia).
    change (2 ^ (3 mod 64)) with 8 in D.
    rewrite (Z.mod_small (bv_unsigned (edenot E (fst p)) / 8 + shadow_off A)) in D by (unfold CEIL in *; lia).
    unfold CEIL in *. lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  (* [comment removed for export] *)
  assert (BYTE : forall y : word, S0 <= bv_unsigned y < S0 + bv_unsigned (edenot E (snd p)) / 8 ->
            MR E cs model' FULL' y = Some (Z_to_bv 8 0)).
  { intros y Hy.
    assert (Hya : bv_unsigned a <= bv_unsigned y < bv_unsigned a + nZ) by (clear -Hy I1 I2; lia).
    destruct (NEW y Hya) as [N1 N2].
    assert (Hsh2 : in_sh A E cs (bv_unsigned y) = true).
    { unfold in_sh. apply existsb_exists. exists p. split; [exact Hp|]. unfold sh_lo, sh_hi, uE.
      apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt].
      - lia.
      - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    assert (V : VIS E cs model' y = true).
    { unfold vis. rewrite (gp_maps _ _ _ _ _ GPo), (gp_noacc _ _ _ _ _ GPo). cbn [kind_none].
      rewrite in_ivs_cons. cbn [fst snd]. rewrite Un, N1.
      rewrite (proj2 (Z.leb_le (bv_unsigned a) (bv_unsigned y))) by lia.
      rewrite (proj2 (Z.ltb_lt (bv_unsigned y) (bv_unsigned a + nZ))) by lia.
      unfold in_allow. rewrite Hsh2. rewrite !orb_true_r. cbn [andb orb negb]. rewrite ?orb_true_r. reflexivity. }
    unfold Mr, mrestrict, hid. rewrite N2, V. cbn [orb negb].
    rewrite (GM2 y) by (rewrite Un; exact Hya). reflexivity. }
  assert (Hfl : flat E (SA sb sk) (elenZ E (mkSrl (kn cs) (snd p) 3))).
  { unfold flat, estart, elenZ. cbn [a_base a_off]. fold S0. rewrite Usn. unfold CEIL in *.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  constructor; [|constructor; [|constructor]]; cbn [kentry_ok]; split; try exact Hfl;
    unfold estart, elenZ; cbn [a_base a_off]; fold S0; rewrite Usn.
  - intros d w Hd Hdw. destruct w as [|w']; [reflexivity|].
    apply store_ok_of_all; [rewrite u64_lit by (unfold CEIL in *; lia); unfold CEIL in *; lia|].
    intros x Hx. rewrite u64_lit in Hx by (unfold CEIL in *; lia). unfold wview. rewrite (BYTE x) by lia. discriminate.
  - intros i Hi. apply BYTE. rewrite u64_lit by (unfold CEIL in *; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma fixed_pre : forall cs b off ne nlo nhi E R FULL model,
  CSOK E cs R FULL model ->
  fixed_args A cs = Some (b, off, ne, nlo, nhi) ->
  let addr := edenot E (reg cs 10) in
  let len := bv_unsigned (edenot E (reg cs 11)) in
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  edenot E ne = n /\ bv_unsigned n = nZ /\ estart E (SA b off) = bv_unsigned addr
  /\ bv_unsigned addr mod 4096 = 0 /\ 0 < bv_unsigned addr
  /\ (bv_unsigned addr + nZ <= img_lo A \/ img_hi A <= bv_unsigned addr)
  /\ bv_unsigned addr + nZ <= CEIL
  /\ getr R (Z_to_bv 5 (Z.of_nat 10)) = addr /\ nZ mod 4096 = 0 /\ 0 < nZ <= nhi.
Proof.
  intros cs b off ne nlo nhi E R FULL model HC HFA addr len nZ n.
  destruct (fixed_args_sound E cs R FULL model b off ne nlo nhi HC HFA) as (Hsp & HML & Hal & Hpos & Himg & HtopA & R10 & Hflat).
  fold addr in Hal, Hpos, Himg, HtopA, R10.
  destruct (mmap_len_sound E cs R FULL model ne nlo nhi HC HML) as (R11 & Hlen & Hne & Hnlo & HnZ & HnZal & HneE).
  fold len in R11, Hlen, Hne, HnZ, HnZal. fold nZ in Hne, HnZ, HnZal. fold n in Hne.
  pose proof (page_round_up_Z_bounds len ltac:(lia)) as PB. fold nZ in PB. unfold page_size in PB.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  destruct (split_flat_estart E _ (kn cs) (reg cs 10) b off ne HK Hsp Hflat) as (Hest & Hfl2 & Hfl3). fold addr in Hest.
  pose proof (u64_range addr) as Ra.
  assert (Un0 : bv_unsigned n = nZ).
  { subst n. apply u64_lit. split; [lia|]. pose proof (u64_range (Z_to_bv 64 nZ)) as Rn. unfold CEIL in HtopA. lia. }
  split; [exact Hne|]. split; [exact Un0|]. split; [exact Hest|]. split; [exact Hal|]. split; [exact Hpos|].
  split; [destruct Himg; [left|right]; lia|]. split; [lia|]. split; [exact R10|]. split; [exact HnZal | lia].
Qed.

(* [comment removed for export] *)
Lemma maps_match_unhole : forall E ms h l, maps_match E ms l <-> maps_match E (unhole ms h) l.
Proof.
  intros E ms h. unfold unhole. induction ms as [|m ms IH]; intros l; [cbn; tauto|].
  cbn [List.map maps_match].
  destruct (is_hole m && amap_eqb m h)%bool eqn:Hc.
  - apply andb_prop in Hc as [Hh _].
    assert (Hf : is_fog m = true) by (unfold is_fog, is_hole in *; destruct (am_kind m); cbn in Hh |- *; congruence).
    rewrite Hf. cbn [is_fog is_tok_kind am_kind am_len].
    split; (intros [H|(iv & l' & H1 & H2 & H3)]; [left; apply IH; exact H | right; exists iv, l'; split; [exact H1|]; split; [exact H2| apply IH; exact H3]]).
  - destruct (is_fog m).
    + split; (intros [H|(iv & l' & H1 & H2 & H3)]; [left; apply IH; exact H | right; exists iv, l'; split; [exact H1|]; split; [exact H2| apply IH; exact H3]]).
    + split; (intros (l' & H1 & H2); exists l'; split; [exact H1 | apply IH; exact H2]).
Qed.

(* [comment removed for export] *)
Lemma same_val_sound : forall E M k a b,
  know_ok SEGS E M k -> same_val k a b = true -> bv_unsigned (edenot E a) = bv_unsigned (edenot E b).
Proof.
  intros E M k a b HK H. unfold same_val in H.
  destruct (expr_eqb a b) eqn:He; [apply expr_eqb_eq in He; subst; reflexivity|].
  destruct (lin_ge0 k [(a, 0)] [(b, 0)]) eqn:H1; [|discriminate].
  pose proof (lin_ge0_sound SEGS E M k _ _ HK H1) as X1. pose proof (lin_ge0_sound SEGS E M k _ _ HK H) as X2.
  cbn [xt_den] in X1, X2. lia.
Qed.

(* [comment removed for export] *)
Lemma find_hole_sound : forall E M k ms a ne h,
  know_ok SEGS E M k -> find_hole k ms a ne = Some h ->
  In h ms /\ is_hole h = true
  /\ uE E (am_base h) = bv_unsigned (edenot E a) /\ uE E (am_len h) = bv_unsigned (edenot E ne).
Proof.
  intros E M k ms a ne h HK H. unfold find_hole in H. apply find_some in H as [Hin Hc].
  apply andb_prop in Hc as [Hc H2]. apply andb_prop in Hc as [Hh H1].
  split; [exact Hin|]. split; [exact Hh|]. unfold uE.
  split; symmetry; [exact (same_val_sound E M k _ _ HK H1) | exact (same_val_sound E M k _ _ HK H2)].
Qed.

(* [comment removed for export] *)
Lemma cs_ok_unhole : forall E cs R FULL model h,
  CSOK E cs R FULL model -> CSOK E (with_maps0 cs (unhole (a_maps cs) h)) R FULL model.
Proof.
  intros E cs R FULL model h HC.
  assert (ELEM : forall m, In m (unhole (a_maps cs) h) ->
            In m (a_maps cs) \/ exists m0, In m0 (a_maps cs) /\ m = AM (am_base m0) (am_len m0) KFOG).
  { intros m Hm. unfold unhole in Hm. apply in_map_iff in Hm as (m0 & Hm0 & Hin).
    destruct (is_hole m0 && amap_eqb m0 h)%bool; [right; exists m0; split; [exact Hin | symmetry; exact Hm0] | left; subst; exact Hin]. }
  destruct HC as [Xregs Xlog Xknow Xhalt Xfds Xfs Xtid Xres Xlimit Xmaps Xholes Xseps Xwf Xbounds Xlazyb Xnasub Xnone Xkinds Xtotsz Xisp Xbrk Xsbrk Xeager Xabytes Xminv Xzero Xsinv Xplain].
  constructor; unfold with_maps0 in *;
    cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn] in *; try assumption.
  - (* [comment removed for export] *) apply (proj1 (maps_match_unhole E _ h _)). exact Xmaps.
  - (* [comment removed for export] *) apply Forall_forall. intros m Hm Hk. destruct (ELEM m Hm) as [Hin|(m0 & Hin & ->)];
      [exact (proj1 (Forall_forall _ _) Xholes m Hin Hk) | cbn in Hk; discriminate].
  - (* [comment removed for export] *) apply Forall_forall. intros m Hm Hk. destruct (ELEM m Hm) as [Hin|(m0 & Hin & ->)];
      [exact (proj1 (Forall_forall _ _) Xnone m Hin Hk) | cbn in Hk; destruct Hk; discriminate].
  - (* [comment removed for export] *) apply Forall_forall. intros m Hm Hk. destruct (ELEM m Hm) as [Hin|(m0 & Hin & ->)];
      [exact (proj1 (Forall_forall _ _) Xkinds m Hin Hk) | cbn in Hk; discriminate].
Qed.

(* [comment removed for export] *)
Lemma mmap_fixed_grant_cs1 : forall cs ms0 kd (eager : bool) b off ne nlo nhi E R FULL model model' FULL',
  CSOK E cs R FULL model ->
  fixed_args A cs = Some (b, off, ne, nlo, nhi) ->      (* [comment removed for export] *)
  CSOK E (with_maps0 cs ms0) R FULL model ->
  let addr := edenot E (reg cs 10) in
  let len := bv_unsigned (edenot E (reg cs 11)) in
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  (forall m, In m ms0 -> is_hole m = true ->
     bv_unsigned addr + nZ <= uE E (am_base m) \/ uE E (am_base m) + uE E (am_len m) <= bv_unsigned addr) ->
  (* [comment removed for export] *)
  (eager = true -> a_eager cs + a_abytes cs + nhi <= LIMIT) ->
  (kind_none kd || kind_lazy kd = negb eager)%bool -> is_tok_kind kd = false ->
  (plain A = true -> kind_lazy kd = false) ->
  grant_post kd addr n model model' -> grant_mem kd addr n FULL FULL' ->
  CSOK E (fixed_cs1 (with_maps0 cs ms0) kd eager ne nhi) (regupd R (Z_to_bv 5 (Z.of_nat 10)) addr) FULL' model'
  /\ (forall x : word, bv_unsigned addr <= bv_unsigned x < bv_unsigned addr + nZ ->
        in_ivs (bv_unsigned x) (vm_maps (m_vmmaps model')) = true
        /\ in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)) = false /\ argH E x = false).
Proof.
  intros cs ms0 kd eager b off ne nlo nhi E R FULL model model' FULL' HC HFA HC0 addr len nZ n Hrf Hholes Hbudget Hkind Hkfog Hplain GPo GM.
  destruct (fixed_pre cs b off ne nlo nhi E R FULL model HC HFA) as (Hne & Un & Hest & Hal & Hpos & Himg & HtopA & R10 & HnZal & HnZ).
  fold addr len nZ n in Hne, Un, Hest, Hal, Hpos, Himg, HtopA, R10, HnZal, HnZ.
  assert (HaC : bv_unsigned addr + nZ <= CEIL) by lia.
  assert (HnZpos : 0 < nZ) by lia.
  pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as (_ & _ & _ & Wsp0). pose proof (alloc_ceiling_le_alloc_top _ Wsp0) as HAT. pose proof CEIL_eq as CE.
  assert (Htop2 : bv_unsigned addr + nZ <= alloc_top (m_vmmaps model)) by lia.
  pose proof (grant_new_facts E cs R FULL model addr n nZ HC Hrf Un HnZpos Htop2) as NEW.
  destruct (grant_cs1_ok E (with_maps0 cs ms0) R FULL model kd addr n nZ model' FULL'
              (s_regs (a_ss cs)) (regupd R (Z_to_bv 5 (Z.of_nat 10)) addr)
              (if mkind_eqb kd KRWLAZY then flat_map (fun p => shadow_facts_in A (kn cs) (AM (reg cs 10) ne kd) (fst p) (snd p)) (a_vis cs) else [])
              (reg cs 10) ne nhi eager (a_ylo cs) (nxt cs)
              HC0 Un HnZpos HnZal Hal Htop2 Hrf GPo GM) as (HC1 & MROUT & MRSAME).
  - apply regs_ok_regupd_same; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) | lia | exact R10].
  - reflexivity.
  - exact Hne.
  - destruct kd; cbn [mkind_eqb]; try constructor.
    change (MR E (with_maps0 cs ms0) model' FULL') with (MR E cs model' FULL').
    eapply shadow_facts_new_ok; [exact HC | exact Un | exact Hne | exact HaC | reflexivity | exact GPo | exact GM |].
    intros x Hx. destruct (NEW x Hx) as (_ & N1 & N2 & _). auto.
  - exact Hkind.
  - exact Hkfog.
  - exact Hplain.
  - lia.
  - exact Hbudget.
  - cbn [with_maps0 a_ylo]. lia.
  - cbn [with_maps0 a_maps]. exact Hholes.
  - split; [exact HC1|].
    intros x Hx. destruct (NEW x Hx) as (N0 & N1 & N2 & _). split; [|auto].
    rewrite (gp_maps _ _ _ _ _ GPo), in_ivs_cons. cbn [fst snd]. rewrite Un.
    apply orb_true_iff. left. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

(* [comment removed for export] *)
Lemma mmap_fixed_old_facts : forall cs b off ne nlo nhi E R FULL model,
  CSOK E cs R FULL model ->
  fixed_args A cs = Some (b, off, ne, nlo, nhi) ->
  no_fog (a_maps cs) = true ->
  forallb (fun m => ranges_apart_x (kn cs) b off ne (am_base m) 0 (am_len m)) (a_maps cs) = true ->
  let addr := edenot E (reg cs 10) in
  let nZ := page_round_up_Z (bv_unsigned (edenot E (reg cs 11))) in
  CSOK E (with_maps0 cs (a_maps cs)) R FULL model
  /\ region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr (Z_to_bv 64 nZ) = true
  /\ (forall m, In m (a_maps cs) -> is_hole m = true ->
        bv_unsigned addr + nZ <= uE E (am_base m) \/ uE E (am_base m) + uE E (am_len m) <= bv_unsigned addr).
Proof.
  intros cs b off ne nlo nhi E R FULL model HC HFA Hnf Hall addr nZ.
  destruct (fixed_pre cs b off ne nlo nhi E R FULL model HC HFA) as (Hne & Un & Hest & Hal & Hpos & Himg & HtopA & R10 & HnZal & HnZ).
  fold addr nZ in Hne, Un, Hest, Hal, Hpos, Himg, HtopA, R10, HnZal, HnZ.
  split; [|split].
  - destruct cs; exact HC.
  - eapply region_free_of_apart; [exact HC | exact Hnf | exact Hall | exact Hest | unfold elenZ; rewrite Hne; reflexivity | rewrite Un; exact Himg].
  - intros m Hm Hk. exfalso. unfold no_fog in Hnf. pose proof (proj1 (forallb_forall _ _) Hnf m Hm) as X.
    apply negb_true_iff in X. unfold is_fog, is_hole in *. destruct (am_kind m); cbn in X, Hk; congruence.
Qed.

(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma seps_map_disjoint : forall (f : amap -> word * word) ms m m',
  seps (map f ms) -> In m ms -> In m' ms -> m <> m' -> iv_disjoint (f m) (f m').
Proof.
  intros f ms. induction ms as [|h t IH]; intros m m' Hs Hm Hm' Hne; [destruct Hm|].
  cbn [map] in Hs. inversion Hs as [|p l Hf Hl]; subst.
  destruct Hm as [<-|Hm]; destruct Hm' as [<-|Hm'].
  - exfalso. exact (Hne eq_refl).
  - exact (proj1 (Forall_forall _ _) Hf (f m') (in_map f t m' Hm')).
  - pose proof (proj1 (Forall_forall _ _) Hf (f m) (in_map f t m Hm)) as D. unfold iv_disjoint in *. lia.
  - exact (IH m m' Hl Hm Hm' Hne).
Qed.

(* [comment removed for export] *)
Lemma maps_match_disjoint : forall E ms l m m',
  maps_match E ms l -> seps l -> In m ms -> In m' ms -> is_fog m = false -> is_fog m' = false -> m <> m' ->
  iv_disjoint (amap_den E m) (amap_den E m').
Proof.
  intros E ms. induction ms as [|h t IH]; intros l m m' HM Hs Hm Hm' Hf Hf' Hne; [destruct Hm|].
  cbn [maps_match] in HM. destruct (is_fog h) eqn:Hfh.
  - assert (Hmt : In m t) by (destruct Hm as [<-|Hm]; [congruence | exact Hm]).
    assert (Hmt' : In m' t) by (destruct Hm' as [<-|Hm']; [congruence | exact Hm']).
    destruct HM as [HM|(iv & l' & -> & _ & HM)].
    + exact (IH l m m' HM Hs Hmt Hmt' Hf Hf' Hne).
    + inversion Hs as [|p l0 Hfa Hl]; subst. exact (IH l' m m' HM Hl Hmt Hmt' Hf Hf' Hne).
  - destruct HM as (l' & -> & HM). inversion Hs as [|p l0 Hfa Hl]; subst.
    destruct Hm as [<-|Hm]; destruct Hm' as [<-|Hm'].
    + exfalso. exact (Hne eq_refl).
    + exact (proj1 (Forall_forall _ _) Hfa (amap_den E m') (maps_match_In E t l' m' HM Hm' Hf')).
    + pose proof (proj1 (Forall_forall _ _) Hfa (amap_den E m) (maps_match_In E t l' m HM Hm Hf)) as D. unfold iv_disjoint in *. lia.
    + exact (IH l' m m' HM Hl Hm Hm' Hf Hf' Hne).
Qed.

(* [comment removed for export] *)
Lemma overlap_sum_contained : forall l (b s : word) lo hi,
  seps l -> In (b, s) l -> bv_unsigned b <= lo -> hi <= bv_unsigned b + bv_unsigned s -> lo <= hi ->
  overlap_sum l lo hi <= hi - lo.
Proof.
  intros l b s lo hi Hs Hin H1 H2 Hlh. induction l as [|p l IH]; [destruct Hin|].
  inversion Hs as [|p' l' Hf Hl]; subst. rewrite overlap_sum_cons. destruct Hin as [->|Hin].
  - pose proof (iv_count_in_rng_le (b, s) lo hi Hlh).
    assert (Z0 : overlap_sum l lo hi = 0); [|lia].
    clear IH Hs. revert Hf Hl. induction l as [|q l IH2]; intros Hf Hl; [reflexivity|]. rewrite overlap_sum_cons.
    apply Forall_cons_iff in Hf as [Hq Hf']. inversion Hl; subst.
    rewrite (IH2 Hf' ltac:(assumption)). rewrite iv_count_in_rng_disjoint; [lia|].
    unfold iv_disjoint, B, S in *. cbn [fst snd] in Hq. lia.
  - pose proof (IH Hl Hin) as IH'. rewrite iv_count_in_rng_disjoint; [lia|].
    pose proof (proj1 (Forall_forall _ _) Hf (b, s) Hin) as D. unfold iv_disjoint, B, S in *. cbn [fst snd] in D. lia.
Qed.

Lemma rekind_den : forall E ms m, map (amap_den E) (rekind ms m) = map (amap_den E) ms.
Proof.
  intros E ms m. unfold rekind. rewrite map_map. apply map_ext. intros m'. destruct (amap_eqb m' m); reflexivity.
Qed.

Lemma in_rekind : forall ms m m', In m' (rekind ms m) ->
  exists m0, In m0 ms /\ ((m0 = m /\ m' = AM (am_base m) (am_len m) KRW) \/ (m0 <> m /\ m' = m0)).
Proof.
  intros ms m m' H. unfold rekind in H. apply in_map_iff in H as (m0 & Hm0 & Hin). exists m0. split; [exact Hin|].
  destruct (amap_eqb m0 m) eqn:He.
  - left. apply APS.amap_eqb_eq in He. subst m0. auto.
  - right. split; [|symmetry; exact Hm0]. intros ->. rewrite amap_eqb_refl in He. discriminate.
Qed.

Lemma covered_maps_subtract : forall l lo hi x,
  ivs_wf l -> lo <= hi ->
  covered (maps_subtract l lo hi) x = (covered l x && negb (in_rng lo hi x))%bool.
Proof. intros. apply (proj2 (proj2 (maps_subtract_sem l lo hi H H0))). Qed.

Inductive slarm := SlE | SlF | SlG | SlM.

Definition sl_nn (s : slarm) : bool := match s with SlG => true | _ => false end.
Definition sl_charge (s : slarm) : bool := match s with SlE | SlM => true | _ => false end.

Record slice_post (s : slarm) (addr n : word) (model model' : Model) : Prop := SP {
  sp_maps : vm_maps (m_vmmaps model') = vm_maps (m_vmmaps model);
  sp_res : vm_reserved (m_vmmaps model') = vm_reserved (m_vmmaps model);
  sp_noacc : vm_noaccess (m_vmmaps model') =
             (if sl_nn s then [(addr, n)] else [])
               ++ maps_subtract (vm_noaccess (m_vmmaps model)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n);
  sp_lazy : m_vm_lazy model' =
            match s with
            | SlM => m_vm_lazy model
            | SlF => (addr, n) :: maps_subtract (m_vm_lazy model) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
            | _ => maps_subtract (m_vm_lazy model) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
            end;
  sp_mat : m_vm_materialized model' =
           match s with
           | SlM => m_vm_materialized model
           | _ => List.filter (page_outside_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)) (m_vm_materialized model)
           end;
  sp_limit : vm_limit (m_vmmaps model') = vm_limit (m_vmmaps model);
  sp_brk : vm_brk (m_vmmaps model') = vm_brk (m_vmmaps model);
  sp_sbrk : vm_start_brk (m_vmmaps model') = vm_start_brk (m_vmmaps model);
  sp_mbase : vm_mmap_base (m_vmmaps model') = vm_mmap_base (m_vmmaps model);
  sp_halted : m_halted model' = m_halted model;
  sp_fds : m_fds model' = m_fds model;
  sp_fs : m_fs model' = m_fs model;
  sp_tid : m_tid model' = m_tid model;
  sp_isp : vm_init_sp (m_vmmaps model') = vm_init_sp (m_vmmaps model)  (* [comment removed for export] *) }.

Definition slice_mem (s : slarm) (addr n : word) (FULL FULL' : word -> option byte) : Prop :=
  (forall x : word, bv_unsigned x < bv_unsigned addr \/ bv_unsigned addr + bv_unsigned n <= bv_unsigned x -> FULL' x = FULL x)
  /\ (forall x : word, bv_unsigned addr <= bv_unsigned x < bv_unsigned addr + bv_unsigned n ->
        FULL' x = if sl_nn s then None else Some (Z_to_bv 8 0)).

(* [comment removed for export] *)
Record slice_hyps (E : env) (cs : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model)
       (s : slarm) (m : amap) (addr n : word) (nZ : Z) (model' : Model) (FULL' : word -> option byte) : Prop := SH_ {
  sh_C : CSOK E cs R FULL model;
  sh_m : In m (a_maps cs);
  sh_nf : is_fog m = false;
  sh_Un : bv_unsigned n = nZ;
  sh_pos : 0 < nZ;
  sh_nal : nZ mod 4096 = 0;
  sh_al : bv_unsigned addr mod 4096 = 0;
  sh_in1 : bv_unsigned (edenot E (am_base m)) <= bv_unsigned addr;
  sh_in2 : bv_unsigned addr + nZ <= bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m));
  sh_post : slice_post s addr n model model';
  sh_mem : slice_mem s addr n FULL FULL';
  sh_F : s = SlF -> am_kind m = KRWLAZY;
  sh_nF : s <> SlF -> am_kind m <> KRWLAZY }.

Section Slice.
  Variables (E : env) (cs : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Variables (s : slarm) (m : amap) (addr n : word) (nZ : Z) (model' : Model) (FULL' : word -> option byte).
  Hypothesis SH : slice_hyps E cs R FULL model s m addr n nZ model' FULL'.
  Let HC := sh_C _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let Hm := sh_m _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let Hnf := sh_nf _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let Un := sh_Un _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let HnZpos := sh_pos _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let HnZal := sh_nal _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let Hal := sh_al _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let Hin1 := sh_in1 _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let Hin2 := sh_in2 _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let SPo := sh_post _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let SM := sh_mem _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let HF := sh_F _ _ _ _ _ _ _ _ _ _ _ _ SH.
  Let HnF := sh_nF _ _ _ _ _ _ _ _ _ _ _ _ SH.

  Let lo := bv_unsigned addr.
  Let hi := bv_unsigned addr + nZ.

  (* [comment removed for export] *)
  Lemma sl_bounds : 0 < bv_unsigned (edenot E (am_len m)) /\ bv_unsigned (edenot E (am_base m)) mod 4096 = 0
                    /\ bv_unsigned (edenot E (am_len m)) mod 4096 = 0
                    /\ (bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= img_lo A \/ img_hi A <= bv_unsigned (edenot E (am_base m)))
                    /\ bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= alloc_top (m_vmmaps model).
  Proof.
    pose proof (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) as B.
    destruct (proj1 (Forall_forall _ _) B (amap_den E m) (maps_match_In E _ _ m (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) Hm Hnf)) as (B1 & B2 & B3 & B4 & B5).
    unfold amap_den in *. cbn [fst snd] in *. repeat split; assumption.
  Qed.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma sl_F_asan : s = SlF -> plain A = false.
  Proof.
    intros Hs. destruct (plain A) eqn:P; [|reflexivity]. exfalso.
    pose proof sl_bounds as (B1 & _).
    destruct (proj1 (Forall_forall _ _) (co_kinds _ _ _ _ _ _ _ _ _ _ _ HC) m Hm (HF Hs) (edenot E (am_base m)) ltac:(lia)) as [_ K2].
    rewrite (co_plain _ _ _ _ _ _ _ _ _ _ _ HC P) in K2. cbn in K2. discriminate.
  Qed.

  (* [comment removed for export] *)
  Lemma sl_top : alloc_top (m_vmmaps model) <= 0x7FFFFF800000.
  Proof.
    pose proof (SINV_sp _ _ (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC)) as [_ Shi]. pose proof (co_isp _ _ _ _ _ _ _ _ _ _ _ HC) as I.
    unfold alloc_top, stack_max_size. rewrite I. unfold APS.uE, sp_window_hi in Shi. lia.
  Qed.

  Lemma sl_lohi : (hi <= img_lo A \/ img_hi A <= lo) /\ hi <= alloc_top (m_vmmaps model) /\ lo < hi /\ hi <= 2 ^ 64 /\ lo mod 4096 = 0 /\ hi mod 4096 = 0.
  Proof.
    pose proof sl_bounds as (B1 & B2 & B3 & B4 & B5). pose proof sl_top as T. subst lo hi.
    repeat split; try lia. rewrite Z.add_mod, Hal, HnZal by lia. reflexivity.
  Qed.

  Lemma sl_in_maps : forall x : word, lo <= bv_unsigned x < hi -> in_ivs (bv_unsigned x) (vm_maps (m_vmmaps model)) = true.
  Proof.
    intros x Hx. eapply in_ivs_maps_match; [exact (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) | exact Hm | exact Hnf |]. subst lo hi. lia.
  Qed.

  Lemma sl_wf' : model_ivs_wf model'.
  Proof.
    pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as (W1 & W2 & W3 & Wsp). pose proof sl_lohi as (L1 & L2 & L3 & L4 & L5 & L6).
    assert (iv_wf (addr, n)) by (unfold iv_wf, B, S; cbn; subst lo hi; lia).
    unfold model_ivs_wf. rewrite (sp_maps _ _ _ _ _ SPo), (sp_noacc _ _ _ _ _ SPo), (sp_lazy _ _ _ _ _ SPo).
    split; [exact W1|]. split; [|split; [|unfold init_sp_ok in *; rewrite (sp_isp _ _ _ _ _ SPo); exact Wsp]].
    - apply ivs_wf_app; [destruct (sl_nn s); [apply ivs_wf_cons; [assumption | apply ivs_wf_nil] | apply ivs_wf_nil] |].
      apply maps_subtract_wf; [exact W2 | rewrite Un; lia].
    - destruct s; try exact W3; try (apply ivs_wf_cons; [assumption|]); apply maps_subtract_wf; try assumption; rewrite Un; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sl_noacc_out : forall x : word, bv_unsigned x < lo \/ hi <= bv_unsigned x ->
    in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model')) = in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)).
  Proof.
    intros x Hx. pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as (W1 & W2 & W3 & _).
    rewrite (sp_noacc _ _ _ _ _ SPo), in_ivs_app. rewrite !in_ivs_covered.
    rewrite covered_maps_subtract by (try exact W2; rewrite Un; lia). rewrite Un.
    replace (in_rng (bv_unsigned addr) (bv_unsigned addr + nZ) (bv_unsigned x)) with false
      by (symmetry; unfold in_rng; apply andb_false_iff; subst lo hi; destruct Hx; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
    destruct (sl_nn s); cbn [app]; [|rewrite andb_true_r; reflexivity].
    rewrite <- in_ivs_covered, in_ivs_cons. cbn [fst snd in_ivs existsb]. rewrite Un.
    replace ((bv_unsigned addr <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned addr + nZ))%bool with false
      by (symmetry; apply andb_false_iff; subst lo hi; destruct Hx; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
    cbn [orb]. rewrite andb_true_r. reflexivity.
  Qed.

  Lemma sl_noacc_in : forall x : word, lo <= bv_unsigned x < hi ->
    in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model')) = sl_nn s.
  Proof.
    intros x Hx. pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as (W1 & W2 & W3 & _).
    rewrite (sp_noacc _ _ _ _ _ SPo), in_ivs_app. rewrite (in_ivs_covered _ (maps_subtract _ _ _)).
    rewrite covered_maps_subtract by (try exact W2; rewrite Un; lia). rewrite Un.
    replace (in_rng (bv_unsigned addr) (bv_unsigned addr + nZ) (bv_unsigned x)) with true
      by (symmetry; unfold in_rng; apply andb_true_intro; subst lo hi; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    cbn [negb]. rewrite andb_false_r, orb_false_r.
    destruct (sl_nn s); cbn [app in_ivs existsb fst snd]; [|reflexivity]. rewrite Un.
    rewrite (proj2 (Z.leb_le _ _)) by (subst lo; lia). rewrite (proj2 (Z.ltb_lt _ _)) by (subst hi; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma sl_lazy_out : forall x : word, bv_unsigned x < lo \/ hi <= bv_unsigned x ->
    page_in_ranges (page_base x) (m_vm_lazy model') = page_in_ranges (page_base x) (m_vm_lazy model).
  Proof.
    intros x Hx. pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as (W1 & W2 & W3 & _). pose proof sl_lohi as (L1 & L2 & L3 & L4 & L5 & L6).
    pose proof (page_of_byte_out_aligned x lo hi L5 L6 Hx) as P. subst lo hi.
    rewrite (sp_lazy _ _ _ _ _ SPo). destruct s; try reflexivity.
    - apply page_in_ranges_subtract_out; [exact W3 | rewrite Un; lia | unfold page_size; rewrite Un; lia].
    - rewrite page_in_ranges_cons_out; [| unfold page_size; rewrite Un; lia | rewrite Un; lia].
      apply page_in_ranges_subtract_out; [exact W3 | rewrite Un; lia | unfold page_size; rewrite Un; lia].
    - apply page_in_ranges_subtract_out; [exact W3 | rewrite Un; lia | unfold page_size; rewrite Un; lia].
  Qed.

  Lemma sl_lazy_in : forall x : word, lo <= bv_unsigned x < hi ->
    page_in_ranges (page_base x) (m_vm_lazy model') =
      match s with SlM => page_in_ranges (page_base x) (m_vm_lazy model) | SlF => true | _ => false end.
  Proof.
    intros x Hx. pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as (W1 & W2 & W3 & _). pose proof sl_lohi as (L1 & L2 & L3 & L4 & L5 & L6).
    destruct (page_of_byte_in_aligned x lo hi L5 L6 Hx) as [P1 P2]. subst lo hi.
    rewrite (sp_lazy _ _ _ _ _ SPo). destruct s; try reflexivity.
    - apply page_in_ranges_subtract_in; [exact W3 | rewrite Un; lia].
    - apply page_in_ranges_cons_in; unfold page_size; rewrite ?Un; lia.
    - apply page_in_ranges_subtract_in; [exact W3 | rewrite Un; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma sp_atop : alloc_top (m_vmmaps model') = alloc_top (m_vmmaps model).
  Proof. unfold alloc_top. rewrite (sp_isp _ _ _ _ _ SPo). reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma sl_vis_out : forall cs1 (x : word), a_vis cs1 = a_vis cs -> (bv_unsigned x < lo \/ hi <= bv_unsigned x) ->
    VIS E cs1 model' x = VIS E cs model x.
  Proof.
    intros cs1 x Hv Hx. unfold vis. rewrite (sp_maps _ _ _ _ _ SPo), (sl_noacc_out x Hx), (sl_lazy_out x Hx), (in_allow_ext E cs cs1 Hv), sp_atop. reflexivity.
  Qed.

  Lemma sl_MR_out : forall cs1 (x : word), a_vis cs1 = a_vis cs -> (bv_unsigned x < lo \/ hi <= bv_unsigned x) ->
    MR E cs1 model' FULL' x = MR E cs model FULL x.
  Proof.
    intros cs1 x Hv Hx. unfold Mr, mrestrict, hid. rewrite (sl_vis_out cs1 x Hv Hx). rewrite (proj1 SM x) by (subst lo hi; rewrite Un; exact Hx). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma sl_vis_in_E : s = SlE -> forall cs1 (x : word), lo <= bv_unsigned x < hi -> VIS E cs1 model' x = true.
  Proof.
    intros Hs cs1 x Hx. unfold vis. rewrite (sp_maps _ _ _ _ _ SPo), (sl_in_maps x Hx), (sl_noacc_in x Hx), (sl_lazy_in x Hx). subst s.
    cbn [sl_nn negb andb orb]. rewrite !orb_true_r. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sl_vis_in_G : s = SlG -> forall cs1 (x : word), lo <= bv_unsigned x < hi -> argH E x = false -> VIS E cs1 model' x = false.
  Proof.
    intros Hs cs1 x Hx Ha. pose proof sl_lohi as (L1 & L2 & L3 & L4 & L5 & L6). unfold vis. rewrite sp_atop.
    rewrite (sp_maps _ _ _ _ _ SPo), (sl_in_maps x Hx), (sl_noacc_in x Hx). subst s. cbn [sl_nn negb andb].
    replace (in_hull A (bv_unsigned x)) with false
      by (symmetry; unfold in_hull; apply andb_false_iff; destruct L1; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
    replace (alloc_top (m_vmmaps model) <=? bv_unsigned x) with false by (symmetry; apply Z.leb_gt; lia).
    rewrite andb_false_r. reflexivity.
  Qed.

  Lemma sl_vis_in_F : s = SlF -> forall cs1 (x : word), a_vis cs1 = a_vis cs -> lo <= bv_unsigned x < hi -> VIS E cs1 model' x = VIS E cs model x.
  Proof.
    intros Hs cs1 x Hv Hx. unfold vis. rewrite sp_atop.
    rewrite (sp_maps _ _ _ _ _ SPo), (sl_in_maps x Hx), (sl_noacc_in x Hx), (sl_lazy_in x Hx), (in_allow_ext E cs cs1 Hv).
    destruct (proj1 (Forall_forall _ _) (co_kinds _ _ _ _ _ _ _ _ _ _ _ HC) m Hm (HF Hs) x ltac:(subst lo hi; lia)) as [K1 K2].
    rewrite K1, K2. subst s. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma sl_eager : eager_used model' <= eager_used model + (if sl_charge s then nZ else 0).
  Proof.
    pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as Hwf. pose proof Hwf as (W1 & W2 & W3 & _). pose proof sl_lohi as (L1 & L2 & L3 & L4 & L5 & L6).
    rewrite (eager_used_sem model' sl_wf'), (eager_used_sem model Hwf). rewrite (sp_maps _ _ _ _ _ SPo).
    set (C := vm_noaccess (m_vmmaps model) ++ m_vm_lazy model).
    set (C' := vm_noaccess (m_vmmaps model') ++ m_vm_lazy model').
    assert (CEQ : forall x, covered C' x =
              ((sl_nn s && in_rng lo hi x)
               || (covered (vm_noaccess (m_vmmaps model)) x && negb (in_rng lo hi x))
               || match s with
                  | SlM => covered (m_vm_lazy model) x
                  | SlF => in_rng lo hi x || (covered (m_vm_lazy model) x && negb (in_rng lo hi x))
                  | _ => covered (m_vm_lazy model) x && negb (in_rng lo hi x)
                  end)%bool).
    { intros x. subst C'. rewrite (sp_noacc _ _ _ _ _ SPo), (sp_lazy _ _ _ _ _ SPo). rewrite !covered_app.
      rewrite covered_maps_subtract by (try exact W2; rewrite Un; lia). rewrite Un. fold hi. fold lo.
      assert (HD : covered (if sl_nn s then [(addr, n)] else []) x = (sl_nn s && in_rng lo hi x)%bool).
      { destruct (sl_nn s); cbn [covered existsb]; [|reflexivity]. unfold in_iv, B, S. cbn [fst snd]. rewrite Un. fold lo hi. apply orb_false_r. }
      rewrite HD. f_equal.
      assert (SC : lo <= hi) by (unfold lo, hi; lia).
      destruct s; cbn [sl_nn]; rewrite ?covered_maps_subtract by first [exact W3 | exact SC]; try reflexivity.
      unfold covered at 1. cbn [existsb]. fold (covered (maps_subtract (m_vm_lazy model) lo hi) x).
      rewrite covered_maps_subtract by first [exact W3 | exact SC]. unfold in_iv, B, S. cbn [fst snd]. rewrite Un. reflexivity. }
    assert (CC : forall x, covered C x = (covered (vm_noaccess (m_vmmaps model)) x || covered (m_vm_lazy model) x)%bool).
    { intros x. subst C. apply covered_app. }
    assert (MONO : sum_count (fun x => negb (covered C' x)) (vm_maps (m_vmmaps model))
                   <= sum_count (fun x => (negb (covered C x) || (in_rng lo hi x && sl_charge s))%bool) (vm_maps (m_vmmaps model))).
    { apply sum_count_mono. intros x Hx. apply negb_true_iff in Hx. rewrite CEQ in Hx. rewrite CC.
      destruct s; cbn [sl_nn sl_charge] in Hx |- *;
        destruct (in_rng lo hi x), (covered (vm_noaccess (m_vmmaps model)) x), (covered (m_vm_lazy model) x); cbn in Hx |- *; congruence. }
    pose proof (sum_count_or_le (fun x => negb (covered C x)) (fun x => (in_rng lo hi x && sl_charge s)%bool) (vm_maps (m_vmmaps model))) as OR.
    assert (CH : sum_count (fun x => (in_rng lo hi x && sl_charge s)%bool) (vm_maps (m_vmmaps model)) <= (if sl_charge s then nZ else 0)).
    { destruct (sl_charge s).
      - rewrite (sum_count_ext _ (in_rng lo hi)) by (intros; apply andb_true_r).
        pose proof (overlap_sum_contained (vm_maps (m_vmmaps model)) (edenot E (am_base m)) (edenot E (am_len m)) lo hi
                      (co_seps _ _ _ _ _ _ _ _ _ _ _ HC) (maps_match_In E _ _ m (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) Hm Hnf)
                      ltac:(unfold lo; lia) ltac:(unfold hi; lia) ltac:(unfold lo, hi; lia)) as OV.
        unfold overlap_sum in OV. unfold lo, hi in *. lia.
      - rewrite (sum_count_ext _ (fun _ => false)) by (intros; apply andb_false_r).
        clear. induction (vm_maps (m_vmmaps model)) as [|q l IH]; cbn; [lia|]. unfold iv_count. rewrite zcount_const_false. lia. }
    cbv beta in OR. lia.
  Qed.

  Lemma page_base_aligned : forall p : word, bv_unsigned p mod 4096 = 0 -> page_base p = p.
  Proof.
    intros p Hp. unfold page_base, page_base_of, page_size. apply bv_eq. pose proof (u64_range p).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    rewrite u64_lit; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.

  (* [comment removed for export] *)
  Lemma slice_cs1_ok : forall sr' R' k' p nx nhi,
    regs_ok E sr' R' ->
    know_ok SEGS E (MR E cs model' FULL') k' ->
    nZ <= nhi ->
    (sl_charge s = true -> a_eager cs + a_abytes cs + nhi <= LIMIT) ->
    (plain A = true -> match s with SlF => False | _ => True end) ->     (* [comment removed for export] *)
    CSOK E (ACS (mk_ss p sr' k' nx)
                (match s with SlF => a_maps cs | _ => rekind (a_maps cs) m end)
                (a_totsz cs) (a_ylo cs)
                (if sl_charge s then a_eager cs + nhi else a_eager cs)
                (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs)) R' FULL' model'.
  Proof.
    intros sr' R' k' p nx nhi Hregs Hknow Hnhi Hbudget Hplain.
    assert (Es : exists s0, s0 = s) by (exists s; reflexivity). destruct Es as [s0 Es].
    pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as Hwf. pose proof Hwf as (W1 & W2 & W3 & _).
    pose proof sl_lohi as (L1 & L2 & L3 & L4 & L5 & L6). pose proof sl_bounds as (B1 & B2 & B3 & B4 & B5).
    pose proof sl_wf' as Hwf'. pose proof sl_eager as EG.
    pose proof (co_seps _ _ _ _ _ _ _ _ _ _ _ HC) as SEPS. pose proof (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) as MM.
    assert (DISJ := fun m' Hm' Hnf' Hne => maps_match_disjoint E (a_maps cs) _ m m' MM SEPS Hm Hm' Hnf Hnf' Hne).
    assert (DISJ' : forall m', In m' (a_maps cs) -> is_fog m' = false -> m <> m' ->
              bv_unsigned (edenot E (am_base m')) + bv_unsigned (edenot E (am_len m')) <= lo
              \/ hi <= bv_unsigned (edenot E (am_base m'))).
    { intros m' Hm' Hnf' Hne. pose proof (DISJ m' Hm' Hnf' Hne) as D. unfold iv_disjoint, amap_den in D. cbn [fst snd] in D. unfold lo, hi. lia. }
    assert (KNF : forall m', am_kind m' = KNONE \/ am_kind m' = KNONELAZY \/ am_kind m' = KRWLAZY -> is_fog m' = false).
    { intros m' Hk. unfold is_fog. destruct Hk as [-> |[-> | ->]]; reflexivity. }
    (* [comment removed for export] *)
    assert (NONE : forall m', In m' (a_maps cs) -> m <> m' -> (am_kind m' = KNONE \/ am_kind m' = KNONELAZY) ->
              In (amap_den E m') (vm_noaccess (m_vmmaps model'))).
    { intros m' Hm' Hne Hk. rewrite (sp_noacc _ _ _ _ _ SPo). apply in_app_iff. right.
      assert (Hnf' : is_fog m' = false) by (apply KNF; tauto).
      pose proof (proj1 (Forall_forall _ _) (co_none _ _ _ _ _ _ _ _ _ _ _ HC) m' Hm' Hk) as X.
      pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) (amap_den E m')
                    (maps_match_In E _ _ m' MM Hm' Hnf')) as (Bm1 & _).
      unfold amap_den in *. apply maps_subtract_keeps; [rewrite Un; lia | exact Bm1 | exact X |].
      cbn [fst snd]. rewrite Un. pose proof (DISJ' m' Hm' Hnf' Hne). unfold lo, hi in *. lia. }
    (* [comment removed for export] *)
    assert (KINDS : forall m', In m' (a_maps cs) -> am_kind m' = KRWLAZY ->
              forall x : word, bv_unsigned (edenot E (am_base m')) <= bv_unsigned x < bv_unsigned (edenot E (am_base m')) + bv_unsigned (edenot E (am_len m')) ->
                in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model')) = false
                /\ page_in_ranges (page_base x) (m_vm_lazy model') = true).
    { intros m' Hm' Hk x Hx.
      destruct (proj1 (Forall_forall _ _) (co_kinds _ _ _ _ _ _ _ _ _ _ _ HC) m' Hm' Hk x Hx) as [K1 K2].
      destruct (Z_lt_le_dec (bv_unsigned x) lo) as [Hlt|Hge]; [|destruct (Z_lt_le_dec (bv_unsigned x) hi) as [Hlt2|Hge2]].
      - rewrite sl_noacc_out, sl_lazy_out by lia. auto.
      - (* [comment removed for export] *)
        assert (Hmm : m = m').
        { destruct (amap_eqb m m') eqn:He; [apply APS.amap_eqb_eq in He; exact He|]. exfalso.
          assert (Hne : m <> m') by (intros ->; rewrite amap_eqb_refl in He; discriminate).
          pose proof (DISJ' m' Hm' ltac:(apply KNF; tauto) Hne). lia. }
        subst m'. rewrite sl_noacc_in, sl_lazy_in by lia.
        destruct s0; rewrite <- Es; cbn [sl_nn]; auto; exfalso; refine (HnF _ Hk); rewrite <- Es; discriminate.
      - rewrite sl_noacc_out, sl_lazy_out by lia. auto. }
    match goal with |- CSOK _ ?c _ _ _ => set (cs1 := c) end.
    assert (HIDOUT : forall x : word, bv_unsigned x < lo \/ hi <= bv_unsigned x -> HID E cs1 model' x = HID E cs model x).
    { intros x Hx. unfold hid. rewrite (sl_vis_out cs1 x eq_refl Hx). reflexivity. }
    assert (HALLOW : ALLOW E cs1 = ALLOW E cs) by reflexivity.
    destruct HC as [Xregs Xlog Xknow Xhalt Xfds Xfs Xtid Xres Xlimit Xmaps Xholes Xseps Xwf Xbounds Xlazyb Xnasub Xnone Xkinds Xtotsz Xisp Xbrk Xsbrk Xeager Xabytes Xminv Xzero Xsinv Xplain].
    constructor; rewrite ?HALLOW; unfold cs1; cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn s_regs s_log s_know s_next mk_ss]; fold cs1.
    - exact Hregs.
    - reflexivity.
    - unfold Mr. rewrite (hid_ext A argH E cs _ model') by reflexivity. exact Hknow.
    - rewrite (sp_halted _ _ _ _ _ SPo). exact Xhalt.
    - unfold fds_ok in *. rewrite (sp_fds _ _ _ _ _ SPo), (sp_fs _ _ _ _ _ SPo). exact Xfds.
    - rewrite (sp_fs _ _ _ _ _ SPo). exact Xfs.
    - rewrite (sp_tid _ _ _ _ _ SPo). exact Xtid.
    - rewrite (sp_res _ _ _ _ _ SPo). exact Xres.
    - rewrite (sp_limit _ _ _ _ _ SPo). exact Xlimit.
    - rewrite (sp_maps _ _ _ _ _ SPo).
      assert (RK : maps_match E (rekind (a_maps cs) m) (vm_maps (m_vmmaps model))).
      { unfold rekind. apply maps_match_rekind; [|exact Xmaps]. intros m0. destruct (amap_eqb m0 m) eqn:He; [|auto].
        apply APS.amap_eqb_eq in He. subst m0. cbn [am_base am_len]. split; [reflexivity|]. split; [reflexivity|]. rewrite Hnf. reflexivity. }
      destruct s0; rewrite <- Es; first [exact RK | exact Xmaps].
    - (* [comment removed for export] *)
      rewrite (sp_maps _ _ _ _ _ SPo), (sp_res _ _ _ _ _ SPo).
      assert (RKH : Forall (hole_ok E (a_ylo cs) (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))) (rekind (a_maps cs) m)).
      { unfold rekind. apply Forall_forall. intros m0 HinR Hh. apply in_map_iff in HinR as (m1 & <- & HinR1).
        destruct (amap_eqb m1 m) eqn:He.
        - exfalso. unfold is_hole in Hh. cbn [am_kind] in Hh. discriminate.
        - exact (proj1 (Forall_forall _ _) Xholes m1 HinR1 Hh). }
      destruct s0; rewrite <- Es; first [exact RKH | exact Xholes].
    - rewrite (sp_maps _ _ _ _ _ SPo). exact Xseps.
    - exact Hwf'.
    - unfold alloc_top in *. rewrite (sp_maps _ _ _ _ _ SPo), (sp_isp _ _ _ _ _ SPo). exact Xbounds.
    - (* [comment removed for export] *)
      pose proof sl_lohi as (A1 & A2 & _).
      rewrite (sp_lazy _ _ _ _ _ SPo). unfold alloc_top in *. rewrite (sp_isp _ _ _ _ _ SPo).
      assert (SUB : Forall (fun iv : word * word => (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_lo A \/ img_hi A <= bv_unsigned (fst iv))
                                               /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= bv_unsigned (vm_init_sp (m_vmmaps model)) - stack_max_size)
                      (maps_subtract (m_vm_lazy model) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))).
      { apply Forall_forall. intros q Hq. destruct (maps_subtract_pieces _ _ _ q W3 Hq) as (r & Hr & R1 & R2 & _).
        pose proof (proj1 (Forall_forall _ _) Xlazyb r Hr) as [Y1 Y2]. split; [destruct Y1; [left|right]; lia | lia]. }
      destruct s0; rewrite <- Es; try exact SUB; try exact Xlazyb.
      apply Forall_cons; [cbn [fst snd]; unfold lo, hi in *; split; lia | exact SUB].
    - (* [comment removed for export] *) intros z Hz. rewrite (sp_maps _ _ _ _ _ SPo). rewrite (sp_noacc _ _ _ _ _ SPo), in_ivs_app in Hz.
      apply orb_prop in Hz as [Hz|Hz].
      + destruct (sl_nn s); [|discriminate]. rewrite in_ivs_cons in Hz. cbn [fst snd in_ivs existsb] in Hz. rewrite orb_false_r in Hz.
        apply andb_prop in Hz as [Z1 Z2]. apply Z.leb_le in Z1. apply Z.ltb_lt in Z2.
        eapply in_ivs_maps_match; [exact Xmaps | exact Hm | exact Hnf |]. unfold lo, hi in *. lia.
      + apply Xnasub. rewrite in_ivs_covered in Hz |- *. rewrite covered_maps_subtract in Hz by (try exact W2; rewrite Un; lia).
        apply andb_prop in Hz as [Hz _]. exact Hz.
    - (* [comment removed for export] *) apply Forall_forall. intros m' Hm' Hk'. destruct s0; rewrite <- Es in Hm'.
      2: { apply NONE; [exact Hm' | | exact Hk']. intros <-. rewrite (HF (eq_sym Es)) in Hk'. destruct Hk'; discriminate. }
      all: destruct (in_rekind _ _ _ Hm') as (m0 & Hm0 & [[-> ->]|[Hne ->]]); [cbn in Hk'; destruct Hk'; discriminate|];
           apply NONE; [exact Hm0 | congruence | exact Hk'].
    - (* [comment removed for export] *) apply Forall_forall. intros m' Hm' Hk'. destruct s0; rewrite <- Es in Hm'.
      2: { apply KINDS; assumption. }
      all: destruct (in_rekind _ _ _ Hm') as (m0 & Hm0 & [[-> ->]|[Hne ->]]); [cbn in Hk'; discriminate|];
           apply KINDS; assumption.
    - rewrite (sp_res _ _ _ _ _ SPo), (sp_maps _ _ _ _ _ SPo). exact Xtotsz.
    - (* [comment removed for export] *) rewrite (sp_isp _ _ _ _ _ SPo). exact Xisp.
    - rewrite (sp_brk _ _ _ _ _ SPo). exact Xbrk.
    - rewrite (sp_brk _ _ _ _ _ SPo), (sp_sbrk _ _ _ _ _ SPo). exact Xsbrk.
    - (* [comment removed for export] *) destruct (sl_charge s); lia.
    - exact Xabytes.
    - (* [comment removed for export] *) destruct Xminv as [N1 N2 N3 N4 N5].
      assert (MAT : forall q, In q (m_vm_materialized model') -> In q (m_vm_materialized model)
                      /\ (s <> SlM -> bv_unsigned q < lo \/ hi <= bv_unsigned q)).
      { intros q Hq. pose proof (sp_mat _ _ _ _ _ SPo) as SMAT. destruct s0; rewrite <- Es in SMAT; rewrite SMAT in Hq; try (split; [exact Hq | congruence]).
        all: apply filter_In in Hq as [Hq Ho]; split; [exact Hq|]; intros _;
             unfold page_outside_range in Ho; apply negb_true_iff in Ho; apply andb_false_iff in Ho as [Ho|Ho];
             [apply Z.leb_gt in Ho | apply Z.ltb_ge in Ho]; unfold lo, hi; rewrite <- ?Un; lia. }
      constructor; rewrite ?(sp_limit _ _ _ _ _ SPo).
      + pose proof (sp_mat _ _ _ _ _ SPo) as SMAT. destruct s0; rewrite <- Es in SMAT; rewrite SMAT; try apply NoDup_filter; exact N1.
      + intros q Hq. apply N2. apply MAT. exact Hq.
      + intros q Hq. apply N3. apply MAT. exact Hq.
      + intros q Hq. destruct (MAT q Hq) as [Hq0 Hout]. pose proof (N4 q Hq0) as L0.
        pose proof (sl_lazy_out q) as LO. pose proof (sp_lazy _ _ _ _ _ SPo) as SL.
        destruct s0; rewrite <- Es in SL, Hout; [| | | rewrite SL; exact L0].
        all: specialize (Hout ltac:(discriminate)); rewrite <- (page_base_aligned q (N2 q Hq0)); rewrite LO by exact Hout;
             rewrite page_base_aligned by exact (N2 q Hq0); exact L0.
      + destruct (sl_charge s); [specialize (Hbudget eq_refl)|]; rewrite Xlimit in *; lia.
    - (* [comment removed for export] *) intros x Hh Hmx Hna Hlz Hgh.
      destruct (Z_lt_le_dec (bv_unsigned x) lo) as [Hlt|Hge]; [|destruct (Z_lt_le_dec (bv_unsigned x) hi) as [Hlt2|Hge2]].
      + rewrite (proj1 SM x) by (unfold lo in *; lia). rewrite HIDOUT in Hh by lia. rewrite (sp_maps _ _ _ _ _ SPo) in Hmx.
        rewrite sl_noacc_out in Hna by lia. rewrite sl_lazy_out in Hlz by lia. exact (Xzero x Hh Hmx Hna Hlz Hgh).
      + rewrite sl_noacc_in in Hna by lia. rewrite (proj2 SM x) by (unfold lo, hi in *; rewrite Un; lia). rewrite Hna. reflexivity.
      + rewrite (proj1 SM x) by (unfold hi in *; rewrite Un; lia). rewrite HIDOUT in Hh by lia. rewrite (sp_maps _ _ _ _ _ SPo) in Hmx.
        rewrite sl_noacc_out in Hna by lia. rewrite sl_lazy_out in Hlz by lia. exact (Xzero x Hh Hmx Hna Hlz Hgh).
    - (* [comment removed for export] *)
      eapply SINV_frame; [|exact Xsinv]. intros x Hx. apply (proj1 SM). pose proof (argH_sp _ _ _ Xsinv Hx) as AS.
      pose proof sl_lohi as (_ & LT2 & _). unfold alloc_top, stack_max_size in LT2. rewrite Xisp in LT2. unfold APS.uE in AS. unfold hi in *. rewrite Un. lia.
    - (* [comment removed for export] *) intros HP. specialize (Hplain HP). rewrite (sp_lazy _ _ _ _ _ SPo), (Xplain HP). destruct s; cbn; first [reflexivity | destruct Hplain].
  Qed.

End Slice.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma kn_unfill_clip_ok : forall E M M' k b off ne,
  know_ok SEGS E M k ->
  img_hi A <= estart E (SA b off) ->
  (forall x : word, bv_unsigned x < estart E (SA b off) \/ estart E (SA b off) + elenZ E ne <= bv_unsigned x -> M' x = M x) ->
  know_ok SEGS E M' (kimg_clip A (kn_unfill k b off ne)).
Proof.
  intros E M M' k b off ne HK Hhull Hout.
  pose proof (kimg_clip_in_hull' (kn_unfill k b off ne)) as Hh.
  unfold know_ok. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) Hh K Hin) as HKh.
  apply kimg_clip_incl in Hin. unfold kn_unfill in Hin. apply filter_In in Hin as [Hin Hkeep].
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  eapply kentry_keep_sem'; [exact HKK | | exact Hout].
  apply orb_prop in Hkeep as [Himg|Hap].
  - destruct K; try discriminate. unfold kfoot_apart, kfoot. cbn in HKh. lia.
  - rewrite APS.kentry_apart_bp_eq in Hap. eapply kentry_apart_b_sem'; [exact HK | exact Hap].
Qed.

(* [comment removed for export] *)
Lemma kn_rezero_ok_gen : forall E M M' k b off ne,
  know_ok SEGS E M k ->
  (estart E (SA b off) + elenZ E ne <= img_lo A \/ img_hi A <= estart E (SA b off)) ->   (* [comment removed for export] *)
  (forall x : word, bv_unsigned x < estart E (SA b off) \/ estart E (SA b off) + elenZ E ne <= bv_unsigned x -> M' x = M x) ->
  (forall x : word, estart E (SA b off) <= bv_unsigned x < estart E (SA b off) + elenZ E ne -> M x <> None -> M' x = Some (Z_to_bv 8 0)) ->
  forall K, In K (kn_rezero k b off ne) ->
    match K with KImg lo hi => img_lo A <= lo /\ hi <= img_hi A | _ => True end ->
    kentry_ok SEGS E M' K.
Proof.
  intros E M M' k b off ne HK Hhull Hout Hin0 K Hin HKh.
  assert (DEF : forall x : word, M x <> None -> M' x <> None).
  { intros x Hx. destruct (Z_lt_le_dec (bv_unsigned x) (estart E (SA b off))); [rewrite Hout by lia; exact Hx|].
    destruct (Z_lt_le_dec (bv_unsigned x) (estart E (SA b off) + elenZ E ne)); [rewrite (Hin0 x ltac:(lia) Hx); discriminate | rewrite Hout by lia; exact Hx]. }
  assert (ZERO : forall x : word, M x = Some (Z_to_bv 8 0) -> M' x = Some (Z_to_bv 8 0)).
  { intros x Hx. destruct (Z_lt_le_dec (bv_unsigned x) (estart E (SA b off))); [rewrite Hout by lia; exact Hx|].
    destruct (Z_lt_le_dec (bv_unsigned x) (estart E (SA b off) + elenZ E ne)); [apply Hin0; [lia | rewrite Hx; discriminate] | rewrite Hout by lia; exact Hx]. }
  unfold kn_rezero in Hin. apply filter_In in Hin as [Hin Hkeep].
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  destruct K as [[kb kk] w v|[kb kk] l|[kb kk] l bk|ilo ihi|e mm|e rlo rhi|[kb kk] l|a1 n1 a2 n2|[kb kk] l fc|[kb kk] l];
    try (rewrite APS.kentry_apart_bp_eq in Hkeep; eapply kentry_keep_sem'; [exact HKK | eapply kentry_apart_b_sem'; [exact HK | exact Hkeep] | exact Hout]).
  - (* [comment removed for export] *) cbn [kentry_ok] in HKK |- *. destruct HKK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. apply ZERO. apply Hz. exact Hi.
  - (* [comment removed for export] *) eapply kentry_keep_sem'; [exact HKK | | exact Hout]. unfold kfoot_apart, kfoot. lia.
  - exact HKK.
  - exact HKK.
  - (* [comment removed for export] *) cbn [kentry_ok] in HKK |- *. destruct HKK as [Hfl Hs]. split; [exact Hfl|]. intros d mm Hd Hdm. eapply store_ok_mono; [exact DEF | apply Hs; assumption].
  - exact HKK.
  - (* [comment removed for export] *) cbn [kentry_ok] in HKK |- *. destruct HKK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. apply DEF. apply Hz. exact Hi.
Qed.

Lemma kn_rezero_clip_ok : forall E M M' k b off ne,
  know_ok SEGS E M k ->
  (estart E (SA b off) + elenZ E ne <= img_lo A \/ img_hi A <= estart E (SA b off)) ->   (* [comment removed for export] *)
  (forall x : word, bv_unsigned x < estart E (SA b off) \/ estart E (SA b off) + elenZ E ne <= bv_unsigned x -> M' x = M x) ->
  (forall x : word, estart E (SA b off) <= bv_unsigned x < estart E (SA b off) + elenZ E ne -> M x <> None -> M' x = Some (Z_to_bv 8 0)) ->
  know_ok SEGS E M' (kimg_clip A (kn_rezero k b off ne)).
Proof.
  intros E M M' k b off ne HK Hhull Hout Hin0. pose proof (kimg_clip_in_hull' (kn_rezero k b off ne)) as Hh.
  unfold know_ok. apply Forall_forall. intros K Hin. pose proof (proj1 (Forall_forall _ _) Hh K Hin) as HKh.
  apply kimg_clip_incl in Hin. apply (kn_rezero_ok_gen E M M' k b off ne HK Hhull Hout Hin0 K Hin). destruct K; try exact I. exact HKh.
Qed.

Lemma kn_rezero_hull_ok : forall E M M' k b off ne,
  know_ok SEGS E M k -> kimg_in_hull A k ->
  (estart E (SA b off) + elenZ E ne <= img_lo A \/ img_hi A <= estart E (SA b off)) ->   (* [comment removed for export] *)
  (forall x : word, bv_unsigned x < estart E (SA b off) \/ estart E (SA b off) + elenZ E ne <= bv_unsigned x -> M' x = M x) ->
  (forall x : word, estart E (SA b off) <= bv_unsigned x < estart E (SA b off) + elenZ E ne -> M x <> None -> M' x = Some (Z_to_bv 8 0)) ->
  know_ok SEGS E M' (kn_rezero k b off ne).
Proof.
  intros E M M' k b off ne HK Hh Hhull Hout Hin0.
  unfold know_ok. apply Forall_forall. intros K Hin.
  assert (Hin' : In K k) by (unfold kn_rezero in Hin; apply filter_In in Hin as [Hin _]; exact Hin).
  pose proof (proj1 (Forall_forall _ _) Hh K Hin') as HKh.
  apply (kn_rezero_ok_gen E M M' k b off ne HK Hhull Hout Hin0 K Hin). destruct K; try exact I. exact HKh.
Qed.

Lemma kimg_in_hull_cons2 : forall K1 K2 k,
  match K1 with KImg _ _ => False | _ => True end -> match K2 with KImg _ _ => False | _ => True end ->
  kimg_in_hull A k -> kimg_in_hull A (K1 :: K2 :: k).
Proof.
  intros K1 K2 k H1 H2 Hk. unfold kimg_in_hull in *. constructor; [destruct K1; tauto|]. constructor; [destruct K2; tauto | exact Hk].
Qed.

(* [comment removed for export] *)
Lemma vis_add_slice_ok : forall E cs1 cs2 (ea : expr) b off ne R FULL' model' (lo nZ : Z),
  CSOK E cs1 R FULL' model' ->
  vis_add A LIMIT cs1 ea ne (KWr (SA b off) ne :: KZero (SA b off) ne :: kn cs1) = Some cs2 ->
  kimg_in_hull A (kn cs1) ->
  uE E ea = lo -> estart E (SA b off) = lo -> elenZ E ne = nZ -> 0 <= lo -> 0 < nZ -> lo + nZ <= ATOP_MAX ->   (* [comment removed for export] *)
  (forall x : word, lo <= bv_unsigned x < lo + nZ ->
     in_ivs (bv_unsigned x) (vm_maps (m_vmmaps model')) = true
     /\ in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model')) = false
     /\ argH E x = false /\ FULL' x = Some (Z_to_bv 8 0)) ->
  CSOK E cs2 R FULL' model'.
Proof.
  intros E cs1 cs2 ea b off ne R FULL' model' lo nZ HC1 Hva Hkh Hea Hest Hne Hlo HnZ Hhi NEW.
  eapply vis_add_sound'; [exact Hva | exact HC1 |].
  destruct (vis_add_inv cs1 ea ne _ cs2 Hva) as (nhi & Hnhi & Ecs2).
  assert (BYTE : forall x : word, lo <= bv_unsigned x < lo + nZ -> MR E cs2 model' FULL' x = Some (Z_to_bv 8 0)).
  { intros x Hx. destruct (NEW x Hx) as (N1 & N2 & N3 & N4).
    unfold Mr, mrestrict, hid. rewrite N3. cbn [orb]. unfold vis. rewrite N1, N2. cbn [negb andb].
    assert (Hal : in_allow A E cs2 (bv_unsigned x) = true).
    { unfold in_allow, in_vis. rewrite Ecs2. cbn [a_vis existsb fst snd]. rewrite Hea. unfold uE. fold (elenZ E ne). rewrite Hne.
      rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
    rewrite Hal, !orb_true_r. cbn [negb]. exact N4. }
  assert (Hfl : flat E (SA b off) (elenZ E ne)) by (unfold flat; rewrite Hest, Hne; unfold ATOP_MAX in Hhi; lia).
  constructor; [|constructor].
  - cbn [kentry_ok]. split; [exact Hfl|]. rewrite Hest, Hne. intros d w' Hd Hdw. destruct w' as [|w'']; [reflexivity|].
    apply store_ok_of_all; [rewrite u64_lit by (unfold ATOP_MAX in Hhi; lia); unfold ATOP_MAX in Hhi; lia|].
    intros x Hx. rewrite u64_lit in Hx by (unfold ATOP_MAX in Hhi; lia). unfold wview. rewrite (BYTE x) by lia. discriminate.
  - cbn [kentry_ok]. split; [exact Hfl|]. rewrite Hest, Hne. intros i Hi. apply BYTE. rewrite u64_lit by (unfold ATOP_MAX in Hhi; lia). lia.
  - pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC1) as HK1. unfold Mr in HK1 |- *.
    eapply know_ok_unhide'; [apply H_off_segments_cs' | exact Hkh | | | exact HK1].
    + intros y Hy. rewrite Ecs2 in Hy. eapply hid_cons_sub. exact Hy.
    + intros y Hy. apply hid_hull'. exact Hy.
Qed.

(* [comment removed for export] *)
Lemma find_containing_sound : forall E M k ms kinds b off ne m,
  know_ok SEGS E M k -> find_containing k ms kinds b off ne = Some m ->
  In m ms /\ (In (am_kind m) kinds /\ is_fog m = false)
  /\ bv_unsigned (edenot E (am_base m)) <= estart E (SA b off)
  /\ estart E (SA b off) + elenZ E ne <= bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)).
Proof.
  intros E M k ms kinds b off ne m HK Hf. unfold find_containing in Hf. apply find_some in Hf as [Hin Hb].
  apply andb_prop in Hb as [Hk Hins]. apply andb_prop in Hk as [Hnf Hk]. apply negb_true_iff in Hnf.
  apply existsb_exists in Hk as (k0 & Hk0 & Hkk). apply APS.mkind_eqb_eq in Hkk. subst k0.
  pose proof (xinside_sound SEGS E M k b off ne (am_base m) 0 (am_len m) HK Hins) as [I1 I2].
  unfold estart in I1, I2 |- *. cbn [a_base a_off] in *. unfold elenZ in *. repeat split; try assumption; lia.
Qed.

(* [comment removed for export] *)
Lemma slice_args : forall E cs R FULL model b off ne nlo nhi kinds m,
  CSOK E cs R FULL model ->
  fixed_args_in cs = Some (b, off, ne, nlo, nhi) ->      (* [comment removed for export] *)
  find_containing (kn cs) (a_maps cs) kinds b off ne = Some m ->
  let addr := edenot E (reg cs 10) in
  let len := bv_unsigned (edenot E (reg cs 11)) in
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  In m (a_maps cs) /\ (In (am_kind m) kinds /\ is_fog m = false)
  /\ getr R (Z_to_bv 5 (Z.of_nat 10)) = addr /\ getr R (Z_to_bv 5 (Z.of_nat 11)) = Z_to_bv 64 len /\ 0 < len < 2 ^ 64
  /\ edenot E ne = n /\ bv_unsigned n = nZ /\ 0 < nZ /\ nZ <= nhi /\ nZ mod 4096 = 0
  /\ bv_unsigned addr mod 4096 = 0 /\ 0 < bv_unsigned addr
  /\ (bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= img_lo A \/ img_hi A <= bv_unsigned (edenot E (am_base m)))   (* [comment removed for export] *)
  /\ estart E (SA b off) = bv_unsigned addr
  /\ bv_unsigned (edenot E (am_base m)) <= bv_unsigned addr
  /\ bv_unsigned addr + nZ <= bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m))
  /\ bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= alloc_top (m_vmmaps model)   (* [comment removed for export] *)
  /\ map_contains (vm_maps (m_vmmaps model)) addr n = true
  /\ region_free (vm_reserved (m_vmmaps model)) addr n = true
  /\ overlap_sum (vm_maps (m_vmmaps model)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) <= nZ.
Proof.
  intros E cs R FULL model b off ne nlo nhi kinds m HC HFA Hf addr len nZ n.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  destruct (fixed_args_in_sound E cs R FULL model b off ne nlo nhi HC HFA) as (Hsp & HML & Hal & Hpos & Htop & R10 & _). unfold ATOP_MAX in Htop.
  destruct (mmap_len_sound E cs R FULL model ne nlo nhi HC HML) as (R11 & Hlen & Hne & Hnlo & HnZ & HnZal & _).
  fold addr in Hal, Hpos, Htop, R10. fold len in R11, Hlen, Hne, HnZ, HnZal. fold nZ in Hne, HnZ, HnZal. fold n in Hne.
  destruct (find_containing_sound E _ (kn cs) (a_maps cs) kinds b off ne m HK Hf) as (Hm & [Hkind Hnf] & I1 & I2).
  pose proof (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) as HB.
  pose proof (maps_match_In E _ _ m (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) Hm Hnf) as HIN.
  pose proof (proj1 (Forall_forall _ _) HB (amap_den E m) HIN) as (B1 & B2 & B3 & B5 & B4). cbn [amap_den fst snd] in B1, B2, B3, B4, B5.
  pose proof (u64_range (edenot E (am_base m))) as Rb.
  assert (T : alloc_top (m_vmmaps model) <= 0x7FFFFF800000).
  { pose proof (SINV_sp _ _ (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC)) as [_ Shi]. pose proof (co_isp _ _ _ _ _ _ _ _ _ _ _ HC) as I.
    unfold alloc_top, stack_max_size. rewrite I. unfold APS.uE, sp_window_hi in Shi. lia. }
  assert (Hest : bv_unsigned addr = estart E (SA b off)).
  { unfold addr. apply (APS.u_of_split E (reg cs 10) b off Hsp). unfold elenZ in I2. pose proof (u64_range (edenot E ne)). lia. }
  unfold elenZ in I2. rewrite Hne in I2.
  pose proof (page_round_up_Z_bounds len ltac:(lia)) as PB. fold nZ in PB. unfold page_size in PB.
  assert (Un : bv_unsigned n = nZ).
  { unfold n. apply u64_lit. pose proof (u64_range (Z_to_bv 64 nZ)). fold n in H. unfold CEIL in *. lia. }
  rewrite Un in I2.
  assert (Hmc : map_contains (vm_maps (m_vmmaps model)) addr n = true).
  { eapply map_contains_intro; [exact HIN | lia | rewrite Un; lia]. }
  split; [exact Hm|]. split; [split; [exact Hkind | exact Hnf]|].
  repeat (split; [first [assumption | lia | symmetry; assumption] |]).
  split; [apply reserved_free_of_hull; [exact (co_res _ _ _ _ _ _ _ _ _ _ _ HC) | rewrite Un; lia] |].
  rewrite Un. pose proof (overlap_sum_contained (vm_maps (m_vmmaps model)) (edenot E (am_base m)) (edenot E (am_len m)) (bv_unsigned addr) (bv_unsigned addr + nZ)
    (co_seps _ _ _ _ _ _ _ _ _ _ _ HC) HIN ltac:(lia) ltac:(lia) ltac:(lia)). lia.
Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

End Nodes.
