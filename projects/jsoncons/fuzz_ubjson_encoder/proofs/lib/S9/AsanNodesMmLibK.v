(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AgentNodes Nodes AllocSim AsanAcctShape AsanPlacement.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BackingAlgebra.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import MmapSim RefNodes NoReserveK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import Scfg KitNodesS.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanCoreK AsanPlanK AsanPlanSoundK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import AsanCeil.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require PlaceLemmasK.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Import AX2K. Import AX2SK. Import APK. Import APSK.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition RES_hull_def (SEGS : list Segment) (A : APK.atable) : Prop :=
  Forall (fun iv : word * word => img_lo A <= bv_unsigned (fst iv)
                                  /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A)
         (segments_reserved SEGS).

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

Lemma map_contains_intro : forall l (lo n : word) b s,
  In (b, s) l -> bv_unsigned b <= bv_unsigned lo -> bv_unsigned lo + bv_unsigned n <= bv_unsigned b + bv_unsigned s ->
  map_contains l lo n = true.
Proof.
  intros l lo n b s Hin H1 H2. unfold map_contains. apply existsb_exists. exists (b, s). split; [exact Hin|].
  cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

Lemma map_has_intro : forall l (lo n : word), In (lo, n) l -> map_has l lo n = true.
Proof.
  intros l lo n Hin. unfold map_has. apply existsb_exists. exists (lo, n). split; [exact Hin|].
  cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity.
Qed.

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
  MInv A m -> A_wf A -> eager_used m + A_bytes A <= vm_limit (m_vmmaps m) -> vm_backing_used m <= vm_limit (m_vmmaps m).
Proof.
  intros A m HM Hwf Hb. pose proof (vm_backing_used_le A m HM Hwf). lia.
Qed.

Lemma sum_count_negb_covered_mono : forall C C' l,
  (forall x, covered C x = true -> covered C' x = true) ->
  sum_count (fun x => negb (covered C' x)) l <= sum_count (fun x => negb (covered C x)) l.
Proof.
  intros C C' l H. apply sum_count_mono. intros x Hx. apply negb_true_iff in Hx. apply negb_true_iff.
  destruct (covered C x) eqn:E; [|reflexivity]. rewrite (H x E) in Hx. discriminate.
Qed.

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

Lemma page_in_ranges_covers : forall p l z,
  page_in_ranges p l = true -> bv_unsigned p <= z < bv_unsigned p + page_size -> in_ivs z l = true.
Proof.
  intros p l z Hp Hz. apply page_in_ranges_true in Hp as (iv & Hin & H1 & H2).
  apply (proj2 (in_ivs_true' z l)). exists iv. split; [exact Hin | lia].
Qed.

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
  -
    destruct Hout as [Hout|Hout].
    + destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + Z.min (bv_unsigned sz) (lo - bv_unsigned a)));
      destruct (Z.leb_spec (Z.max (bv_unsigned a) hi) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (Z.max (bv_unsigned a) hi + (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)));
      destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
    + destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + Z.min (bv_unsigned sz) (lo - bv_unsigned a)));
      destruct (Z.leb_spec (Z.max (bv_unsigned a) hi) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (Z.max (bv_unsigned a) hi + (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)));
      destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
  -
    destruct Hout as [Hout|Hout];
    destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + Z.min (bv_unsigned sz) (lo - bv_unsigned a)));
      destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
  -
    destruct Hout as [Hout|Hout];
    destruct (Z.leb_spec (Z.max (bv_unsigned a) hi) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (Z.max (bv_unsigned a) hi + (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)));
      destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
  -
    destruct Hout as [Hout|Hout];
    destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
Qed.

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

Lemma nth_sr_vars_lt' : forall b sr r, APK.sr_vars_lt b sr = true -> (r < 32)%nat -> APK.expr_vars_lt b (nth r sr (ELit 0)) = true.
Proof.
  intros b sr. induction sr as [|x t IH]; intros r H Hr; [destruct r; reflexivity|].
  cbn [APK.sr_vars_lt] in H. apply andb_prop in H as [H1 H2]. destruct r as [|r]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.

Lemma elenZ_lit'' : forall E z, 0 <= z < 2 ^ 64 -> elenZ E (ELit z) = z.
Proof. intros E z Hz. unfold elenZ. cbn [edenot]. rewrite u64_lit by lia. reflexivity. Qed.

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

Lemma mmap_flags_core_22 : mmap_flags_core (Z_to_bv 64 34) = 34%Z.       Proof. vm_compute. reflexivity. Qed.
Lemma mmap_flags_core_32 : mmap_flags_core (Z_to_bv 64 50) = 50%Z.       Proof. vm_compute. reflexivity. Qed.
Lemma mmap_flags_core_4022 : mmap_flags_core (Z_to_bv 64 16418) = 34%Z.  Proof. vm_compute. reflexivity. Qed.
Lemma mmap_flags_core_4032 : mmap_flags_core (Z_to_bv 64 16434) = 50%Z.  Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_22 : mmap_noreserve_b (Z_to_bv 64 34) = false.   Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_32 : mmap_noreserve_b (Z_to_bv 64 50) = false.   Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_4022 : mmap_noreserve_b (Z_to_bv 64 16418) = true. Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_4032 : mmap_noreserve_b (Z_to_bv 64 16434) = true. Proof. vm_compute. reflexivity. Qed.

Lemma mmap_flags_core_104022 : mmap_flags_core (Z_to_bv 64 1064994) = 1048610%Z.  Proof. vm_compute. reflexivity. Qed.
Lemma mmap_flags_core_104032 : mmap_flags_core (Z_to_bv 64 1065010) = 1048626%Z.  Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_104022 : mmap_noreserve_b (Z_to_bv 64 1064994) = true. Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_104032 : mmap_noreserve_b (Z_to_bv 64 1065010) = true. Proof. vm_compute. reflexivity. Qed.

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

Section OurSpecNodes.
Context {fxg : PropExec.FPState}.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Hypothesis Halloc : sc_alloc scfg = false.

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

Lemma node_instr_noacc : forall ms model ms',
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' []) ->
  ShapeAlg.node_ok segs scfg (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
  intros ms model ms' Hh Hsvc Hstep.
  assert (Hacc : mi_account_step segs ms model = MachineOk (ms', model)).
  { unfold mi_account_step. rewrite Hstep. cbn [accessed_ranges access_value].
    rewrite materialize_model_accesses_nil. reflexivity. }

  apply (node_ok_of_pnode_instr segs scfg); [exact Hsvc |].
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
  srealizes segs scfg (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros regs pc mem rom model w T Hh HF HE Hc.
  eapply srz_silent1; [| exact Hc].
  apply node_instr_noacc; [exact Hh | reflexivity | eapply stepacc_ecall_epend; eassumption].
Qed.

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

Lemma srz_node1 : forall c (IB : Type) (nx : IB -> config) (B : TSet) (b0 : IB),
  ShapeAlg.node_ok segs scfg c IB (fun _ => []) nx ->
  (forall i, srealizes segs scfg (nx i) B) ->
  srealizes segs scfg c B.
Proof.
  intros c IB nx B b0 Hnode HB.
  assert (HB0 : B []) by (eapply srealizes_nonempty; apply (HB b0)).
  apply (srz_conseq segs scfg c (t_alt (fun i : IB => t_emit [] B))).
  - apply (srz_node segs scfg c IB (fun _ => []) nx (fun _ => B) b0 Hnode). exact HB.
  - intro tr. split.
    + intros [i Hi]. exact (proj1 (t_emit_nil_eq B HB0 tr) Hi).
    + intros H. exists b0. exact (proj2 (t_emit_nil_eq B HB0 tr) H).
Qed.

Lemma refusal_b_mmap_epend : forall ms x8 model r, bv_unsigned x8 = 222%Z ->
  refusal_b (sys_input segs ms x8) model r = errno_ret_in mmap_errnos r.
Proof. intros ms x8 model r Hno. unfold refusal_b. cbn [in_sysno sys_input]. rewrite Hno. reflexivity. Qed.

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
  destruct (errno_ret_in mmap_errnos r); [reflexivity|].
  unfold grant_ok_na_pin, mmap_model.
  destruct (mmap_noreserve_backed_ok flags model nZ); rewrite ?andb_true_r, ?andb_false_r; [reflexivity|].
  cbn [andb]. reflexivity.
Qed.

Lemma srz_mmap_rw1 : forall regs (pc : word) mem rom model w (len : Z) (flags : word) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = flags -> mmap_flags_core flags = 34%Z ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  (exists a, grant_ok_na_pin model a nZ = true) ->
  mmap_noreserve_backed_ok flags model nZ = true ->
  (forall a, grant_ok_na_pin model a nZ = true ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (zfill a n mem) rom)
                          (with_mmap_backing flags a n (mmap_model a n model))) KB) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w len flags KB HF HE Hh H17 H11 Hlen H12 H13 Hcore H14 H15 nZ n (a0 & Ha0) Hb0 HB.
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
  pose (IB := {a : word | grant_ok_na_pin model a nZ = true}).
  pose (effs := fun i : IB => match i with exist _ a _ => mkEffectU a [] [(a, n)] [] [] [] end).
  pose (ms' := fun i : IB => match i with exist _ a _ => with_mmap_backing flags a n (mmap_model a n model) end).
  assert (HokS : forall a, grant_ok_na_pin model a nZ = true ->
            check_syscall (sys_input segs ms (getr regs 17)) (mkEffectU a [] [(a, n)] [] [] []) model
            = CheckOk (with_mmap_backing flags a n (mmap_model a n model)) []).
  { intros a Ha. rewrite Hchk. rewrite (grant_na_pin_not_errno model a nZ Hn0 Ha), Ha. cbn [andb].
    rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity. }
  eapply (srz_node1 (mkCfg ms model) IB (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) KB (exist _ a0 Ha0)).
  - apply (node_chk_ev_gen_noacc segs scfg ms model (getr regs 17) IB effs ms' (fun _ => []) materialize_model_accesses_nil Hh eq_refl).
    + intros [a Ha]; cbn [effs ms']. exact (HokS a Ha).
    + intros [a Ha]; cbn [effs ms']. apply alloc_nonrefusal_step. cbn [eff_ret]. rewrite (refusal_b_mmap_epend _ _ _ _ Hno).
      exact (grant_na_pin_not_errno model a nZ Hn0 Ha).
    + intros [r ws zs us cs ci] m' evs Hc Hu.
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      * exfalso. apply Hu. apply (alloc_refusal_unforced segs scfg Halloc ms model (getr regs 17) _ _ _ _ ltac:(rewrite Hno; reflexivity) (HokS a0 Ha0)).
        -- cbn [eff_ret]. rewrite (refusal_b_mmap_epend _ _ _ _ Hno). exact (grant_na_pin_not_errno model a0 nZ Hn0 Ha0).
        -- cbn [eff_ret]. rewrite (refusal_b_mmap_epend _ _ _ _ Hno). exact Er.
      * rewrite Hchk in Hc. rewrite Er in Hc.
        destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
        destruct (grant_ok_na_pin model r nZ) eqn:Hg; [|discriminate]. cbn [andb] in Hc.
        destruct (listNN_eqb zs [(r, n)]) eqn:Hl; [|discriminate].
        apply listNN_eqb_eq in Hl. subst zs. injection Hc as <- <-.
        exists (exist _ r Hg). repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct zs; discriminate|].
      destruct (grant_ok_na_pin model r nZ && true && listNN_eqb zs [(r, n)])%bool; discriminate.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct zs; [|discriminate]; injection Hc as <- <-; exact Hh|].
      destruct (grant_ok_na_pin model r nZ && true && listNN_eqb zs [(r, n)])%bool; [|discriminate].
      injection Hc as <- <-. rewrite with_mmap_backing_halted. unfold mmap_model. rewrite with_vmmaps_halted. exact Hh.
    + intros [a Ha]; reflexivity.
  - intros [a Ha]. cbn [effs ms']. unfold ms. rewrite adv_zeros1_epend. apply HB. exact Ha.
Qed.

Lemma alloc_budget_refused_b_mmap : forall ms x8 model,
  bv_unsigned x8 = 222%Z ->
  alloc_budget_refused_b (sys_input segs ms x8) model
  = mmap_budget_refused_b (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 4) (ms_gpr ms 5) model.
Proof. intros ms x8 model Hno. unfold alloc_budget_refused_b. rewrite ExitSim.in_sysno_sys_input, Hno. reflexivity. Qed.

Lemma mmap_rw_refused_mark : forall ms x8 model flags,
  bv_unsigned x8 = 222%Z ->
  ms_gpr ms 1 <> Z_to_bv 64 0 -> ms_gpr ms 2 = Z_to_bv 64 3 ->
  ms_gpr ms 3 = flags -> mmap_flags_core flags = 34%Z ->
  ms_gpr ms 5 = Z_to_bv 64 0 ->
  mmap_noreserve_backed_ok flags model (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  alloc_budget_refused_b (sys_input segs ms x8) model = true.
Proof.
  intros ms x8 model flags Hno H1 H2 H3 Hcore H5 Hgate.
  destruct (mmap_gates_core34 flags Hcore) as (Gm & _ & _).
  rewrite (alloc_budget_refused_b_mmap ms x8 model Hno). unfold mmap_budget_refused_b.
  assert (E1 : w_is0 (ms_gpr ms 1) = false) by (unfold w_is0; apply bv_eqb_neq; exact H1).
  rewrite E1, H2, H3, H5, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl), Gm. cbn [negb]. cbv beta iota zeta.
  rewrite Hgate. reflexivity.
Qed.

Lemma srz_mmap_rw_refused : forall regs (pc : word) mem rom model w (len : Z) (flags : word) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = flags -> mmap_flags_core flags = 34%Z ->
  getr regs 15 = Z_to_bv 64 0 ->
  mmap_noreserve_backed_ok flags model (page_round_up_Z len) = false ->
  KB [] ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w len flags KB HF HE Hh H17 H11 Hlen H12 H13 Hcore H15 Hgate HKB.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  destruct (epend_len regs pc mem rom len H11 Hlen) as [Hl1 Hne1]. fold ms in Hl1, Hne1.
  apply (srz_brefused segs scfg (mkCfg ms model) KB); [reflexivity | | exact HKB].
  split; [exact Hh|]. right. exists (getr regs 17). split; [reflexivity|]. left.
  apply (mmap_rw_refused_mark ms (getr regs 17) model flags Hno Hne1
           ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
           ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13) Hcore
           ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15)).
  rewrite Hl1. exact Hgate.
Qed.

Lemma srz_mmap_rw1_bm : forall regs (pc : word) mem rom model w (len : Z) (flags : word) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = flags -> mmap_flags_core flags = 34%Z ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  (exists a, grant_ok_na_pin model a nZ = true) ->
  KB [] ->
  (mmap_noreserve_backed_ok flags model nZ = true ->
   forall a, grant_ok_na_pin model a nZ = true ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (zfill a n mem) rom)
                          (with_mmap_backing flags a n (mmap_model a n model))) KB) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w len flags KB HF HE Hh H17 H11 Hlen H12 H13 Hcore H14 H15 nZ n Hex HKB HB.
  destruct (Sumbool.sumbool_of_bool (mmap_noreserve_backed_ok flags model nZ)) as [Hgate|Hgate].
  - exact (srz_mmap_rw1 regs pc mem rom model w len flags KB HF HE Hh H17 H11 Hlen H12 H13 Hcore H14 H15 Hex Hgate (HB Hgate)).
  - exact (srz_mmap_rw_refused regs pc mem rom model w len flags KB HF HE Hh H17 H11 Hlen H12 H13 Hcore H15 Hgate HKB).
Qed.

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
  destruct (errno_ret_in mmap_errnos r); [reflexivity|].
  unfold grant_ok_na_pin, noaccess_model. reflexivity.
Qed.

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
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (unfill a n mem) rom)
                          (with_mmap_backing flags a n (noaccess_model a n model))) KB) ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) KB.
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
  pose (IB := {a : word | grant_ok_na_pin model a nZ = true}).
  pose (effs := fun i : IB => match i with exist _ a _ => mkEffectU a [] [] [(a, n)] [] [] end).
  pose (ms' := fun i : IB => match i with exist _ a _ => with_mmap_backing flags a n (noaccess_model a n model) end).
  assert (HokS : forall a, grant_ok_na_pin model a nZ = true ->
            check_syscall (sys_input segs ms (getr regs 17)) (mkEffectU a [] [] [(a, n)] [] []) model
            = CheckOk (with_mmap_backing flags a n (noaccess_model a n model)) []).
  { intros a Ha. rewrite Hchk. rewrite (grant_na_pin_not_errno model a nZ Hn0 Ha), Ha. cbn [andb].
    rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity. }
  eapply (srz_node1 (mkCfg ms model) IB (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) KB (exist _ a0 Ha0)).
  - apply (node_chk_ev_gen_noacc segs scfg ms model (getr regs 17) IB effs ms' (fun _ => []) materialize_model_accesses_nil Hh eq_refl).
    + intros [a Ha]; cbn [effs ms']. exact (HokS a Ha).
    + intros [a Ha]; cbn [effs ms']. apply alloc_nonrefusal_step. cbn [eff_ret]. rewrite (refusal_b_mmap_epend _ _ _ _ Hno).
      exact (grant_na_pin_not_errno model a nZ Hn0 Ha).
    + intros [r ws zs us cs ci] m' evs Hc Hu.
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      * exfalso. apply Hu. apply (alloc_refusal_unforced segs scfg Halloc ms model (getr regs 17) _ _ _ _ ltac:(rewrite Hno; reflexivity) (HokS a0 Ha0)).
        -- cbn [eff_ret]. rewrite (refusal_b_mmap_epend _ _ _ _ Hno). exact (grant_na_pin_not_errno model a0 nZ Hn0 Ha0).
        -- cbn [eff_ret]. rewrite (refusal_b_mmap_epend _ _ _ _ Hno). exact Er.
      * rewrite Hchk in Hc. rewrite Er in Hc.
        destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
        destruct (grant_ok_na_pin model r nZ) eqn:Hg; [|discriminate]. cbn [andb] in Hc.
        destruct (listNN_eqb us [(r, n)]) eqn:Hl; [|discriminate].
        apply listNN_eqb_eq in Hl. subst us. injection Hc as <- <-.
        exists (exist _ r Hg). repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct (errno_ret_in mmap_errnos r); destruct us; discriminate].
      destruct ci; [|destruct (errno_ret_in mmap_errnos r); destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct us; discriminate|].
      destruct (grant_ok_na_pin model r nZ && listNN_eqb us [(r, n)])%bool; discriminate.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct (errno_ret_in mmap_errnos r); destruct us; discriminate].
      destruct ci; [|destruct (errno_ret_in mmap_errnos r); destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct us; [|discriminate]; injection Hc as <- <-; exact Hh|].
      destruct (grant_ok_na_pin model r nZ && listNN_eqb us [(r, n)])%bool; [|discriminate].
      injection Hc as <- <-. rewrite with_mmap_backing_halted. unfold noaccess_model. rewrite with_vmmaps_halted. exact Hh.
    + intros [a Ha]; reflexivity.
  - intros [a Ha]. cbn [effs ms']. unfold ms. rewrite adv_unmaps1_epend. apply HB. exact Ha.
Qed.
End OurSpecNodes.

Section OurSpecNodes2.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Hypothesis Halloc : sc_alloc scfg = false.

Lemma refusal_b_mprotect_epend : forall ms x8 model r, bv_unsigned x8 = 226%Z ->
  refusal_b (sys_input segs ms x8) model r = errno_ret_in mprotect_errnos r.
Proof. intros ms x8 model r Hno. unfold refusal_b. cbn [in_sysno sys_input]. rewrite Hno. reflexivity. Qed.

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
  destruct us; [|destruct (errno_ret_in mmap_errnos r); [destruct zs|]; reflexivity].
  destruct cs; [|reflexivity]. destruct ci; [|reflexivity].
  unfold mmap_model. reflexivity.
Qed.

Lemma mmap_gates_noreplace : forall flags prot,
  (mmap_flags_core flags = 1048610 \/ mmap_flags_core flags = 1048626)%Z ->
  mmap_modeled_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_noaccess_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_rw_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_noreplace_noaccess_b (Z_to_bv 64 0) flags (Z_to_bv 64 0) = true
  /\ mmap_noreplace_noaccess_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = false
  /\ mmap_noreplace_rw_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = true
  /\ mmap_anon_b flags = true.
Proof.
  intros flags prot Hc. unfold mmap_modeled_b, mmap_noaccess_b, mmap_fixed_noaccess_b, mmap_fixed_rw_b,
    mmap_noreplace_noaccess_b, mmap_noreplace_rw_b, mmap_noreplace_flags_b.
  destruct Hc as [Hc|Hc]; rewrite Hc; (repeat split; try (vm_compute; reflexivity));
    try (destruct (bv_unsigned prot =? _)%Z; vm_compute; reflexivity);
    (apply (mmap_anon_b_of_core flags _ Hc); reflexivity).
Qed.

Lemma mmap_noreplace_rw_free_check : forall ms x8 model eff flags (addr : word) (len : Z),
  bv_unsigned x8 = 222%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  ms_gpr ms 2 = Z_to_bv 64 3 -> ms_gpr ms 3 = flags ->
  (mmap_flags_core flags = 1048610 \/ mmap_flags_core flags = 1048626)%Z ->
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
  destruct (mmap_gates_noreplace flags (Z_to_bv 64 3) Hcore) as (Gm & Gn & Gfn & Gfr & _ & Gnn & Gnr & Ga).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
  assert (E1 : w_is0 (ms_gpr ms 1) = false).
  { unfold w_is0. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E.
    rewrite Hu1 in E. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
  rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
  rewrite E1, H2, H3, H5, H0, Hu1, mmap_off_aligned_b_0, Ga, Gm, Gn, Gfn, Gfr, Gnn, Gnr. cbn [negb]. cbv beta iota zeta.
  rewrite G1, G2, G3, G4. fold nZ. fold n. rewrite Hrf.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
  destruct us; [|destruct (errno_ret_in mmap_errnos r); [destruct zs|]; reflexivity].
  destruct cs; [|reflexivity]. destruct ci; [|reflexivity].
  unfold mmap_model. reflexivity.
Qed.

Lemma srz_mmap_fixed_rw_free1 : forall regs (pc : word) mem rom model w (addr : word) (len : Z) (flags : word) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  (0 < len)%Z -> (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  (forall eff, check_syscall (sys_input segs (epend regs pc mem rom (getr regs 17)) (getr regs 17)) eff model
     = match eff with
       | mkEffectU r [] zs [] [] [] =>
           if errno_ret_in mmap_errnos r
           then match zs with [] => CheckOk model [] | _ => CheckReject end
           else if bv_eqb r addr && listNN_eqb zs [(addr, n)] && mmap_noreserve_backed_ok flags model nZ
           then CheckOk (with_mmap_backing flags addr n (mmap_model addr n model)) []
           else CheckReject
       | _ => CheckReject
       end) ->
  mmap_noreserve_backed_ok flags model nZ = true ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (zfill addr n mem) rom)
                       (with_mmap_backing flags addr n (mmap_model addr n model))) KB ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w addr len flags KB HF HE Hh H17 Hlen Hnw nZ n Hchk Hbk HB.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)). fold ms in Hchk.
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  rewrite Hbk in Hchk.
  assert (Hna : errno_ret_in mmap_errnos addr = false).
  { apply errno_ret_in_below; [reflexivity|]. pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof alloc_ceiling_val. unfold two_pow_64. lia. }
  pose (effs := fun _ : unit => mkEffectU addr [] [(addr, n)] [] [] []).
  pose (ms' := fun _ : unit => with_mmap_backing flags addr n (mmap_model addr n model)).
  assert (HokS : check_syscall (sys_input segs ms (getr regs 17)) (mkEffectU addr [] [(addr, n)] [] [] []) model
                 = CheckOk (with_mmap_backing flags addr n (mmap_model addr n model)) []).
  { rewrite Hchk, Hna, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity. }
  eapply (srz_node1 segs scfg (mkCfg ms model) unit (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) KB tt).
  - apply (node_chk_ev_gen_noacc segs scfg ms model (getr regs 17) unit effs ms' (fun _ => []) materialize_model_accesses_nil Hh eq_refl).
    + intros []; exact HokS.
    + intros []; cbv delta [effs] beta iota. apply alloc_nonrefusal_step. cbn [eff_ret]. rewrite (refusal_b_mmap_epend segs _ _ _ _ Hno). exact Hna.
    + intros [r ws zs us cs ci] m' evs Hc Hu.
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      * exfalso. apply Hu. apply (alloc_refusal_unforced segs scfg Halloc ms model (getr regs 17) _ _ _ _ ltac:(rewrite Hno; reflexivity) HokS).
        -- cbn [eff_ret]. rewrite (refusal_b_mmap_epend segs _ _ _ _ Hno). exact Hna.
        -- cbn [eff_ret]. rewrite (refusal_b_mmap_epend segs _ _ _ _ Hno). exact Er.
      * rewrite Hchk, Er in Hc.
        destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
        destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
        destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
        apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst r zs. cbn [andb] in Hc. injection Hc as <- <-.
        exists tt. repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct zs; discriminate|].
      destruct (bv_eqb r addr && listNN_eqb zs [(addr, n)] && true)%bool; discriminate.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct zs; [|discriminate]; injection Hc as <- <-; exact Hh|].
      destruct (bv_eqb r addr && listNN_eqb zs [(addr, n)] && true)%bool; [|discriminate].
      injection Hc as <- <-. rewrite with_mmap_backing_halted. unfold mmap_model. rewrite with_vmmaps_halted. exact Hh.
    + intros []; reflexivity.
  - intros []. cbv delta [effs ms'] beta iota. unfold ms. rewrite adv_zeros1_epend. exact HB.
Qed.

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

Lemma mmap_noreplace_none_free_check : forall ms x8 model eff flags (addr : word) (len : Z),
  bv_unsigned x8 = 222%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  ms_gpr ms 2 = Z_to_bv 64 0 -> ms_gpr ms 3 = flags ->
  (mmap_flags_core flags = 1048610 \/ mmap_flags_core flags = 1048626)%Z ->
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
  destruct (mmap_gates_noreplace flags (Z_to_bv 64 0) Hcore) as (Gm & Gn & Gfn & Gfr & Gnn & _ & _ & Ga).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
  assert (E1 : w_is0 (ms_gpr ms 1) = false).
  { unfold w_is0. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E.
    rewrite Hu1 in E. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
  rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
  rewrite E1, H2, H3, H5, H0, Hu1, mmap_off_aligned_b_0, Ga, Gm, Gn, Gfn, Gfr, Gnn. cbn [negb]. cbv beta iota zeta.
  rewrite G1, G2, G3, G4. fold nZ. fold n. rewrite Hrf.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
  destruct zs; [|reflexivity].
  destruct cs; [|destruct (errno_ret_in mmap_errnos r); [destruct us|]; reflexivity].
  destruct ci; [|destruct (errno_ret_in mmap_errnos r); [destruct us|]; reflexivity].
  unfold noaccess_model. reflexivity.
Qed.

Lemma srz_mmap_fixed_none_free1 : forall regs (pc : word) mem rom model w (addr : word) (len : Z) (flags : word) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  (0 < len)%Z -> (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  (forall eff, check_syscall (sys_input segs (epend regs pc mem rom (getr regs 17)) (getr regs 17)) eff model
     = match eff with
       | mkEffectU r [] [] us [] [] =>
           if errno_ret_in mmap_errnos r
           then match us with [] => CheckOk model [] | _ => CheckReject end
           else if bv_eqb r addr && listNN_eqb us [(addr, n)]
           then CheckOk (with_mmap_backing flags addr n (noaccess_model addr n model)) []
           else CheckReject
       | _ => CheckReject
       end) ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (unfill addr n mem) rom)
                       (with_mmap_backing flags addr n (noaccess_model addr n model))) KB ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w addr len flags KB HF HE Hh H17 Hlen Hnw nZ n Hchk HB.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)). fold ms in Hchk.
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Hna : errno_ret_in mmap_errnos addr = false).
  { apply errno_ret_in_below; [reflexivity|]. pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof alloc_ceiling_val. unfold two_pow_64. lia. }
  pose (effs := fun _ : unit => mkEffectU addr [] [] [(addr, n)] [] []).
  pose (ms' := fun _ : unit => with_mmap_backing flags addr n (noaccess_model addr n model)).
  assert (HokS : check_syscall (sys_input segs ms (getr regs 17)) (mkEffectU addr [] [] [(addr, n)] [] []) model
                 = CheckOk (with_mmap_backing flags addr n (noaccess_model addr n model)) []).
  { rewrite Hchk, Hna, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity. }
  eapply (srz_node1 segs scfg (mkCfg ms model) unit (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) KB tt).
  - apply (node_chk_ev_gen_noacc segs scfg ms model (getr regs 17) unit effs ms' (fun _ => []) materialize_model_accesses_nil Hh eq_refl).
    + intros []; exact HokS.
    + intros []; cbv delta [effs] beta iota. apply alloc_nonrefusal_step. cbn [eff_ret]. rewrite (refusal_b_mmap_epend segs _ _ _ _ Hno). exact Hna.
    + intros [r ws zs us cs ci] m' evs Hc Hu.
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      * exfalso. apply Hu. apply (alloc_refusal_unforced segs scfg Halloc ms model (getr regs 17) _ _ _ _ ltac:(rewrite Hno; reflexivity) HokS).
        -- cbn [eff_ret]. rewrite (refusal_b_mmap_epend segs _ _ _ _ Hno). exact Hna.
        -- cbn [eff_ret]. rewrite (refusal_b_mmap_epend segs _ _ _ _ Hno). exact Er.
      * rewrite Hchk, Er in Hc.
        destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
        destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
        destruct (listNN_eqb us [(addr, n)]) eqn:Hl; [|discriminate].
        apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst r us. cbn [andb] in Hc. injection Hc as <- <-.
        exists tt. repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct (errno_ret_in mmap_errnos r); destruct us; discriminate].
      destruct ci; [|destruct (errno_ret_in mmap_errnos r); destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct us; discriminate|].
      destruct (bv_eqb r addr && listNN_eqb us [(addr, n)])%bool; discriminate.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct (errno_ret_in mmap_errnos r); destruct us; discriminate].
      destruct ci; [|destruct (errno_ret_in mmap_errnos r); destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct us; [|discriminate]; injection Hc as <- <-; exact Hh|].
      destruct (bv_eqb r addr && listNN_eqb us [(addr, n)])%bool; [|discriminate].
      injection Hc as <- <-. rewrite with_mmap_backing_halted. unfold noaccess_model. rewrite with_vmmaps_halted. exact Hh.
    + intros []; reflexivity.
  - intros []. cbv delta [effs ms'] beta iota. unfold ms. rewrite adv_unmaps1_epend. exact HB.
Qed.

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
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (zfill addr n mem) rom)
                       (mprotect_model addr n model)) KB ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) KB.
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
  assert (Hz : errno_ret_in mprotect_errnos (Z_to_bv 64 0) = false) by reflexivity.
  pose (effs := fun _ : unit => mkEffectU (Z_to_bv 64 0) [] [(addr, n)] [] [] []).
  pose (ms' := fun _ : unit => mprotect_model addr n model).
  assert (HokS : check_syscall (sys_input segs ms (getr regs 17)) (mkEffectU (Z_to_bv 64 0) [] [(addr, n)] [] [] []) model
                 = CheckOk (mprotect_model addr n model) []).
  { rewrite Hchk, Hz. unfold w_is0. rewrite bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity. }
  eapply (srz_node1 segs scfg (mkCfg ms model) unit (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) KB tt).
  - apply (node_chk_ev_gen_noacc segs scfg ms model (getr regs 17) unit effs ms' (fun _ => []) materialize_model_accesses_nil Hh eq_refl).
    + intros []; exact HokS.
    + intros []; cbv delta [effs] beta iota. apply alloc_nonrefusal_step. cbn [eff_ret]. rewrite (refusal_b_mprotect_epend _ _ _ _ Hno). exact Hz.
    + intros [r ws zs us cs ci] m' evs Hc Hu.
      destruct (errno_ret_in mprotect_errnos r) eqn:Er.
      * exfalso. apply Hu. apply (alloc_refusal_unforced segs scfg Halloc ms model (getr regs 17) _ _ _ _ ltac:(rewrite Hno; reflexivity) HokS).
        -- cbn [eff_ret]. rewrite (refusal_b_mprotect_epend _ _ _ _ Hno). exact Hz.
        -- cbn [eff_ret]. rewrite (refusal_b_mprotect_epend _ _ _ _ Hno). exact Er.
      * rewrite Hchk, Er in Hc.
        destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
        cbn [andb] in Hc. destruct (w_is0 r) eqn:E0; [|discriminate].
        destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
        apply listNN_eqb_eq in Hl. subst zs. injection Hc as <- <-.
        unfold w_is0 in E0. apply bv_eqb_eq in E0. subst r.
        exists tt. repeat split; reflexivity.
    + intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mprotect_errnos r); [destruct zs; discriminate|].
      cbn [andb] in Hc. destruct (w_is0 r && listNN_eqb zs [(addr, n)])%bool; discriminate.
    + intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mprotect_errnos r); [destruct zs; [|discriminate]; injection Hc as <- <-; exact Hh|].
      cbn [andb] in Hc. destruct (w_is0 r && listNN_eqb zs [(addr, n)])%bool; [|discriminate].
      injection Hc as <- <-. unfold mprotect_model. rewrite with_vmmaps_halted. exact Hh.
    + intros []; reflexivity.
  - intros []. cbv delta [effs ms'] beta iota. unfold ms. rewrite adv_zeros1_epend. exact HB.
Qed.

Definition fixed_free_core (c : Z) : Prop := (c = 50 \/ (c = 1048610 \/ c = 1048626))%Z.

Lemma srz_mmap_fixed_rw_free1R : forall regs (pc : word) mem rom model w (addr : word) (len : Z) (flags : word) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = flags -> fixed_free_core (mmap_flags_core flags) ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  mmap_noreserve_backed_ok flags model nZ = true ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (zfill addr n mem) rom)
                       (with_mmap_backing flags addr n (mmap_model addr n model))) KB ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w addr len flags KB HF HE Hh H17 H10 Hal Hpos H11 Hlen Hce Hisp H12 H13 Hcore H14 H15 nZ n Hrf Hbk HB.
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  eapply (srz_mmap_fixed_rw_free1 regs pc mem rom model w addr len flags KB HF HE Hh H17 Hlen Hce); [|exact Hbk|exact HB].
  intros eff. destruct Hcore as [Hc|Hc].
  - apply (mmap_fixed_rw_free_check _ _ model eff flags addr len Hno);
      rewrite ?ms_gpr_epend0, ?ms_gpr_epend1, ?ms_gpr_epend2, ?ms_gpr_epend3, ?ms_gpr_epend4, ?ms_gpr_epend5; try assumption.
  - apply (mmap_noreplace_rw_free_check _ _ model eff flags addr len Hno);
      rewrite ?ms_gpr_epend0, ?ms_gpr_epend1, ?ms_gpr_epend2, ?ms_gpr_epend3, ?ms_gpr_epend4, ?ms_gpr_epend5; try assumption.
Qed.

Lemma srz_mmap_fixed_none_free1R : forall regs (pc : word) mem rom model w (addr : word) (len : Z) (flags : word) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = flags -> fixed_free_core (mmap_flags_core flags) ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  srealizes segs scfg (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (unfill addr n mem) rom)
                       (with_mmap_backing flags addr n (noaccess_model addr n model))) KB ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w addr len flags KB HF HE Hh H17 H10 Hal Hpos H11 Hlen Hce Hisp H12 H13 Hcore H14 H15 nZ n Hrf HB.
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  eapply (srz_mmap_fixed_none_free1 regs pc mem rom model w addr len flags KB HF HE Hh H17 Hlen Hce); [|exact HB].
  intros eff. destruct Hcore as [Hc|Hc].
  - apply (mmap_fixed_none_free_check _ _ model eff flags addr len Hno);
      rewrite ?ms_gpr_epend0, ?ms_gpr_epend1, ?ms_gpr_epend2, ?ms_gpr_epend3, ?ms_gpr_epend4, ?ms_gpr_epend5; try assumption.
  - apply (mmap_noreplace_none_free_check _ _ model eff flags addr len Hno);
      rewrite ?ms_gpr_epend0, ?ms_gpr_epend1, ?ms_gpr_epend2, ?ms_gpr_epend3, ?ms_gpr_epend4, ?ms_gpr_epend5; try assumption.
Qed.

Lemma fixed_free_core_32 : fixed_free_core (mmap_flags_core (Z_to_bv 64 50)).          Proof. left. apply mmap_flags_core_32. Qed.
Lemma fixed_free_core_4032 : fixed_free_core (mmap_flags_core (Z_to_bv 64 16434)).     Proof. left. apply mmap_flags_core_4032. Qed.
Lemma fixed_free_core_104022 : fixed_free_core (mmap_flags_core (Z_to_bv 64 1064994)). Proof. right. left. apply mmap_flags_core_104022. Qed.
Lemma fixed_free_core_104032 : fixed_free_core (mmap_flags_core (Z_to_bv 64 1065010)). Proof. right. right. apply mmap_flags_core_104032. Qed.

End OurSpecNodes2.

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
  - apply APSK.amap_eqb_eq in He. subst m0. right. auto.
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
  - apply APSK.amap_eqb_eq in He. subst h. exfalso. apply H. left. reflexivity.
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
    { destruct (amap_eqb h m) eqn:He; [|reflexivity]. apply APSK.amap_eqb_eq in He. subst h. congruence. }
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
    + apply APSK.amap_eqb_eq in He. subst h.
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

Definition hull_lt (A : atable) : Prop := img_lo A < img_hi A.

Section Nodes.
Variable SEGS : list Segment.
Variable scfg : SpuriousCfg.
Variable A : atable.
Variable nx0 : nat.                      Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.     Variable FS0 : Fs.Fs.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis RES_len : res_len_ok SEGS A.
Hypothesis RES_hull : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A)
                             (segments_reserved SEGS).
Hypothesis HULL_ok : hull_ok A.                  Hypothesis SHADOW_ok : shadow_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ uE E e_sp0 <= bv_unsigned a.
Hypothesis e_sp0_init : expr_vars_lt nx0 e_sp0 = true.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

Hypothesis HULL_tiled : forall z, img_lo A <= z < img_hi A -> in_ivs z (segments_reserved SEGS) = true.

#[local] Notation CSOK := (APSK.cs_ok SEGS A LIMIT SINV argH FS0).
#[local] Notation HID := (APSK.hid A argH).
#[local] Notation VIS := (APSK.vis A).
#[local] Notation MR := (APSK.Mr A argH).
#[local] Notation ALLOW := (APSK.allowA A).
#[local] Notation cfg := (cfg_of SEGS).

Let HS : nat -> option acs := fun _ => None.
Let XN : nat -> list expr -> acs -> option acs := fun _ _ _ => None.
Let XE : nat -> list expr -> acs -> option (Z * list spiece * acs) := fun _ _ _ => None.
Let XB : nat -> list expr -> acs -> option (acs * acs) := fun _ _ _ => None.
Let RES_len' : length (segments_reserved SEGS) = n_res A := RES_len.
Let HULL_ok' : 0 <= img_lo A /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0 /\ img_hi A <= KHI := HULL_ok.
Let SHADOW_ok' : 0 <= shadow_off A <= 2 ^ 47 := SHADOW_ok.
Let RES_hullH : RES_hull_def SEGS A := RES_hull.

Let reg_sound' := APSK.reg_sound SEGS A LIMIT SINV argH FS0.
Let reg_lit_sound' := APSK.reg_lit_sound SEGS A LIMIT SINV argH FS0.
Let kentry_keep_sem' := APSK.kentry_keep_sem SEGS.
Let kentry_apart_b_sem' := APSK.kentry_apart_b_sem SEGS.
Let regs_ok_set_n' := APSK.regs_ok_set_n.
Let in_ivs_map_den' := APSK.in_ivs_map_den.
Let kimg_clip_in_hull' := APSK.kimg_clip_in_hull A.
Let cs_ok_agree' := APSK.cs_ok_agree SEGS A nx0 LIMIT SINV argH e_sp0_init argH_agree SINV_agree FS0.
Let cs_ok_frame' := APSK.cs_ok_frame SEGS A LIMIT SINV argH SINV_frame FS0.
Let hid_agree' := APSK.hid_agree A nx0 argH e_sp0_init argH_agree.
Let vis_add_sound' := APSK.vis_add_sound SEGS A LIMIT HS XN XE XB SHADOW_ok SINV argH argH_high FS0 0%nat.
Let A_wf_allowA' := APSK.A_wf_allowA A HS XN XE XB 0%nat.
Let know_ok_unhide' := APSK.know_ok_unhide SEGS A.
Let hid_hull' := APSK.hid_hull A HULL_ok argH argH_high.
Let H_off_segments_cs' := APSK.H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH argH_high.
Let maps_match_exact' := APSK.maps_match_exact nx0 HS XN XE XB.

Lemma mmap_len_sound : forall E cs R FULL model ne nlo nhi,
  CSOK E cs R FULL model -> mmap_len cs = Some (ne, nlo, nhi) ->
  let len := bv_unsigned (edenot E (reg cs 11)) in
  getr R (Z_to_bv 5 11) = Z_to_bv 64 len
  /\ 0 < len < 2 ^ 64
  /\ edenot E ne = Z_to_bv 64 (page_round_up_Z len)
  /\ 0 < nlo /\ nlo <= page_round_up_Z len <= nhi
  /\ page_round_up_Z len mod 4096 = 0
  /\ (forall E', edenot E' (reg cs 11) = edenot E (reg cs 11) -> edenot E' ne = edenot E ne).
Proof.
  intros E cs R FULL model ne nlo nhi HC HML len.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (reg_sound' E cs R FULL model 11 HC ltac:(lia)) as R11. change (Z.of_nat 11) with 11 in R11.
  pose proof (u64_range (edenot E (reg cs 11))) as Hr.
  rewrite mmap_len_eq in HML.   unfold mmap_len_ref in HML.
  destruct (reg_lit cs 11) as [lz|] eqn:H11.
  - destruct (Z.ltb_spec 0 lz); [|discriminate]. injection HML as <- <- <-.
    destruct (reg_lit_sound' E cs R FULL model 11 lz HC ltac:(lia) H11) as [R11' Hlz]. change (Z.of_nat 11) with 11 in R11'.
    assert (Hlen : len = lz).
    { unfold len. rewrite <- R11, R11'. apply u64_lit. unfold two64 in Hlz. lia. }
    rewrite Hlen. pose proof (page_round_up_Z_bounds lz ltac:(lia)) as PB. unfold page_size in PB.
    rewrite page_up_eq.
    split; [exact R11'|]. split; [unfold two64 in Hlz; lia|]. split; [reflexivity|]. split; [lia|]. split; [lia|].
    split; [apply page_round_up_Z_aligned'|]. intros E' _. reflexivity.
  - destruct (xlo (kn cs) (reg cs 11)) as [lo|] eqn:Hxl; [|discriminate].
    destruct (xhi (kn cs) (reg cs 11)) as [hi|] eqn:Hxh; [|discriminate].
    match type of HML with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
    injection HML as <- <- <-.
    apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hlo Hal].
    apply Z.ltb_lt in Hlo. apply Z.leb_le in Hal. apply Z.leb_le in Hhi.
    pose proof (xlo_sound SEGS E _ (kn cs) _ lo HK Hxl) as B1.
    pose proof (xhi_sound SEGS E _ (kn cs) _ hi HK Hxh) as B2.
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
    intros E' HE'. exact HE'.
Qed.

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

Lemma reserved_free_above : forall model (lo n : word),
  vm_reserved (m_vmmaps model) = segments_reserved SEGS ->
  img_hi A <= bv_unsigned lo ->
  region_free (vm_reserved (m_vmmaps model)) lo n = true.
Proof.
  intros model lo n Hres Hlo. rewrite Hres. apply RefNodes.region_free_intro. intros b s Hin.
  pose proof (proj1 (Forall_forall _ _) RES_hullH _ Hin) as [H1 H2]. cbn [fst snd] in H1, H2. right. lia.
Qed.

Lemma reserved_free_hull_apart : forall model (lo n : word),
  vm_reserved (m_vmmaps model) = segments_reserved SEGS ->
  (bv_unsigned lo + bv_unsigned n <= img_lo A \/ img_hi A <= bv_unsigned lo) ->
  region_free (vm_reserved (m_vmmaps model)) lo n = true.
Proof.
  intros model lo n Hres Hlo. rewrite Hres. apply RefNodes.region_free_intro. intros b s Hin.
  pose proof (proj1 (Forall_forall _ _) RES_hullH _ Hin) as [H1 H2]. cbn [fst snd] in H1, H2.
  pose proof (u64_range s). destruct Hlo; [left | right]; lia.
Qed.

Lemma vis_add_inv : forall cs b n k cs2,
  vis_add A LIMIT cs b n k = Some cs2 ->
  exists nhi, xhi (kn cs) n = Some nhi /\
  cs2 = ACS (mk_ss (pc cs) (s_regs (a_ss cs)) (shadow_facts A (kn cs) (a_maps cs) b n ++ k) (nxt cs))
            (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
            ((b, n) :: a_vis cs) (a_ghost cs) (a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs) (a_hna cs) (a_hlz cs).
Proof.
  intros cs b n k cs2 Hv. rewrite vis_add_eq in Hv.   unfold vis_add_ref in Hv.
  destruct (split_lit b) as [bb bk]. destruct (shadow_of A (kn cs) b n) as [[sb sk] sn] eqn:Hsh.
  destruct (xhi (kn cs) n) as [nhi|]; [|discriminate].
  match type of Hv with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
  injection Hv as <-. exists nhi. split; [reflexivity|]. unfold shadow_facts. rewrite Hsh. reflexivity.
Qed.

Lemma in_allow_ext : forall E cs cs', a_vis cs' = a_vis cs -> in_allow A E cs' = in_allow A E cs.
Proof. intros E cs cs' H. apply functional_extensionality. intros z. unfold in_allow, in_vis, in_sh. rewrite H. reflexivity. Qed.

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
  gp_isp : vm_init_sp (m_vmmaps model') = vm_init_sp (m_vmmaps model)    }.

Definition grant_mem (kd : mkind) (a n : word) (FULL FULL' : word -> option byte) : Prop :=
  (forall x : word, bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x -> FULL' x = FULL x)
  /\ (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n ->
        FULL' x = if kind_none kd then None else Some (Z_to_bv 8 0)).

Lemma vis_grant_out : forall kd (a n : word) model model' E cs cs1 (x : word),
  grant_post kd a n model model' ->
  a_vis cs1 = a_vis cs ->
  0 < bv_unsigned n -> bv_unsigned a mod 4096 = 0 -> bv_unsigned n mod 4096 = 0 ->
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x) ->
  VIS E cs1 model' x = VIS E cs model x.
Proof.
  intros kd a n model model' E cs cs1 x GPo Hvis Hn Hal Hnl Hx.
  unfold vis. rewrite (gp_maps _ _ _ _ _ GPo), (gp_noacc _ _ _ _ _ GPo), (gp_lazy _ _ _ _ _ GPo).
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

Definition maps_apart (E : env) (ms : list amap) (lo n : Z) : Prop :=
  forall m, In m ms -> is_fog m = false ->
    lo + n <= bv_unsigned (edenot E (am_base m)) \/
    bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= lo.

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

Definition isp_facts (E : env) : Prop :=
  sp_window_lo <= uE E e_sp0 <= sp_window_hi /\ uE E e_sppg = pagedown (uE E e_sp0).

Lemma u_e_top : forall E, isp_facts E -> uE E e_top = utop E.
Proof.
  intros E [Hsp Hpg]. pose proof (utop_bounds E) as UB. unfold utop in UB |- *.
  unfold e_top, eaddz, uE in *. rewrite mkAlu_denot, edenot_lit, u_add64, u_lit64. rewrite Hpg.
  unfold two64, sp_window_lo in *. pose proof (u64_range (edenot E e_sp0)).
  replace ((-8388608) mod 2 ^ 64) with (2 ^ 64 - 8388608) by reflexivity.
  replace (pagedown (bv_unsigned (edenot E e_sp0)) + (2 ^ 64 - 8388608))
    with ((pagedown (bv_unsigned (edenot E e_sp0)) - 8388608) + 1 * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small; lia.
Qed.

Lemma lit_ivs_apart : forall E ms lo n a' m,
  maps_apart E ms lo n -> In (a', m) (lit_ivs ms) -> lo + n <= a' \/ a' + m <= lo.
Proof.
  intros E ms lo n a' m Hap Hin.
  destruct (PlaceLemmasK.lit_ivs_In ms a' m Hin) as ((B0 & B1 & B2) & m0 & Hm0 & Hnf & Hb & Hl).
  pose proof (Hap m0 Hm0 Hnf) as D. rewrite Hb, Hl in D. cbn [edenot] in D.
  unfold two64 in B2. rewrite !u64_lit in D by lia. exact D.
Qed.

Lemma runs_apart_grant : forall E ms lo n rlo rn k,
  maps_apart E ms lo n -> 0 < n -> In (rlo, rn, k) (PlaceLemmasK.runs ms) -> lo + n <= rlo \/ rlo + rn <= lo.
Proof.
  intros E ms lo n rlo rn k Hap Hn Hin. eapply PlaceLemmasK.runs_apart; [exact Hin | exact Hn |].
  intros a' m Hin'. eapply lit_ivs_apart; [exact Hap | exact Hin'].
Qed.

Lemma inside_runs_apart : forall E M k ms b o l lo n,
  know_ok SEGS E M k -> maps_apart E ms lo n -> 0 < n ->
  inside_runs k ms b o l = true ->
  estart E (SA b o) + elenZ E l <= lo \/ lo + n <= estart E (SA b o).
Proof.
  intros E M k ms b o l lo n HK Hap Hn H. unfold inside_runs in H.
  destruct (base_range k b) as [[blo bhi]|] eqn:Hb; [|discriminate]. destruct (xhi k l) as [lh|] eqn:Hlh; [|discriminate].
  pose proof (xhi_sound SEGS E M k l lh HK Hlh) as L1. pose proof (base_range_sound SEGS E M k b blo bhi HK Hb) as [B1 B2].
  apply existsb_exists in H as ([[ra rn] rk] & Hin & Hr). apply andb_prop in Hr as [Hr1 Hr2]. apply Z.leb_le in Hr1. apply Z.leb_le in Hr2.
  pose proof (runs_apart_grant E ms lo n ra rn rk Hap Hn Hin) as D.
  unfold estart, elenZ. cbn [a_base a_off]. lia.
Qed.

Lemma safe_range_apart : forall E M k ms b o l lo n,
  know_ok SEGS E M k -> maps_apart E ms lo n ->
  0 <= lo -> (lo + n <= img_lo A \/ img_hi A <= lo) -> lo + n <= utop E -> isp_facts E -> 0 < n ->
  safe_range A k ms b o l = true ->
  estart E (SA b o) + elenZ E l <= lo \/ lo + n <= estart E (SA b o).
Proof.
  intros E M k ms b o l lo n HK Hap Hlo0 Hlo Hhi Hsp Hn H. unfold safe_range in H. apply orb_prop in H as [H|H]; [apply orb_prop in H as [H|H]|].
  - destruct (xhi k l) as [lh|] eqn:Hlh; [|discriminate]. destruct (base_range k b) as [[blo bhi]|] eqn:Hb; [|discriminate].
    pose proof (xhi_sound SEGS E M k l lh HK Hlh) as L1. pose proof (base_range_sound SEGS E M k b blo bhi HK Hb) as [B1 B2].
    unfold estart, elenZ. cbn [a_base a_off].
    apply orb_prop in H as [H|H]; apply andb_prop in H as [H1 H2]; apply Z.leb_le in H2.
    +
      pose proof (lin_ge0_sound SEGS E M k _ _ HK H1) as G. cbn [xt_den] in G.
      pose proof (u_e_top E Hsp) as T. unfold uE in T. rewrite T in G. lia.
    + apply Z.leb_le in H1. lia.
  - eapply inside_maps_apart; eassumption.
  - eapply inside_runs_apart; eassumption.
Qed.

Lemma grant_keep_apart : forall E M k ms K lo n,
  know_ok SEGS E M k -> maps_apart E ms lo n ->
  0 <= lo -> (lo + n <= img_lo A \/ img_hi A <= lo) -> lo + n <= utop E -> isp_facts E -> 0 < n ->
  grant_keep_b A k ms K = true ->
  match K with KImg _ _ => False | _ => True end ->
  kfoot_apart E K lo n.
Proof.
  intros E M k ms K lo n HK Hap Hlo0 Hlo Hhi Hsp Hn H HnI. unfold kfoot_apart, kfoot.
  destruct K as [[b o] w v|[b o] l|[b o] l kb|ilo ihi|e m|e rlo rhi|[b o] l|a1 n1 a2 n2|[b o] l fc|[b o] l]; cbn [grant_keep_b] in H;
    try exact I; [apply andb_prop in H as [Hw H]; apply Nat.leb_le in Hw| | | destruct HnI | | |];
    pose proof (safe_range_apart E M k ms b o _ lo n HK Hap Hlo0 Hlo Hhi Hsp Hn H) as D; try lia.
  rewrite elenZ_lit'' in D by lia. lia.
Qed.

Lemma kn_grant_filter_ok : forall E M M' k ms lo n,
  know_ok SEGS E M k -> maps_apart E ms lo n ->
  0 <= lo -> (lo + n <= img_lo A \/ img_hi A <= lo) -> lo + n <= utop E -> isp_facts E -> 0 < n ->
  (forall x : word, bv_unsigned x < lo \/ lo + n <= bv_unsigned x -> M' x = M x) ->
  know_ok SEGS E M' (kn_grant_filter A k ms).
Proof.
  intros E M M' k ms lo n HK Hap Hlo0 Hlo Hhi Hsp Hn Hout. unfold kn_grant_filter.
  pose proof (kimg_clip_in_hull' (List.filter (grant_keep_b A k ms) k)) as Hhull.
  unfold know_ok. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) Hhull K Hin) as HKh.
  apply kimg_clip_incl in Hin. apply filter_In in Hin as [Hin Hkeep].
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  eapply kentry_keep_sem'; [exact HKK | | exact Hout].
  destruct K as [| | |ilo ihi| | | | | |];
    try (eapply grant_keep_apart; [exact HK | exact Hap | exact Hlo0 | exact Hlo | exact Hhi | exact Hsp | exact Hn | exact Hkeep | exact I]).

  unfold kfoot_apart, kfoot. cbn in HKh. lia.
Qed.

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

Lemma grant_new_facts : forall E cs R FULL model (a n : word) nZ,
  CSOK E cs R FULL model ->
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) a n = true ->
  bv_unsigned n = nZ -> 0 < nZ ->
  (bv_unsigned a + nZ <= img_lo A \/ img_hi A <= bv_unsigned a) -> bv_unsigned a + nZ <= utop E ->
  forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + nZ ->
    in_ivs (bv_unsigned x) (vm_maps (m_vmmaps model)) = false
    /\ in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)) = false
    /\ argH E x = false /\ in_hull A (bv_unsigned x) = false /\ (utop E <=? bv_unsigned x) = false
    /\ VIS E cs model x = false.
Proof.
  intros E cs R FULL model a n nZ HC Hrf Un HnZ Himg HaC x Hx.
  rewrite region_free_app in Hrf. apply andb_prop in Hrf as [_ Hrf2].
  pose proof (region_free_sem _ a n (bv_unsigned x) Hrf2 ltac:(rewrite Un; lia) ltac:(rewrite Un; lia)) as M0.
  assert (N0 : in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)) = false).
  { destruct (in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model))) eqn:En; [|reflexivity]. exfalso.
    apply (co_nasub _ _ _ _ _ _ _ _ _ _ _ HC) in En. congruence. }
  assert (Hh : in_hull A (bv_unsigned x) = false).
  { unfold in_hull. apply andb_false_iff. destruct Himg; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia. }
  assert (Hc : (utop E <=? bv_unsigned x) = false) by (apply Z.leb_gt; lia).
  repeat split; try assumption.
  - destruct (argH E x) eqn:Ea; [|reflexivity]. pose proof (argH_high _ _ Ea). pose proof (utop_bounds E). lia.
  - unfold vis. rewrite Hh, Hc, M0. reflexivity.
Qed.

Lemma grant_cs1_ok : forall E cs R FULL model kd (a n : word) nZ model' FULL' sr' R' knew be ne nhi (eager : bool) ylo' nx',
  CSOK E cs R FULL model ->
  bv_unsigned n = nZ -> 0 < nZ -> nZ mod 4096 = 0 -> bv_unsigned a mod 4096 = 0 ->
  (bv_unsigned a + nZ <= img_lo A \/ img_hi A <= bv_unsigned a) -> bv_unsigned a + nZ <= utop E ->
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) a n = true ->
  grant_post kd a n model model' -> grant_mem kd a n FULL FULL' ->
  regs_ok E sr' R' ->
  edenot E be = a -> edenot E ne = n ->
  know_ok SEGS E (MR E cs model' FULL') knew ->
  (kind_none kd || kind_lazy kd = negb eager)%bool -> is_tok_kind kd = false -> nZ <= nhi ->
  (eager = true -> a_eager cs + a_abytes cs + nhi <= LIMIT) ->
  ylo' <= a_ylo cs ->
  (forall m, In m (a_maps cs) -> is_hole m = true ->
     bv_unsigned a + nZ <= uE E (am_base m) \/ uE E (am_base m) + uE E (am_len m) <= bv_unsigned a) ->
  let cs1 := add_entry cs sr' (knew ++ kn_grant_filter A (kn cs) (a_maps cs)) nx' (AM be ne kd) nhi eager ylo' in
  CSOK E cs1 R' FULL' model'
  /\ (forall x : word, bv_unsigned x < bv_unsigned a \/ bv_unsigned a + nZ <= bv_unsigned x ->
        MR E cs1 model' FULL' x = MR E cs model FULL x)
  /\ MR E cs1 model' FULL' = MR E cs model' FULL'.
Proof.
  intros E cs R FULL model kd a n nZ model' FULL' sr' R' knew be ne nhi eager ylo' nx'
         HC Un HnZpos HnZal Hal Himg_a HaC Hrf GPo [GM1 GM2] Hregs Hbase HneE Hknew Hkind Hkfog Hnhi Hbudget Hylo Hholes cs1.
  pose proof (u64_range a) as Ra. pose proof (utop_bounds E) as UB.
  pose proof (co_isp _ _ _ _ _ _ _ _ _ _ _ HC) as [ISP1 ISP2]. pose proof ISP2 as ISP. unfold sp_window_lo, sp_window_hi in ISP2.
  pose proof HULL_ok' as (HU0 & HU1 & HU2 & HU3).
  pose proof (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) as Hmaps.
  pose proof (maps_apart_of_region_free E (a_maps cs) model a n Hmaps Hrf) as Hapart. rewrite Un in Hapart.
  pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as Hwf.
  pose proof (grant_new_facts E cs R FULL model a n nZ HC Hrf Un HnZpos Himg_a HaC) as NEW.

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

  pose proof (grant_wf kd a n model model' GPo Hwf ltac:(rewrite Un; lia)) as Hwf'.
  destruct HC as [Xregs Xlog Xknow Xhalt Xfds Xfs Xtid Xres Xlimit Xmaps Xholes Xseps Xwf Xbounds Xlazyb Xnasub Xnone Xkinds Xtotsz Xisp Xbrk Xsbrk Xeager Xabytes Xminv Xzero Xsinv Xhna Xhlz Xtidv].
  constructor.
  all: unfold cs1, add_entry; cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_hna a_hlz kn s_regs s_log s_know s_next mk_ss].
  all: try change (ALLOW E (ACS ?s ?m ?t ?y ?e (a_vis cs) (a_ghost cs) ?ab ?br ?fd ?ti ?hn ?hl)) with (ALLOW E cs).
  -   exact Hregs.
  -   reflexivity.
  -   apply Forall_app. split.
    + unfold cs1, add_entry in MRSAME. cbn [kn a_ss s_know mk_ss] in MRSAME. rewrite MRSAME. exact Hknew.
    + eapply kn_grant_filter_ok; [exact Xknow | exact Hapart | lia | exact Himg_a | exact HaC | exact ISP | exact HnZpos | exact MROUT].
  -   rewrite (gp_halted _ _ _ _ _ GPo). exact Xhalt.
  -   unfold fds_ok in *. rewrite (gp_fds _ _ _ _ _ GPo), (gp_fs _ _ _ _ _ GPo). exact Xfds.
  -   rewrite (gp_fs _ _ _ _ _ GPo). exact Xfs.
  -   rewrite (gp_tid _ _ _ _ _ GPo). exact Xtid.
  -   rewrite (gp_res _ _ _ _ _ GPo). exact Xres.
  -   rewrite (gp_limit _ _ _ _ _ GPo). exact Xlimit.
  -   rewrite (gp_maps _ _ _ _ _ GPo). rewrite <- Hbase, <- HneE. apply maps_match_cons; [exact Hkfog | exact Xmaps].
  -
    rewrite (gp_res _ _ _ _ _ GPo), (gp_maps _ _ _ _ _ GPo). apply Forall_cons.
    + intros Hh. exfalso. unfold is_hole in Hh. cbn [am_kind] in Hh. destruct kd; cbn in Hkfog, Hh; discriminate.
    + apply Forall_forall. intros m Hm Hk. destruct (proj1 (Forall_forall _ _) Xholes m Hm Hk) as [F1 F2]. split; [|lia].
      intros iv Hiv. apply in_app_iff in Hiv as [Hiv|[<-|Hiv]].
      * apply F1. apply in_app_iff. left. exact Hiv.
      * cbn [fst snd]. rewrite Un. pose proof (Hholes m Hm Hk). lia.
      * apply F1. apply in_app_iff. right. exact Hiv.
  -   rewrite (gp_maps _ _ _ _ _ GPo). constructor; [|exact Xseps].
    apply Forall_forall. intros [b s] Hin. unfold iv_disjoint. cbn [fst snd]. rewrite Un.
    rewrite region_free_app in Hrf. apply andb_prop in Hrf as [_ Hrf2].
    pose proof (RefNodes.region_free_In _ a n b s Hrf2 Hin). rewrite Un in *. lia.
  -   exact Hwf'.
  -   rewrite (gp_maps _ _ _ _ _ GPo). apply Forall_cons; [|exact Xbounds]. cbn [fst snd]. rewrite Un. repeat split; lia.
  -   rewrite (gp_lazy _ _ _ _ _ GPo). destruct (kind_lazy kd); [apply Forall_cons; [cbn [fst snd]; rewrite Un; lia|]|]; exact Xlazyb.
  -   intros z Hz. rewrite (gp_maps _ _ _ _ _ GPo). rewrite in_ivs_cons. rewrite (gp_noacc _ _ _ _ _ GPo) in Hz.
    destruct (kind_none kd); [rewrite in_ivs_cons in Hz; apply orb_prop in Hz as [Hz|Hz]; [rewrite Hz; reflexivity|]|];
      rewrite (Xnasub z Hz); apply orb_true_r.
  -   apply Forall_cons.
    + cbn [am_kind amap_den am_base am_len]. intros Hk. rewrite (gp_noacc _ _ _ _ _ GPo).
      replace (kind_none kd) with true by (destruct Hk as [-> | ->]; reflexivity). left. unfold amap_den. cbn [am_base am_len]. rewrite Hbase, HneE. reflexivity.
    + apply Forall_forall. intros m Hm Hk. rewrite (gp_noacc _ _ _ _ _ GPo).
      pose proof (proj1 (Forall_forall _ _) Xnone m Hm Hk) as X. destruct (kind_none kd); [right|]; exact X.
  -   apply Forall_cons.
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
  -   rewrite (gp_res _ _ _ _ _ GPo), (gp_maps _ _ _ _ _ GPo).
    rewrite sum_sizes_app in *. cbn [sum_sizes snd]. rewrite Un. cbn [sum_sizes] in Xtotsz. lia.
  -   rewrite (gp_isp _ _ _ _ _ GPo). exact (conj ISP1 ISP2).
  -   rewrite (gp_brk _ _ _ _ _ GPo). exact Xbrk.
  -   rewrite (gp_brk _ _ _ _ _ GPo), (gp_sbrk _ _ _ _ _ GPo). exact Xsbrk.
  -   pose proof (grant_eager_le kd a n model model' GPo Xwf ltac:(rewrite Un; lia)) as EG. rewrite Hkind in EG.
    destruct eager; cbn [negb] in EG; [|lia]. rewrite Un in EG. lia.
  -   exact Xabytes.
  -   destruct Xminv as [N1 N2 N3 N4 N5]. constructor; rewrite ?(gp_mat _ _ _ _ _ GPo), ?(gp_limit _ _ _ _ _ GPo); try assumption.
    + intros p Hp. rewrite (gp_lazy _ _ _ _ _ GPo). destruct (kind_lazy kd); [rewrite page_in_ranges_cons, (N4 p Hp); apply orb_true_r | exact (N4 p Hp)].
    + left. reflexivity.
  -   intros x Hh Hm Hna Hlz Hgh.
    destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge]; [|destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + nZ)) as [Hlt2|Hge2]].
    + rewrite (GM1 x) by lia. apply Xzero; [rewrite <- (HIDOUT x) by lia; exact Hh | | | | exact Hgh].
      * rewrite (gp_maps _ _ _ _ _ GPo), in_ivs_cons in Hm. apply orb_prop in Hm as [Hm|Hm]; [|exact Hm].
        apply andb_prop in Hm as [Hm _]. apply Z.leb_le in Hm. cbn [fst] in Hm. lia.
      * rewrite (gp_noacc _ _ _ _ _ GPo) in Hna. destruct (kind_none kd); [rewrite in_ivs_cons in Hna; apply orb_false_iff in Hna as [_ Hna]|]; exact Hna.
      * rewrite (gp_lazy _ _ _ _ _ GPo) in Hlz. destruct (kind_lazy kd); [|exact Hlz].
        rewrite page_in_ranges_cons_out in Hlz; [exact Hlz | | rewrite Un; lia].
        pose proof (page_of_byte_out_aligned x (bv_unsigned a) (bv_unsigned a + nZ) Hal ltac:(rewrite Z.add_mod, Hal, HnZal by lia; reflexivity) ltac:(lia)). unfold page_size. rewrite Un. lia.
    +   rewrite (GM2 x) by (rewrite Un; lia).
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
  -   eapply SINV_frame; [|exact Xsinv]. intros x Hx. apply GM1. pose proof (argH_high _ _ Hx). rewrite Un. lia.
  -   rewrite (gp_noacc _ _ _ _ _ GPo), Xhna. unfold RNA. cbn [am_kind am_base am_len].
    destruct kd; cbn [kind_noneb kind_none hreplay]; rewrite ?Hbase, ?HneE; reflexivity.
  -   rewrite (gp_lazy _ _ _ _ _ GPo), Xhlz. unfold RLZ. cbn [am_kind am_base am_len].
    destruct kd; cbn [kind_lazyb kind_lazy hreplay]; rewrite ?Hbase, ?HneE; reflexivity.
  -   intros Ht. rewrite (gp_tid _ _ _ _ _ GPo). exact (Xtidv Ht).
Qed.

Definition null_base (cs : acs) : expr := escale 4096 (EVar (nxt cs)).
Definition null_vlo (cs : acs) (nlo : Z) : Z := grant_vlo A (a_maps cs) nlo.
Definition null_vhi (nlo : Z) : Z := (TOPC - nlo) / 4096.
Definition null_kv (cs : acs) (ne : expr) (nlo : Z) : list kentry :=
  KRange (EVar (nxt cs)) (null_vlo cs nlo) (null_vhi nlo) :: null_kend (null_base cs) ne nlo ++ kn cs.
Definition null_kd (cs : acs) (ne : expr) : list kentry :=
  kdisj_fixed A (kn cs) (null_base cs) ne ++ kdisj_new (a_maps cs) (null_base cs) ne.
Definition null_kfacts (cs : acs) (ne : expr) (nlo : Z) : list kentry :=
  KRange (EVar (nxt cs)) (null_vlo cs nlo) (null_vhi nlo) :: null_kend (null_base cs) ne nlo
  ++ null_kd cs ne ++ flat_map (kdisj_shadow_twin A (null_kv cs ne nlo)) (null_kd cs ne).
Definition null_cs1 (cs : acs) (kd : mkind) (eager : bool) (ne : expr) (nlo nhi : Z) : acs :=
  add_entry cs (sr_upd (s_regs (a_ss cs)) 10 (null_base cs))
    (null_kfacts cs ne nlo ++ kn_grant_filter A (kn cs) (a_maps cs))
    (Datatypes.S (nxt cs)) (AM (null_base cs) ne kd) nhi eager (a_ylo cs).

Lemma mmap_null_eq : forall (split : bool) cs kd (eager visible : bool),
  mmap_null A nx0 LIMIT split cs kd eager visible =
  match mmap_len cs with
  | Some (ne, nlo, nhi) =>
      if (fresh_ok nx0 cs && expr_vars_lt (nxt cs) ne
          && gap_ok A cs nhi && (negb eager || budget_ok LIMIT cs nhi)
          && no_holes (a_maps cs))%bool then
        let v := nxt cs in
        let cs1 := null_cs1 cs kd eager ne nlo nhi in
        let fin (c : acs) := if visible then vis_add A LIMIT c (null_base cs) ne ([KWr (SA (null_base cs) 0) ne; KZero (SA (null_base cs) 0) ne] ++ kn c) else Some c in
        let single := match fin cs1 with Some c => Some (contra_cs c, c) | None => None end in
        if negb (split && visible) then single else
        match first_run (a_maps cs) with
        | Some (lo, hi) =>
            let vtopL := (lo - nlo) / 4096 in
            let vbotH := zcdiv' hi 4096 in
            if (Z.leb vbotH (null_vlo cs nlo) || Z.ltb vtopL (null_vlo cs nlo))%bool then single
            else if Z.ltb (null_vhi nlo) vbotH then
              match fin (set_kn cs1 (KRange (EVar v) (null_vlo cs nlo) vtopL :: kn cs1)) with
              | Some c => Some (contra_cs c, c) | None => None end
            else
              match fin (set_kn cs1 (KRange (EVar v) (null_vlo cs nlo) vtopL :: kn cs1)),
                    fin (set_kn cs1 (KRange (EVar v) vbotH (null_vhi nlo) :: kn cs1)) with
              | Some cL, Some cH => Some (cL, cH)
              | _, _ => None
              end
        | None => single
        end
      else None
  | None => None
  end.
Proof. intros. reflexivity. Qed.

Hypothesis HULL_lt : hull_lt A.

Lemma null_kend_ok : forall E M base ne nlo (a n : word),
  edenot E base = a -> edenot E ne = n ->
  4096 <= bv_unsigned a -> nlo <= bv_unsigned n -> bv_unsigned a + bv_unsigned n <= TOPC ->
  know_ok SEGS E M (null_kend base ne nlo).
Proof.
  intros E M base ne nlo a n Hb Hn Hlo Hnlo HaC. unfold null_kend.
  pose proof (u64_range a) as Ra. pose proof (u64_range n) as Rn. unfold two64 in *.
  destruct ne; try (apply Forall_nil); apply Forall_cons; try apply Forall_nil;
    cbn [kentry_ok]; unfold eadd; rewrite AX2SK.mkAlu_denot; cbn [alu64 alu]; rewrite bv_add_unsigned, Hb, Hn;
    unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64)%Z;
    unfold TOPC in *; rewrite Z.mod_small by lia; lia.
Qed.
Lemma null_kend_pure : forall base ne nlo,
  Forall (fun K => match K with KImg _ _ => False | _ => True end) (null_kend base ne nlo).
Proof. intros. unfold null_kend. destruct ne; repeat constructor. Qed.

Lemma escale_4096_denot : forall E v (a : word),
  ev E v = Z_to_bv 64 (bv_unsigned a / 4096) -> bv_unsigned a mod 4096 = 0 ->
  edenot E (escale 4096 (EVar v)) = a.
Proof.
  intros E v a Hv Hal. unfold escale. rewrite mkMd_denot. cbn [edenot]. rewrite Hv.
  pose proof (u64_range a) as Ra. apply bv_eq. rewrite u_mul64.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  rewrite !u64_lit by lia. rewrite Z.mod_small by lia. lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma grant_hull_apart : forall model (a n : word) nZ,
  vm_reserved (m_vmmaps model) = segments_reserved SEGS ->
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) a n = true ->
  bv_unsigned n = nZ -> 0 < nZ ->
  bv_unsigned a + nZ <= img_lo A \/ img_hi A <= bv_unsigned a.
Proof.
  intros model a n nZ Hres Hrf Un HnZ. pose proof HULL_lt as HL. unfold hull_lt in HL.
  rewrite region_free_app in Hrf. apply andb_prop in Hrf as [Hrf1 _]. rewrite Hres in Hrf1.
  destruct (Z_lt_le_dec (bv_unsigned a) (img_hi A)) as [H1|H1]; [|right; lia].
  destruct (Z_lt_le_dec (img_lo A) (bv_unsigned a + nZ)) as [H2|H2]; [|left; lia].
  exfalso. set (z := Z.max (bv_unsigned a) (img_lo A)).
  pose proof (HULL_tiled z ltac:(unfold z; lia)) as T.
  rewrite (region_free_sem _ a n z Hrf1 ltac:(lia) ltac:(unfold z; lia)) in T. discriminate T.
Qed.

Lemma alloc_top_eq : forall E cs R FULL model,
  CSOK E cs R FULL model -> alloc_top (m_vmmaps model) = uE E e_sp0 - 8388608.
Proof.
  intros E cs R FULL model HC. pose proof (co_isp _ _ _ _ _ _ _ _ _ _ _ HC) as [ISP _].
  unfold alloc_top, stack_max_size. rewrite ISP. reflexivity.
Qed.

Lemma alloc_top_utop : forall E cs R FULL model,
  CSOK E cs R FULL model -> utop E <= alloc_top (m_vmmaps model) < utop E + 4096.
Proof.
  intros E cs R FULL model HC. rewrite (alloc_top_eq E cs R FULL model HC). apply utop_bounds.
Qed.

Lemma le_utop : forall E cs R FULL model z,
  CSOK E cs R FULL model -> z mod 4096 = 0 -> z <= alloc_top (m_vmmaps model) -> z <= utop E.
Proof.
  intros E cs R FULL model z HC Hz Hle. rewrite (alloc_top_eq E cs R FULL model HC) in Hle.
  exact (le_utop_of_aligned E z Hz Hle).
Qed.

Lemma utop_le_TOPC : forall E cs R FULL model, CSOK E cs R FULL model -> utop E <= TOPC.
Proof.
  intros E cs R FULL model HC. pose proof (co_isp _ _ _ _ _ _ _ _ _ _ _ HC) as [_ [ISP _]]. pose proof (utop_bounds E).
  unfold TOPC, sp_window_hi in *. lia.
Qed.

Lemma isp_facts_of : forall E cs R FULL model, CSOK E cs R FULL model -> isp_facts E.
Proof. intros E cs R FULL model HC. exact (proj2 (co_isp _ _ _ _ _ _ _ _ _ _ _ HC)). Qed.

Lemma grant_ok_na_pin_parts : forall model (a : word) nZ,
  grant_ok_na_pin model a nZ = true ->
  bv_unsigned a mod 4096 = 0 /\ 0 < bv_unsigned a /\ bv_unsigned a + nZ <= alloc_top (m_vmmaps model)
  /\ region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) a (Z_to_bv 64 nZ) = true.
Proof.
  intros model a nZ Hg. unfold grant_ok_na_pin in Hg.
  apply andb_prop in Hg as [Hg Hrf]. apply andb_prop in Hg as [Hg Htop]. apply andb_prop in Hg as [Hal Hpos].
  apply Z.eqb_eq in Hal. apply Z.ltb_lt in Hpos. apply Z.leb_le in Htop. unfold page_size in Hal.
  repeat split; assumption.
Qed.

Lemma null_grant_facts : forall E cs R FULL model (a : word) nZ,
  CSOK E cs R FULL model -> grant_ok_na_pin model a nZ = true -> 0 < nZ -> nZ mod 4096 = 0 ->
  bv_unsigned a mod 4096 = 0 /\ 4096 <= bv_unsigned a
  /\ bv_unsigned a + nZ <= utop E /\ utop E <= TOPC /\ bv_unsigned (Z_to_bv 64 nZ) = nZ
  /\ region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) a (Z_to_bv 64 nZ) = true
  /\ (bv_unsigned a + nZ <= img_lo A \/ img_hi A <= bv_unsigned a)
  /\ maps_apart E (a_maps cs) (bv_unsigned a) nZ.
Proof.
  intros E cs R FULL model a nZ HC Hg HnZ HnZal.
  destruct (grant_ok_na_pin_parts model a nZ Hg) as (Hal & Hpos & Htop0 & Hrf).
  assert (Htop : bv_unsigned a + nZ <= utop E).
  { eapply le_utop; [exact HC | rewrite Z.add_mod, Hal, HnZal by lia; reflexivity | exact Htop0]. }
  pose proof (utop_le_TOPC E cs R FULL model HC) as HT.
  pose proof (u64_range a) as Ra.
  assert (Un : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (apply u64_lit; unfold TOPC in *; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (H4096 : 4096 <= bv_unsigned a) by lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  pose proof (grant_hull_apart model a (Z_to_bv 64 nZ) nZ (co_res _ _ _ _ _ _ _ _ _ _ _ HC) Hrf Un HnZ) as Hhull.
  pose proof (maps_apart_of_region_free E (a_maps cs) model a (Z_to_bv 64 nZ) (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) Hrf) as Hap.
  rewrite Un in Hap.
  repeat split; assumption.
Qed.

Lemma u_e_stk_len : forall E, isp_facts E -> uE E e_stk_len = 2 ^ 47 - utop E.
Proof.
  intros E [Hsp Hpg]. pose proof (utop_bounds E) as UB. unfold utop in UB |- *.
  unfold e_stk_len, esub, uE in *. rewrite mkAlu_denot, edenot_lit.
  rewrite u_sub64, u_lit64, Hpg. unfold two64, sp_window_lo, sp_window_hi in *.
  rewrite (Z.mod_small (2 ^ 47 + 8388608)) by lia. rewrite Z.mod_small; lia.
Qed.

Lemma kdisj_new_ok : forall E M ms nb ne (lo n : Z),
  bv_unsigned (edenot E nb) = lo -> bv_unsigned (edenot E ne) = n -> maps_apart E ms lo n -> 0 < n ->
  Forall (kentry_ok SEGS E M) (kdisj_new ms nb ne).
Proof.
  intros E M ms nb ne lo n Hb Hn Hap HnZ. pose proof (u64_range (edenot E nb)) as Rb. rewrite Hb in Rb.
  unfold kdisj_new. apply Forall_app. split.
  - unfold kdisj_merged. apply Forall_flat_map. apply Forall_forall. intros [[rlo rn] k] Hin.
    destruct (Nat.leb 2 k); [|constructor]. constructor; [|constructor].
    pose proof (runs_apart_grant E ms lo n rlo rn k Hap HnZ Hin) as D.
    pose proof (PlaceLemmasK.runs_bounds ms rlo rn k Hin) as (B0 & B1 & B2). unfold two64 in B2.
    cbn [kentry_ok]. unfold estart, elenZ; cbn [a_base a_off]. rewrite !edenot_lit, Hb, Hn.
    rewrite !u64_lit by lia. lia.
  - unfold kdisj_new1. apply Forall_flat_map. apply Forall_forall. intros m Hm.
    destruct (is_fog m) eqn:Hfm; [constructor|]. constructor; [|constructor].
    pose proof (Hap m Hm Hfm) as D.
    cbn [kentry_ok]. unfold estart, elenZ; cbn [a_base a_off]. rewrite Hb, Hn. lia.
Qed.

Lemma kdisj_new_pure : forall ms nb ne,
  Forall (fun K => match K with KImg _ _ => False | _ => True end) (kdisj_new ms nb ne).
Proof.
  intros ms nb ne. unfold kdisj_new, kdisj_merged, kdisj_new1. apply Forall_app. split.
  - apply Forall_flat_map. apply Forall_forall. intros [[lo n] k] _. destruct (Nat.leb 2 k); repeat constructor.
  - apply Forall_flat_map. apply Forall_forall. intros m _. destruct (is_fog m); repeat constructor.
Qed.

Lemma null_kfacts_ok : forall E cs R FULL model ne nlo nhi (a n : word) nZ M',
  CSOK E cs R FULL model ->
  mmap_len cs = Some (ne, nlo, nhi) ->
  ev E (nxt cs) = Z_to_bv 64 (bv_unsigned a / 4096) ->
  edenot E ne = n -> bv_unsigned n = nZ -> nlo <= nZ -> 0 < nZ -> nZ mod 4096 = 0 ->
  grant_ok_na_pin model a nZ = true ->
  know_ok SEGS E M' (null_kfacts cs ne nlo) /\ edenot E (null_base cs) = a
  /\ null_vlo cs nlo <= bv_unsigned a / 4096 <= null_vhi nlo.
Proof.
  intros E cs R FULL model ne nlo nhi a n nZ M' HC HML Hv Hne Un Hnlo HnZ HnZal Hg. pose proof HULL_lt as HL. unfold hull_lt in HL.
  destruct (null_grant_facts E cs R FULL model a nZ HC Hg HnZ HnZal) as (Hal & H4096 & Htop & HT & Un' & Hrf & Hhull & Hap).
  pose proof (u64_range a) as Ra. pose proof (u64_range n) as Rn.
  pose proof (co_isp _ _ _ _ _ _ _ _ _ _ _ HC) as [_ ISP]. pose proof (utop_bounds E) as UB.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK0.
  pose proof HULL_ok' as (HU0 & HU1 & HU2 & HU3).
  assert (Hbase : edenot E (null_base cs) = a) by (unfold null_base; apply escale_4096_denot; assumption).
  assert (VLH : null_vlo cs nlo <= bv_unsigned a / 4096 <= null_vhi nlo).
  { unfold null_vlo, null_vhi. split.
    - eapply (PlaceLemmasK.grant_vlo_sound A (a_maps cs) (bv_unsigned a) nZ nlo HnZ Hnlo H4096 Hal Hhull HU2).
      intros lo n0 k Hin. eapply runs_apart_grant; [exact Hap | exact HnZ | exact Hin].
    - apply Z.div_le_mono; lia. }
  split; [|exact (conj Hbase VLH)].
  assert (KR : forall M, kentry_ok SEGS E M (KRange (EVar (nxt cs)) (null_vlo cs nlo) (null_vhi nlo))).
  { intros M. cbn [kentry_ok edenot]. rewrite Hv.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    rewrite u64_lit by lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    exact VLH. }
  assert (KE : forall M, know_ok SEGS E M (null_kend (null_base cs) ne nlo)).
  { intros M. eapply null_kend_ok; [exact Hbase | exact Hne | exact H4096 | lia | lia]. }
  assert (KD : forall M, Forall (kentry_ok SEGS E M) (null_kd cs ne)).
  { intros M. unfold null_kd. apply Forall_app. split.
    -
      pose proof (u_e_top E ISP) as T. pose proof (u_e_stk_len E ISP) as L. unfold uE in T, L.
      unfold kdisj_fixed. apply Forall_app. split; [|apply Forall_app; split].
      + constructor; [|constructor; [|constructor]]; cbn [kentry_ok]; unfold estart, elenZ; cbn [a_base a_off].
        * rewrite !edenot_lit, !u64_lit by (unfold KHI in *; lia). rewrite Hbase, Hne, Un. lia.
        * rewrite Hbase, Hne, Un. right. unfold uE in UB. lia.
      + apply Forall_flat_map. apply Forall_forall. intros [[b off] len] _.
        destruct (lin_ge0 (kn cs) [(b, off)] [(e_top, 0%Z)]) eqn:G; [|constructor]. constructor; [|constructor].
        pose proof (lin_ge0_sound SEGS E _ (kn cs) _ _ HK0 G) as G'. cbn [xt_den] in G'. rewrite T in G'.
        cbn [kentry_ok]. unfold estart, elenZ; cbn [a_base a_off]. rewrite Hbase, Hne, Un. right. lia.
      + constructor; [|constructor]. cbn [kentry_ok]; unfold estart, elenZ; cbn [a_base a_off]. rewrite T, L, Hbase, Hne, Un.
        right. lia.
    -
      unfold kdisj_new. apply Forall_app. split.
      + unfold kdisj_merged. apply Forall_flat_map. apply Forall_forall. intros [[rlo rn] k] Hin.
        destruct (Nat.leb 2 k); [|constructor]. constructor; [|constructor].
        pose proof (runs_apart_grant E (a_maps cs) (bv_unsigned a) nZ rlo rn k Hap HnZ Hin) as D.
        pose proof (PlaceLemmasK.runs_bounds (a_maps cs) rlo rn k Hin) as (B0 & B1 & B2). unfold two64 in B2.
        cbn [kentry_ok]. unfold estart, elenZ; cbn [a_base a_off]. rewrite !edenot_lit, Hbase, Hne, Un.
        rewrite !u64_lit by lia. lia.
      + unfold kdisj_new1. apply Forall_flat_map. apply Forall_forall. intros m Hm.
        destruct (is_fog m) eqn:Hfm; [constructor|]. constructor; [|constructor].
        pose proof (Hap m Hm Hfm) as D.
        cbn [kentry_ok]. unfold estart, elenZ; cbn [a_base a_off]. rewrite Hbase, Hne, Un. lia. }
  unfold null_kfacts. apply Forall_cons; [exact (KR M')|]. apply Forall_app. split; [exact (KE M')|].
  apply Forall_app. split; [exact (KD M')|].
  apply (kdisj_shadow_twins_ok SEGS A SHADOW_ok' E (MR E cs model FULL)); [|exact (KD _)].

  unfold null_kv. apply Forall_cons; [exact (KR _)|]. apply Forall_app. split; [exact (KE _)|].
  exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC).
Qed.

Lemma kdisj_shadow_twin_pure : forall k K,
  Forall (fun K' => match K' with KImg _ _ => False | _ => True end) (kdisj_shadow_twin A k K).
Proof.
  intros k K. unfold kdisj_shadow_twin.
  destruct K as [| | | | | | |[b1 o1z] n1 [b2 o2z] n2| |]; try constructor.
  destruct o1z; try constructor. destruct o2z; try constructor.
  destruct (split_lit b1) as [c1 o1]. destruct (split_lit b2) as [c2 o2].
  destruct (shadow_of A k b1 n1) as [[sb1 sk1] sn1]. destruct (shadow_of A k b2 n2) as [[sb2 sk2] sn2].
  match goal with |- Forall _ (if ?c then _ else _) => destruct c; [|constructor] end.
  constructor; [exact I | constructor].
Qed.

Lemma null_kd_pure : forall cs ne,
  Forall (fun K => match K with KImg _ _ => False | _ => True end) (null_kd cs ne).
Proof.
  intros cs ne. unfold null_kd, kdisj_fixed, kdisj_new, kdisj_merged, kdisj_new1.
  apply Forall_app. split; [|apply Forall_app; split].
  - apply Forall_app. split; [repeat constructor|]. apply Forall_app. split; [|repeat constructor].
    apply Forall_flat_map. apply Forall_forall. intros [[b off] len] _. destruct (lin_ge0 _ _ _); repeat constructor.
  - apply Forall_flat_map. apply Forall_forall. intros [[lo n] k] _. destruct (Nat.leb 2 k); repeat constructor.
  - apply Forall_flat_map. apply Forall_forall. intros m _. destruct (is_fog m); repeat constructor.
Qed.

Lemma null_kfacts_pure : forall cs ne nlo,
  Forall (fun K => match K with KImg _ _ => False | _ => True end) (null_kfacts cs ne nlo).
Proof.
  intros cs ne nlo. unfold null_kfacts. apply Forall_cons; [exact I|]. apply Forall_app. split; [apply null_kend_pure|].
  apply Forall_app. split; [apply null_kd_pure|].
  apply Forall_flat_map. apply Forall_forall. intros K _. apply kdisj_shadow_twin_pure.
Qed.

Lemma mmap_null_cs1 : forall cs kd (eager : bool) ne nlo nhi E R FULL model (a : word) model' FULL',
  CSOK E cs R FULL model ->
  mmap_len cs = Some (ne, nlo, nhi) ->
  fresh_ok nx0 cs = true -> expr_vars_lt (nxt cs) ne = true ->
  (eager = true -> a_eager cs + a_abytes cs + nhi <= LIMIT) ->
  (kind_none kd || kind_lazy kd = negb eager)%bool -> is_tok_kind kd = false ->
  no_holes (a_maps cs) = true ->
  let len := bv_unsigned (edenot E (reg cs 11)) in
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  grant_ok_na_pin model a nZ = true ->
  grant_post kd a n model model' -> grant_mem kd a n FULL FULL' ->
  let v := nxt cs in
  let E' := ext1 E v (Z_to_bv 64 (bv_unsigned a / 4096)) in
  let cs1 := null_cs1 cs kd eager ne nlo nhi in
  CSOK E' cs1 (regupd R (Z_to_bv 5 (Z.of_nat 10)) a) FULL' model'
  /\ edenot E' (null_base cs) = a /\ edenot E' ne = n /\ bv_unsigned n = nZ
  /\ env_agree nx0 E E' /\ env_agree (nxt cs) E E'
  /\ ev E' v = Z_to_bv 64 (bv_unsigned a / 4096)
  /\ (bv_unsigned a mod 4096 = 0 /\ 4096 <= bv_unsigned a /\ bv_unsigned a + nZ <= utop E' /\ utop E' <= TOPC
      /\ nlo <= nZ <= nhi /\ 0 < nZ /\ nZ mod 4096 = 0 /\ null_vlo cs nlo <= bv_unsigned a / 4096 <= null_vhi nlo)
  /\ maps_apart E' (a_maps cs) (bv_unsigned a) nZ
  /\ (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + nZ ->
        in_ivs (bv_unsigned x) (vm_maps (m_vmmaps model')) = true
        /\ in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)) = false
        /\ argH E' x = false /\ in_hull A (bv_unsigned x) = false /\ (utop E' <=? bv_unsigned x) = false).
Proof.
  intros cs kd eager ne nlo nhi E R FULL model a model' FULL' HC HML Hfresh Hnev Hbudget Hkind Hkfog Hnoh len nZ n Hg GPo GM v E' cs1.
  assert (Hnoholes : Forall (fun m => is_hole m = false) (a_maps cs)).
  { unfold no_holes in Hnoh. apply Forall_forall. intros m Hm. pose proof (proj1 (forallb_forall _ _) Hnoh m Hm) as X. apply negb_true_iff in X. exact X. }

  destruct (mmap_len_sound E cs R FULL model ne nlo nhi HC HML) as (R11 & Hlen & Hne & Hnlo & HnZ & HnZal & HneE).
  fold len in R11, Hlen, Hne, HnZ, HnZal. fold nZ in Hne, HnZ, HnZal.
  pose proof (page_round_up_Z_bounds len ltac:(lia)) as PB. fold nZ in PB. unfold page_size in PB.
  assert (HnZpos : 0 < nZ) by lia.
  pose proof (u64_range a) as Ra.
  pose proof HULL_ok' as (HU0 & HU1 & HU2 & HU3).

  pose proof (ext1_agree'' E v (Z_to_bv 64 (bv_unsigned a / 4096))) as Hag. fold E' in Hag.
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fvis & Fbrk & Ffd & Fle). fold v in Fsr, Fkn, Fmaps, Fvis, Fbrk, Ffd, Fle.
  assert (HC' : CSOK E' cs R FULL model) by (eapply cs_ok_agree'; [exact Hag | exact Hfresh | exact HC]).
  assert (Hag0 : env_agree nx0 E E') by (eapply env_agree_le'; [exact Hag | exact Fle]).
  assert (Hv : ev E' v = Z_to_bv 64 (bv_unsigned a / 4096)) by apply ext1_at.
  assert (HneE' : edenot E' ne = n).
  { rewrite (HneE E'); [exact Hne|]. symmetry. eapply edenot_agree'; [exact Hag|]. unfold reg. apply nth_sr_vars_lt'; [exact Fsr | lia]. }

  destruct (null_grant_facts E' cs R FULL model a nZ HC' Hg HnZpos HnZal) as (Hal & H4096 & HaT & HT & Un & Hrf & Himg_a & Hapart).
  fold n in Un, Hrf.
  destruct (null_kfacts_ok E' cs R FULL model ne nlo nhi a n nZ (MR E' cs model' FULL') HC' HML Hv HneE' Un ltac:(lia) HnZpos HnZal Hg) as (KNEW & Hbase & VLH).
  pose proof (grant_new_facts E' cs R FULL model a n nZ HC' Hrf Un HnZpos Himg_a HaT) as NEW.

  destruct (grant_cs1_ok E' cs R FULL model kd a n nZ model' FULL'
              (sr_upd (s_regs (a_ss cs)) 10 (null_base cs)) (regupd R (Z_to_bv 5 (Z.of_nat 10)) a)
              (null_kfacts cs ne nlo) (null_base cs) ne nhi eager (a_ylo cs) (Datatypes.S v)
              HC' Un HnZpos HnZal Hal Himg_a HaT Hrf GPo GM) as (HC1 & MROUT & MRSAME).
  - apply regs_ok_set_n'; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC') | lia | exact Hbase].
  - exact Hbase.
  - exact HneE'.
  - exact KNEW.
  - exact Hkind.
  - exact Hkfog.
  - lia.
  - exact Hbudget.
  - lia.
  - intros m Hm Hk. exfalso. pose proof (proj1 (Forall_forall _ _) Hnoholes m Hm) as X. congruence.
  - split; [exact HC1|]. split; [exact Hbase|]. split; [exact HneE'|]. split; [exact Un|]. split; [exact Hag0|]. split; [exact Hag|].
    split; [exact Hv|]. split; [destruct VLH; repeat split; lia|]. split; [exact Hapart|].
    intros x Hx. destruct (NEW x Hx) as (N0 & N1 & N2 & N3 & N4 & _).
    split; [|auto]. rewrite (gp_maps _ _ _ _ _ GPo), in_ivs_cons. cbn [fst snd]. rewrite Un.
    apply orb_true_iff. left. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma null_first_run : forall E ms lo n flo fhi,
  maps_apart E ms lo n -> 0 < n -> first_run ms = Some (flo, fhi) -> lo + n <= flo \/ fhi <= lo.
Proof.
  intros E ms lo n flo fhi Hap Hn Hfr.
  destruct (PlaceLemmasK.first_run_In ms flo fhi Hfr) as (rn & k & -> & Hin).
  eapply runs_apart_grant; eassumption.
Qed.

Lemma null_low_fact : forall E v (a : word) nZ nlo lo vlo M,
  ev E v = Z_to_bv 64 (bv_unsigned a / 4096) -> vlo <= bv_unsigned a / 4096 ->
  bv_unsigned a + nZ <= lo -> nlo <= nZ ->
  kentry_ok SEGS E M (KRange (EVar v) vlo ((lo - nlo) / 4096)).
Proof.
  intros E v a nZ nlo lo vlo M Hv Hvlo Hlo Hnlo. pose proof (u64_range a) as Ra.
  cbn [kentry_ok edenot]. rewrite Hv.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  rewrite u64_lit by lia. split; [exact Hvlo|]. apply Z.div_le_mono; lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma null_high_fact : forall E v (a : word) hi vhi M,
  ev E v = Z_to_bv 64 (bv_unsigned a / 4096) -> bv_unsigned a / 4096 <= vhi ->
  hi <= bv_unsigned a -> bv_unsigned a mod 4096 = 0 ->
  kentry_ok SEGS E M (KRange (EVar v) (zcdiv' hi 4096) vhi).
Proof.
  intros E v a hi vhi M Hv Hvhi Hhi Hal. pose proof (u64_range a) as Ra.
  cbn [kentry_ok edenot]. rewrite Hv. unfold zcdiv'.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  rewrite u64_lit by lia. split; [|exact Hvhi]. lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma null_child_ok : forall E cs1 R FULL model K,
  CSOK E cs1 R FULL model -> (forall M, kentry_ok SEGS E M K) ->
  CSOK E (set_kn cs1 (K :: kn cs1)) R FULL model.
Proof.
  intros E cs1 R FULL model K HC HK. apply cs_ok_set_kn; [exact HC|].
  constructor; [apply HK | exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC)].
Qed.

Lemma null_high_vbot : forall (a hi : Z), hi <= a -> a mod 4096 = 0 -> zcdiv' hi 4096 <= a / 4096.
Proof.
  intros a hi Hhi Hal. unfold zcdiv'.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
Lemma null_low_vtop : forall (a nZ nlo lo : Z), a + nZ <= lo -> nlo <= nZ -> 0 <= a -> a / 4096 <= (lo - nlo) / 4096.
Proof. intros a nZ nlo lo H1 H2 H3. apply Z.div_le_mono; lia. Qed.

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
  -
    eapply (kmem_ok E _ base ne (bv_unsigned a) nZ); [unfold estart; cbn [a_base a_off]; rewrite Hbase; lia | unfold elenZ; rewrite Hne; exact Un | lia | lia | lia |].
    intros x Hx. destruct (NEW x Hx) as (N1 & N2 & N3).
    unfold Mr, mrestrict, hid. rewrite N3. cbn [orb].
    unfold vis. rewrite N1, N2. cbn [negb andb].
    assert (Hal : in_allow A E cs2 (bv_unsigned x) = true).
    { unfold in_allow, in_vis. rewrite Ecs2. cbn [a_vis existsb fst snd]. unfold uE. rewrite Hbase, Hne, Un.
      rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
    rewrite Hal. rewrite !orb_true_r. cbn [negb]. apply ZERO. exact Hx.
  -
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC1) as HK1. unfold Mr in HK1 |- *.
    eapply know_ok_unhide'; [apply H_off_segments_cs' | exact Hkh | | | exact HK1].
    + intros y Hy. rewrite Ecs2 in Hy. eapply hid_cons_sub. exact Hy.
    + intros y Hy. apply hid_hull'. exact Hy.
Qed.

Lemma gap_weight_eq : forall nZ l, gap_weight nZ l = sum_sizes l + Z.of_nat (length l) * (nZ + 4095).
Proof. induction l as [|[b sz] l IH]; cbn -[Z.of_nat Z.add Z.mul]; [lia|]. rewrite IH. rewrite Nat2Z.inj_succ. cbn [snd]. lia. Qed.

Lemma gap_ok_sound : forall E cs R FULL model nhi nZ,
  CSOK E cs R FULL model -> gap_ok A cs nhi = true -> 0 <= nZ <= nhi ->
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
  pose proof (alloc_top_eq E cs R FULL model HC) as AT. pose proof (co_isp _ _ _ _ _ _ _ _ _ _ _ HC) as [_ [ISP _]].
  exists (Z_to_bv 64 g). unfold grant_ok_na_pin. rewrite u64_lit by lia.
  rewrite Hfree. unfold page_size in Hal |- *.
  rewrite (proj2 (Z.eqb_eq _ _) Hal). rewrite (proj2 (Z.ltb_lt 0 g)) by lia.
  rewrite (proj2 (Z.leb_le _ _)); [reflexivity|]. rewrite AT. unfold sp_window_lo in *. lia.
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

Lemma refuse_cont : forall cs E R FULL model TA,
  CSOK E cs R FULL model -> 0 <= pc cs -> pc cs + 4 < 2 ^ 64 ->
  (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' (refuse cs) R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS scfg (cfg R' (pc (refuse cs)) FULL' model') TA) ->
  srealizes SEGS scfg (mkCfg (mkst (regupd R 10 (errno_ret ENOMEM)) (v_addi (Z_to_bv 64 (pc cs)) 4) FULL (seg_rom SEGS)) model) TA.
Proof.
  intros cs E R FULL model TA HC Hp0 Hp4 HKA.
  specialize (HKA E (regupd R (Z_to_bv 5 (Z.of_nat 10)) (errno_ret ENOMEM)) FULL model
                  (conj (env_agree_refl' _ _) (env_agree_refl' _ _)) (refuse_ok E cs R FULL model HC) eq_refl).
  unfold cfg_of in HKA. rewrite refuse_pc, <- bv5_10 in HKA. rewrite (v_addi_pc (pc cs) Hp0 Hp4). exact HKA.
Qed.

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

Lemma fixed_args_sound : forall E cs R FULL model top b off ne nlo nhi,
  CSOK E cs R FULL model -> fixed_args A cs top = Some (b, off, ne, nlo, nhi) ->
  split_lit (reg cs 10) = (b, off) /\ mmap_len cs = Some (ne, nlo, nhi)
  /\ bv_unsigned (edenot E (reg cs 10)) mod 4096 = 0
  /\ 0 < bv_unsigned (edenot E (reg cs 10))
  /\ (bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) <= img_lo A \/ img_hi A <= bv_unsigned (edenot E (reg cs 10)))
  /\ bv_unsigned (edenot E (reg cs 10)) + nhi <= top
  /\ getr R (Z_to_bv 5 (Z.of_nat 10)) = edenot E (reg cs 10)
  /\ flat_x (kn cs) b off ne = true.
Proof.
  intros E cs R FULL model top b off ne nlo nhi HC H. unfold fixed_args in H. pose proof HULL_lt as HL. unfold hull_lt in HL.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK. pose proof HULL_ok' as (HU0 & HU1 & HU2 & HU3).
  destruct (split_lit (reg cs 10)) as [b0 off0] eqn:Hsp.
  destruct (mmap_len cs) as [[[ne0 nlo0] nhi0]|] eqn:HML; [|discriminate].
  destruct (xlo (kn cs) (reg cs 10)) as [alo|] eqn:Hxl; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [ahi|] eqn:Hxh; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  apply andb_prop in Hc as [Hc Hflat].
  injection H as -> -> -> -> ->.
  apply andb_prop in Hc as [Hc Htop]. apply andb_prop in Hc as [Hc Himg]. apply andb_prop in Hc as [Hpa Hpos].
  apply Z.ltb_lt in Hpos. apply Z.leb_le in Htop.
  pose proof (xlo_sound SEGS E _ (kn cs) _ alo HK Hxl). pose proof (xhi_sound SEGS E _ (kn cs) _ ahi HK Hxh).
  assert (Hhull : bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) <= img_lo A \/ img_hi A <= bv_unsigned (edenot E (reg cs 10))).
  { apply orb_prop in Himg as [Himg|Hoff].
    - apply Z.leb_le in Himg. right. lia.
    - unfold off_image_x in Hoff. pose proof (ranges_apart_x_sound SEGS E _ (kn cs) b off ne (ELit 0) (img_lo A) (ELit (img_hi A - img_lo A)) HK Hoff) as D.
      destruct (APSK.flat_x_sound SEGS E _ (kn cs) b off ne HK Hflat) as (F1 & F2 & F3).
      pose proof (APSK.u_of_split E (reg cs 10) b off Hsp ltac:(lia)) as U.
      unfold estart, elenZ in D. cbn [a_base a_off] in D. rewrite !edenot_lit in D. rewrite !u64_lit in D by (unfold KHI in *; lia).
      unfold estart in U. cbn [a_base a_off] in U. lia. }
  repeat split; try lia.
  - eapply page_aligned_sound; [exact HK | exact Hpa].
  - apply (reg_sound' E cs R FULL model); [exact HC | lia].
  - exact Hflat.
Qed.

Lemma split_flat_estart : forall E M k e b off n,
  know_ok SEGS E M k -> split_lit e = (b, off) -> flat_x k b off n = true ->
  estart E (SA b off) = bv_unsigned (edenot E e)
  /\ estart E (SA b off) + bv_unsigned (edenot E n) <= 2 ^ 64 /\ 0 < bv_unsigned (edenot E n).
Proof.
  intros E M k e b off n HK Hsp Hfl.
  destruct (APSK.flat_x_sound SEGS E M k b off n HK Hfl) as (F1 & F2 & F3).
  pose proof (APSK.u_of_split E e b off Hsp ltac:(lia)). repeat split; lia.
Qed.

Lemma region_free_of_apart : forall E cs R FULL model b off ne (lo n : word),
  CSOK E cs R FULL model -> no_fog (a_maps cs) = true ->
  forallb (fun m => ranges_apart_x (kn cs) b off ne (am_base m) 0 (am_len m)) (a_maps cs) = true ->
  estart E (SA b off) = bv_unsigned lo -> elenZ E ne = bv_unsigned n ->
  (bv_unsigned lo + bv_unsigned n <= img_lo A \/ img_hi A <= bv_unsigned lo) ->
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) lo n = true.
Proof.
  intros E cs R FULL model b off ne lo n HC Hnf Hall Hs Hn Himg.
  rewrite region_free_app. apply andb_true_intro. split.
  - apply reserved_free_hull_apart; [exact (co_res _ _ _ _ _ _ _ _ _ _ _ HC) | exact Himg].
  - rewrite (proj1 (maps_match_exact' E _ _ Hnf) (co_maps _ _ _ _ _ _ _ _ _ _ _ HC)). apply RefNodes.region_free_intro. intros bm sm Hin.
    apply in_map_iff in Hin as (m & Hm & Hinm). unfold amap_den in Hm. injection Hm as <- <-.
    pose proof (proj1 (forallb_forall _ _) Hall m Hinm) as Hap.
    pose proof (ranges_apart_x_sound SEGS E _ (kn cs) b off ne (am_base m) 0 (am_len m) (co_know _ _ _ _ _ _ _ _ _ _ _ HC) Hap) as D.
    unfold estart in D at 2 3. cbn [a_base a_off] in D. unfold elenZ in D, Hn. rewrite Hs, Hn in D. lia.
Qed.

Definition fixed_cs1 (cs : acs) (kd : mkind) (eager : bool) (ne : expr) (nhi : Z) : acs :=
  let k := kn cs in
  let m := AM (reg cs 10) ne kd in
  let ksh := if mkind_eqb kd KRWLAZY then flat_map (fun p => shadow_facts A k [m] (fst p) (snd p)) (a_vis cs) else [] in
  add_entry cs (s_regs (a_ss cs)) (ksh ++ kn_grant_filter A k (a_maps cs)) (nxt cs) m nhi eager (a_ylo cs).

Lemma shadow_facts_new_ok : forall E cs R FULL model (a n : word) nZ ne model' FULL',
  CSOK E cs R FULL model ->
  bv_unsigned n = nZ -> edenot E ne = n -> bv_unsigned a + nZ <= CEIL -> edenot E (reg cs 10) = a ->
  grant_post KRWLAZY a n model model' -> grant_mem KRWLAZY a n FULL FULL' ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + nZ ->
     in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)) = false /\ argH E x = false) ->
  know_ok SEGS E (MR E cs model' FULL')
    (flat_map (fun p => shadow_facts A (kn cs) [AM (reg cs 10) ne KRWLAZY] (fst p) (snd p)) (a_vis cs)).
Proof.
  intros E cs R FULL model a n nZ ne model' FULL' HC Un Hne HaC Hra GPo [GM1 GM2] NEW.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (u64_range a) as Ra. pose proof SHADOW_ok' as SO.
  unfold know_ok. apply Forall_flat_map. apply Forall_forall. intros p Hp.
  unfold shadow_facts.
  destruct (shadow_of A (kn cs) (fst p) (snd p)) as [[sb sk] sn] eqn:Hsh.
  match goal with |- Forall _ (if ?c then _ else _) => destruct c eqn:Hjust; [|constructor] end.
  unfold shadow_of in Hsh.
  destruct (split_lit (eadd (mkSrl (kn cs) (fst p) 3) (ELit (shadow_off A)))) as [sb' sk'] eqn:Hss. injection Hsh as -> -> <-.

  destruct (APSK.shadow_facts_holder SEGS A HS XN XE XB SHADOW_ok 0%nat E _ (kn cs) [AM (reg cs 10) ne KRWLAZY] (fst p) (snd p) sb sk HK Hss Hjust)
    as (_ & m & Hmin & _ & _ & I1 & I2).
  destruct Hmin as [<-|[]]. cbn [am_base am_len] in I1, I2. rewrite Hne, Un in I2. rewrite Hra in I1, I2.
  pose proof HaC as HaC'. unfold CEIL in HaC'.

  assert (Usn : bv_unsigned (edenot E (mkSrl (kn cs) (snd p) 3)) = bv_unsigned (edenot E (snd p)) / 8).
  { rewrite (mkSrl_denot SEGS E _ (kn cs) (snd p) 3 (Z_to_bv 64 3) HK) by (rewrite u64_lit by lia; reflexivity).
    rewrite u_srl64. rewrite u64_lit by lia. reflexivity. }
  rewrite Usn in I2.
  set (S0 := bv_unsigned (edenot E sb) + sk) in *.
  pose proof (u64_range (edenot E (fst p))) as Rb. pose proof (u64_range (edenot E (snd p))) as Rn.
  pose proof (u64_range (edenot E (mkSrl (kn cs) (snd p) 3))) as Rsn.
  assert (HS0 : S0 = shadow_off A + bv_unsigned (edenot E (fst p)) / 8).
  { pose proof (APSK.split_lit_denot E _ sb sk Hss) as D. unfold eadd in D. rewrite mkAlu_denot in D. cbn [edenot] in D.
    apply (f_equal bv_unsigned) in D. rewrite u_add64 in D.
    rewrite (mkSrl_denot SEGS E _ (kn cs) (fst p) 3 (Z_to_bv 64 3) HK) in D by (rewrite u64_lit by lia; reflexivity).
    rewrite u_srl64 in D. fold S0 in D.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    rewrite !u64_lit in D by (unfold CEIL in *; lia).
    change (2 ^ (3 mod 64)) with 8 in D.
    rewrite (Z.mod_small (bv_unsigned (edenot E (fst p)) / 8 + shadow_off A)) in D by (unfold CEIL in *; lia).
    unfold CEIL in *. lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }

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

Lemma fixed_pre : forall cs top b off ne nlo nhi E R FULL model,
  CSOK E cs R FULL model ->
  fixed_args A cs top = Some (b, off, ne, nlo, nhi) -> top <= CEIL ->
  let addr := edenot E (reg cs 10) in
  let len := bv_unsigned (edenot E (reg cs 11)) in
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  edenot E ne = n /\ bv_unsigned n = nZ /\ estart E (SA b off) = bv_unsigned addr
  /\ bv_unsigned addr mod 4096 = 0 /\ 0 < bv_unsigned addr /\ (bv_unsigned addr + nZ <= img_lo A \/ img_hi A <= bv_unsigned addr)
  /\ bv_unsigned addr + nZ <= top
  /\ getr R (Z_to_bv 5 (Z.of_nat 10)) = addr /\ nZ mod 4096 = 0 /\ 0 < nZ <= nhi.
Proof.
  intros cs top b off ne nlo nhi E R FULL model HC HFA Htop addr len nZ n.
  destruct (fixed_args_sound E cs R FULL model top b off ne nlo nhi HC HFA) as (Hsp & HML & Hal & Hpos & Himg & HtopA & R10 & Hflat).
  fold addr in Hal, Hpos, Himg, HtopA, R10.
  destruct (mmap_len_sound E cs R FULL model ne nlo nhi HC HML) as (R11 & Hlen & Hne & Hnlo & HnZ & HnZal & HneE).
  fold len in R11, Hlen, Hne, HnZ, HnZal. fold nZ in Hne, HnZ, HnZal. fold n in Hne.
  pose proof (page_round_up_Z_bounds len ltac:(lia)) as PB. fold nZ in PB. unfold page_size in PB.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  destruct (split_flat_estart E _ (kn cs) (reg cs 10) b off ne HK Hsp Hflat) as (Hest & Hfl2 & Hfl3). fold addr in Hest.
  pose proof (u64_range addr) as Ra.
  assert (Un0 : bv_unsigned n = nZ).
  { subst n. apply u64_lit. split; [lia|]. pose proof (u64_range (Z_to_bv 64 nZ)) as Rn. unfold CEIL in Htop. lia. }
  split; [exact Hne|]. split; [exact Un0|]. split; [exact Hest|]. split; [exact Hal|]. split; [exact Hpos|].
  split; [rewrite Hne, Un0 in Himg; exact Himg|]. split; [lia|]. split; [exact R10|]. split; [exact HnZal | lia].
Qed.

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

Lemma same_val_sound : forall E M k a b,
  know_ok SEGS E M k -> same_val k a b = true -> bv_unsigned (edenot E a) = bv_unsigned (edenot E b).
Proof.
  intros E M k a b HK H. unfold same_val in H.
  destruct (expr_eqb a b) eqn:He; [apply expr_eqb_eq in He; subst; reflexivity|].
  destruct (lin_ge0 k [(a, 0)] [(b, 0)]) eqn:H1; [|discriminate].
  pose proof (lin_ge0_sound SEGS E M k _ _ HK H1) as X1. pose proof (lin_ge0_sound SEGS E M k _ _ HK H) as X2.
  cbn [xt_den] in X1, X2. lia.
Qed.

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

Lemma cs_ok_unhole : forall E cs R FULL model h,
  CSOK E cs R FULL model -> CSOK E (with_maps0 cs (unhole (a_maps cs) h)) R FULL model.
Proof.
  intros E cs R FULL model h HC.
  assert (ELEM : forall m, In m (unhole (a_maps cs) h) ->
            In m (a_maps cs) \/ exists m0, In m0 (a_maps cs) /\ m = AM (am_base m0) (am_len m0) KFOG).
  { intros m Hm. unfold unhole in Hm. apply in_map_iff in Hm as (m0 & Hm0 & Hin).
    destruct (is_hole m0 && amap_eqb m0 h)%bool; [right; exists m0; split; [exact Hin | symmetry; exact Hm0] | left; subst; exact Hin]. }
  destruct HC as [Xregs Xlog Xknow Xhalt Xfds Xfs Xtid Xres Xlimit Xmaps Xholes Xseps Xwf Xbounds Xlazyb Xnasub Xnone Xkinds Xtotsz Xisp Xbrk Xsbrk Xeager Xabytes Xminv Xzero Xsinv Xhna Xhlz Xtidv].
  constructor; unfold with_maps0 in *;
    cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_hna a_hlz kn] in *; try assumption.
  -   apply (proj1 (maps_match_unhole E _ h _)). exact Xmaps.
  -   apply Forall_forall. intros m Hm Hk. destruct (ELEM m Hm) as [Hin|(m0 & Hin & ->)];
      [exact (proj1 (Forall_forall _ _) Xholes m Hin Hk) | cbn in Hk; discriminate].
  -   apply Forall_forall. intros m Hm Hk. destruct (ELEM m Hm) as [Hin|(m0 & Hin & ->)];
      [exact (proj1 (Forall_forall _ _) Xnone m Hin Hk) | cbn in Hk; destruct Hk; discriminate].
  -   apply Forall_forall. intros m Hm Hk. destruct (ELEM m Hm) as [Hin|(m0 & Hin & ->)];
      [exact (proj1 (Forall_forall _ _) Xkinds m Hin Hk) | cbn in Hk; discriminate].
Qed.

Lemma CEIL_le_utop : forall E cs R FULL model, CSOK E cs R FULL model -> CEIL <= utop E.
Proof.
  intros E cs R FULL model HC. pose proof (co_isp _ _ _ _ _ _ _ _ _ _ _ HC) as [_ [ISP _]].
  pose proof (utop_bounds E) as UB. pose proof (utop_mod E) as UM.
  pose proof (Z.div_mod (utop E) 4096 ltac:(lia)) as Du. rewrite UM in Du.
  unfold CEIL, sp_window_lo in *. lia.
Qed.

Lemma mmap_fixed_grant_cs1 : forall cs ms0 kd (eager : bool) top b off ne nlo nhi E R FULL model model' FULL',
  CSOK E cs R FULL model ->
  fixed_args A cs top = Some (b, off, ne, nlo, nhi) -> top <= CEIL ->
  CSOK E (with_maps0 cs ms0) R FULL model ->
  let addr := edenot E (reg cs 10) in
  let len := bv_unsigned (edenot E (reg cs 11)) in
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
  (forall m, In m ms0 -> is_hole m = true ->
     bv_unsigned addr + nZ <= uE E (am_base m) \/ uE E (am_base m) + uE E (am_len m) <= bv_unsigned addr) ->
  (eager = true -> a_eager cs + a_abytes cs + nhi <= LIMIT) ->
  (kind_none kd || kind_lazy kd = negb eager)%bool -> is_tok_kind kd = false ->
  grant_post kd addr n model model' -> grant_mem kd addr n FULL FULL' ->
  CSOK E (fixed_cs1 (with_maps0 cs ms0) kd eager ne nhi) (regupd R (Z_to_bv 5 (Z.of_nat 10)) addr) FULL' model'
  /\ (forall x : word, bv_unsigned addr <= bv_unsigned x < bv_unsigned addr + nZ ->
        in_ivs (bv_unsigned x) (vm_maps (m_vmmaps model')) = true
        /\ in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)) = false /\ argH E x = false).
Proof.
  intros cs ms0 kd eager top b off ne nlo nhi E R FULL model model' FULL' HC HFA Htop HC0 addr len nZ n Hrf Hholes Hbudget Hkind Hkfog GPo GM.
  destruct (fixed_pre cs top b off ne nlo nhi E R FULL model HC HFA Htop) as (Hne & Un & Hest & Hal & Hpos & Himg & HtopA & R10 & HnZal & HnZ).
  fold addr len nZ n in Hne, Un, Hest, Hal, Hpos, Himg, HtopA, R10, HnZal, HnZ.
  assert (HaC : bv_unsigned addr + nZ <= CEIL) by lia.
  pose proof (CEIL_le_utop E cs R FULL model HC) as CU.
  assert (HaT : bv_unsigned addr + nZ <= utop E) by lia.
  assert (HnZpos : 0 < nZ) by lia.
  pose proof Himg as Himg_a.
  pose proof (grant_new_facts E cs R FULL model addr n nZ HC Hrf Un HnZpos Himg_a HaT) as NEW.
  destruct (grant_cs1_ok E (with_maps0 cs ms0) R FULL model kd addr n nZ model' FULL'
              (s_regs (a_ss cs)) (regupd R (Z_to_bv 5 (Z.of_nat 10)) addr)
              (if mkind_eqb kd KRWLAZY then flat_map (fun p => shadow_facts A (kn cs) [AM (reg cs 10) ne kd] (fst p) (snd p)) (a_vis cs) else [])
              (reg cs 10) ne nhi eager (a_ylo cs) (nxt cs)
              HC0 Un HnZpos HnZal Hal Himg_a HaT Hrf GPo GM) as (HC1 & MROUT & MRSAME).
  - apply regs_ok_regupd_same; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) | lia | exact R10].
  - reflexivity.
  - exact Hne.
  - destruct kd; cbn [mkind_eqb]; try constructor.
    change (MR E (with_maps0 cs ms0) model' FULL') with (MR E cs model' FULL').
    eapply shadow_facts_new_ok; [exact HC | exact Un | exact Hne | exact HaC | reflexivity | exact GPo | exact GM |].
    intros x Hx. destruct (NEW x Hx) as (_ & N1 & N2 & _). auto.
  - exact Hkind.
  - exact Hkfog.
  - lia.
  - exact Hbudget.
  - cbn [with_maps0 a_ylo]. lia.
  - cbn [with_maps0 a_maps]. exact Hholes.
  - split; [exact HC1|].
    intros x Hx. destruct (NEW x Hx) as (N0 & N1 & N2 & _). split; [|auto].
    rewrite (gp_maps _ _ _ _ _ GPo), in_ivs_cons. cbn [fst snd]. rewrite Un.
    apply orb_true_iff. left. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma mmap_fixed_old_facts : forall cs b off ne nlo nhi E R FULL model,
  CSOK E cs R FULL model ->
  fixed_args A cs CEIL = Some (b, off, ne, nlo, nhi) ->
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
  destruct (fixed_pre cs CEIL b off ne nlo nhi E R FULL model HC HFA ltac:(lia)) as (Hne & Un & Hest & Hal & Hpos & Himg & HtopA & R10 & HnZal & HnZ).
  fold addr nZ in Hne, Un, Hest, Hal, Hpos, Himg, HtopA, R10, HnZal, HnZ.
  split; [|split].
  - destruct cs; exact HC.
  - eapply region_free_of_apart; [exact HC | exact Hnf | exact Hall | exact Hest | unfold elenZ; rewrite Hne; reflexivity | rewrite Un; exact Himg].
  - intros m Hm Hk. exfalso. unfold no_fog in Hnf. pose proof (proj1 (forallb_forall _ _) Hnf m Hm) as X.
    apply negb_true_iff in X. unfold is_fog, is_hole in *. destruct (am_kind m); cbn in X, Hk; congruence.
Qed.

Lemma mmap_fixed_hole_facts : forall cs b off ne nlo nhi h E R FULL model,
  CSOK E cs R FULL model ->
  fixed_args A cs CEIL = Some (b, off, ne, nlo, nhi) ->
  find_hole (kn cs) (a_maps cs) (reg cs 10) ne = Some h ->
  forallb (fun m => negb (is_hole m) || ranges_apart_x (kn cs) b off ne (am_base m) 0 (am_len m)) (unhole (a_maps cs) h) = true ->
  let addr := edenot E (reg cs 10) in
  let nZ := page_round_up_Z (bv_unsigned (edenot E (reg cs 11))) in
  CSOK E (with_maps0 cs (unhole (a_maps cs) h)) R FULL model
  /\ region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr (Z_to_bv 64 nZ) = true
  /\ (forall m, In m (unhole (a_maps cs) h) -> is_hole m = true ->
        bv_unsigned addr + nZ <= uE E (am_base m) \/ uE E (am_base m) + uE E (am_len m) <= bv_unsigned addr).
Proof.
  intros cs b off ne nlo nhi h E R FULL model HC HFA Hfh Hap addr nZ.
  destruct (fixed_pre cs CEIL b off ne nlo nhi E R FULL model HC HFA ltac:(lia)) as (Hne & Un & Hest & Hal & Hpos & Himg & HtopA & R10 & HnZal & HnZ).
  fold addr nZ in Hne, Un, Hest, Hal, Hpos, Himg, HtopA, R10, HnZal, HnZ.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  destruct (find_hole_sound E _ (kn cs) (a_maps cs) (reg cs 10) ne h HK Hfh) as (Hin & Hh & Hhb & Hhn).
  fold addr in Hhb. rewrite Hne, Un in Hhn.
  destruct (proj1 (Forall_forall _ _) (co_holes _ _ _ _ _ _ _ _ _ _ _ HC) h Hin Hh) as [F1 F2].
  rewrite Hhb, Hhn in F1, F2.
  split; [apply cs_ok_unhole; exact HC|]. split.
  - apply RefNodes.region_free_intro. intros b' s' Hin'. rewrite Un. destruct (F1 (b', s') Hin'); cbn [fst snd] in *; lia.
  - intros m Hm Hk. pose proof (proj1 (forallb_forall _ _) Hap m Hm) as X. cbn beta in X. rewrite Hk in X. cbn [negb orb] in X.
    pose proof (ranges_apart_x_sound SEGS E _ (kn cs) b off ne (am_base m) 0 (am_len m) HK X) as D.
    unfold estart in D at 2 3. cbn [a_base a_off] in D. unfold elenZ in D. rewrite Hest, Hne, Un in D. unfold uE. lia.
Qed.

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
  - left. apply APSK.amap_eqb_eq in He. subst m0. auto.
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
  sp_isp : vm_init_sp (m_vmmaps model') = vm_init_sp (m_vmmaps model)    }.

Definition slice_mem (s : slarm) (addr n : word) (FULL FULL' : word -> option byte) : Prop :=
  (forall x : word, bv_unsigned x < bv_unsigned addr \/ bv_unsigned addr + bv_unsigned n <= bv_unsigned x -> FULL' x = FULL x)
  /\ (forall x : word, bv_unsigned addr <= bv_unsigned x < bv_unsigned addr + bv_unsigned n ->
        FULL' x = if sl_nn s then None else Some (Z_to_bv 8 0)).

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

  Lemma sl_bounds : 0 < bv_unsigned (edenot E (am_len m)) /\ bv_unsigned (edenot E (am_base m)) mod 4096 = 0
                    /\ bv_unsigned (edenot E (am_len m)) mod 4096 = 0
                    /\ (bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= img_lo A
                        \/ img_hi A <= bv_unsigned (edenot E (am_base m)))
                    /\ bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= utop E.
  Proof.
    pose proof (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) as B.
    exact (proj1 (Forall_forall _ _) B (amap_den E m) (maps_match_In E _ _ m (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) Hm Hnf)).
  Qed.

  Lemma sl_lohi : (hi <= img_lo A \/ img_hi A <= lo) /\ hi <= utop E /\ lo < hi /\ hi <= 2 ^ 64 /\ lo mod 4096 = 0 /\ hi mod 4096 = 0.
  Proof.
    pose proof sl_bounds as (B1 & B2 & B3 & B4 & B5). pose proof (utop_le_TOPC _ _ _ _ _ HC) as UT. subst lo hi. unfold TOPC in *.
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

  Lemma sl_vis_out : forall cs1 (x : word), a_vis cs1 = a_vis cs -> (bv_unsigned x < lo \/ hi <= bv_unsigned x) ->
    VIS E cs1 model' x = VIS E cs model x.
  Proof.
    intros cs1 x Hv Hx. unfold vis. rewrite (sp_maps _ _ _ _ _ SPo), (sl_noacc_out x Hx), (sl_lazy_out x Hx), (in_allow_ext E cs cs1 Hv). reflexivity.
  Qed.

  Lemma sl_MR_out : forall cs1 (x : word), a_vis cs1 = a_vis cs -> (bv_unsigned x < lo \/ hi <= bv_unsigned x) ->
    MR E cs1 model' FULL' x = MR E cs model FULL x.
  Proof.
    intros cs1 x Hv Hx. unfold Mr, mrestrict, hid. rewrite (sl_vis_out cs1 x Hv Hx). rewrite (proj1 SM x) by (subst lo hi; rewrite Un; exact Hx). reflexivity.
  Qed.

  Lemma sl_vis_in_E : s = SlE -> forall cs1 (x : word), lo <= bv_unsigned x < hi -> VIS E cs1 model' x = true.
  Proof.
    intros Hs cs1 x Hx. unfold vis. rewrite (sp_maps _ _ _ _ _ SPo), (sl_in_maps x Hx), (sl_noacc_in x Hx), (sl_lazy_in x Hx). subst s.
    cbn. rewrite !orb_true_r. reflexivity.
  Qed.

  Lemma sl_vis_in_G : s = SlG -> forall cs1 (x : word), lo <= bv_unsigned x < hi -> argH E x = false -> VIS E cs1 model' x = false.
  Proof.
    intros Hs cs1 x Hx Ha. pose proof sl_lohi as (L1 & L2 & L3 & L4 & L5 & L6). unfold vis.
    rewrite (sp_maps _ _ _ _ _ SPo), (sl_in_maps x Hx), (sl_noacc_in x Hx). subst s. cbn [sl_nn negb andb].
    replace (in_hull A (bv_unsigned x)) with false by (symmetry; unfold in_hull; apply andb_false_iff; destruct L1; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
    replace (utop E <=? bv_unsigned x) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  Qed.

  Lemma sl_vis_in_F : s = SlF -> forall cs1 (x : word), a_vis cs1 = a_vis cs -> lo <= bv_unsigned x < hi -> VIS E cs1 model' x = VIS E cs model x.
  Proof.
    intros Hs cs1 x Hv Hx. unfold vis.
    rewrite (sp_maps _ _ _ _ _ SPo), (sl_in_maps x Hx), (sl_noacc_in x Hx), (sl_lazy_in x Hx), (in_allow_ext E cs cs1 Hv).
    destruct (proj1 (Forall_forall _ _) (co_kinds _ _ _ _ _ _ _ _ _ _ _ HC) m Hm (HF Hs) x ltac:(subst lo hi; lia)) as [K1 K2].
    rewrite K1, K2. subst s. reflexivity.
  Qed.

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

  Definition sl_hna (ae ne : expr) : list hop := (if sl_nn s then [HCons ae ne] else []) ++ HSub ae ne :: a_hna cs.
  Definition sl_hlz (ae ne : expr) : list hop :=
    match s with SlM => a_hlz cs | SlF => HCons ae ne :: HSub ae ne :: a_hlz cs | _ => HSub ae ne :: a_hlz cs end.

  Lemma slice_cs1_ok : forall sr' R' k' p nx nhi (ae ne : expr),
    regs_ok E sr' R' ->
    know_ok SEGS E (MR E cs model' FULL') k' ->
    nZ <= nhi ->
    (sl_charge s = true -> a_eager cs + a_abytes cs + nhi <= LIMIT) ->
    edenot E ae = addr -> edenot E ne = n ->
    CSOK E (ACS (mk_ss p sr' k' nx)
                (match s with SlF => a_maps cs | _ => rekind (a_maps cs) m end)
                (a_totsz cs) (a_ylo cs)
                (if sl_charge s then a_eager cs + nhi else a_eager cs)
                (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) (sl_hna ae ne) (sl_hlz ae ne)) R' FULL' model'.
  Proof.
    intros sr' R' k' p nx nhi ae ne Hregs Hknow Hnhi Hbudget Hae HneX.
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

    assert (NONE : forall m', In m' (a_maps cs) -> m <> m' -> (am_kind m' = KNONE \/ am_kind m' = KNONELAZY) ->
              In (amap_den E m') (vm_noaccess (m_vmmaps model'))).
    { intros m' Hm' Hne Hk. rewrite (sp_noacc _ _ _ _ _ SPo). apply in_app_iff. right.
      assert (Hnf' : is_fog m' = false) by (apply KNF; tauto).
      pose proof (proj1 (Forall_forall _ _) (co_none _ _ _ _ _ _ _ _ _ _ _ HC) m' Hm' Hk) as X.
      pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) (amap_den E m')
                    (maps_match_In E _ _ m' MM Hm' Hnf')) as (Bm1 & _).
      unfold amap_den in *. apply maps_subtract_keeps; [rewrite Un; lia | exact Bm1 | exact X |].
      cbn [fst snd]. rewrite Un. pose proof (DISJ' m' Hm' Hnf' Hne). unfold lo, hi in *. lia. }

    assert (KINDS : forall m', In m' (a_maps cs) -> am_kind m' = KRWLAZY ->
              forall x : word, bv_unsigned (edenot E (am_base m')) <= bv_unsigned x < bv_unsigned (edenot E (am_base m')) + bv_unsigned (edenot E (am_len m')) ->
                in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model')) = false
                /\ page_in_ranges (page_base x) (m_vm_lazy model') = true).
    { intros m' Hm' Hk x Hx.
      destruct (proj1 (Forall_forall _ _) (co_kinds _ _ _ _ _ _ _ _ _ _ _ HC) m' Hm' Hk x Hx) as [K1 K2].
      destruct (Z_lt_le_dec (bv_unsigned x) lo) as [Hlt|Hge]; [|destruct (Z_lt_le_dec (bv_unsigned x) hi) as [Hlt2|Hge2]].
      - rewrite sl_noacc_out, sl_lazy_out by lia. auto.
      -
        assert (Hmm : m = m').
        { destruct (amap_eqb m m') eqn:He; [apply APSK.amap_eqb_eq in He; exact He|]. exfalso.
          assert (Hne : m <> m') by (intros ->; rewrite amap_eqb_refl in He; discriminate).
          pose proof (DISJ' m' Hm' ltac:(apply KNF; tauto) Hne). lia. }
        subst m'. rewrite sl_noacc_in, sl_lazy_in by lia.
        destruct s0; rewrite <- Es; cbn [sl_nn]; auto; exfalso; refine (HnF _ Hk); rewrite <- Es; discriminate.
      - rewrite sl_noacc_out, sl_lazy_out by lia. auto. }
    match goal with |- CSOK _ ?c _ _ _ => set (cs1 := c) end.
    assert (HIDOUT : forall x : word, bv_unsigned x < lo \/ hi <= bv_unsigned x -> HID E cs1 model' x = HID E cs model x).
    { intros x Hx. unfold hid. rewrite (sl_vis_out cs1 x eq_refl Hx). reflexivity. }
    assert (HALLOW : ALLOW E cs1 = ALLOW E cs) by reflexivity.
    destruct HC as [Xregs Xlog Xknow Xhalt Xfds Xfs Xtid Xres Xlimit Xmaps Xholes Xseps Xwf Xbounds Xlazyb Xnasub Xnone Xkinds Xtotsz Xisp Xbrk Xsbrk Xeager Xabytes Xminv Xzero Xsinv Xhna Xhlz Xtidv].
    constructor; rewrite ?HALLOW; unfold cs1; cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_hna a_hlz kn s_regs s_log s_know s_next mk_ss]; fold cs1.
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
        apply APSK.amap_eqb_eq in He. subst m0. cbn [am_base am_len]. split; [reflexivity|]. split; [reflexivity|]. rewrite Hnf. reflexivity. }
      destruct s0; rewrite <- Es; first [exact RK | exact Xmaps].
    -
      rewrite (sp_maps _ _ _ _ _ SPo), (sp_res _ _ _ _ _ SPo).
      assert (RKH : Forall (hole_ok E (a_ylo cs) (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))) (rekind (a_maps cs) m)).
      { unfold rekind. apply Forall_forall. intros m0 HinR Hh. apply in_map_iff in HinR as (m1 & <- & HinR1).
        destruct (amap_eqb m1 m) eqn:He.
        - exfalso. unfold is_hole in Hh. cbn [am_kind] in Hh. discriminate.
        - exact (proj1 (Forall_forall _ _) Xholes m1 HinR1 Hh). }
      destruct s0; rewrite <- Es; first [exact RKH | exact Xholes].
    - rewrite (sp_maps _ _ _ _ _ SPo). exact Xseps.
    - exact Hwf'.
    - rewrite (sp_maps _ _ _ _ _ SPo). exact Xbounds.
    -   rewrite (sp_lazy _ _ _ _ _ SPo).
      assert (SUB : Forall (fun iv : word * word => (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_lo A \/ img_hi A <= bv_unsigned (fst iv))
                                               /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= utop E)
                      (maps_subtract (m_vm_lazy model) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))).
      { apply Forall_forall. intros q Hq. destruct (maps_subtract_pieces _ _ _ q W3 Hq) as (r & Hr & R1 & R2 & _).
        pose proof (proj1 (Forall_forall _ _) Xlazyb r Hr) as [Y1 Y2]. lia. }
      destruct s0; rewrite <- Es; try exact SUB; try exact Xlazyb. apply Forall_cons; [cbn [fst snd]; unfold lo, hi in *; lia | exact SUB].
    -   intros z Hz. rewrite (sp_maps _ _ _ _ _ SPo). rewrite (sp_noacc _ _ _ _ _ SPo), in_ivs_app in Hz.
      apply orb_prop in Hz as [Hz|Hz].
      + destruct (sl_nn s); [|discriminate]. rewrite in_ivs_cons in Hz. cbn [fst snd in_ivs existsb] in Hz. rewrite orb_false_r in Hz.
        apply andb_prop in Hz as [Z1 Z2]. apply Z.leb_le in Z1. apply Z.ltb_lt in Z2.
        eapply in_ivs_maps_match; [exact Xmaps | exact Hm | exact Hnf |]. unfold lo, hi in *. lia.
      + apply Xnasub. rewrite in_ivs_covered in Hz |- *. rewrite covered_maps_subtract in Hz by (try exact W2; rewrite Un; lia).
        apply andb_prop in Hz as [Hz _]. exact Hz.
    -   apply Forall_forall. intros m' Hm' Hk'. destruct s0; rewrite <- Es in Hm'.
      2: { apply NONE; [exact Hm' | | exact Hk']. intros <-. rewrite (HF (eq_sym Es)) in Hk'. destruct Hk'; discriminate. }
      all: destruct (in_rekind _ _ _ Hm') as (m0 & Hm0 & [[-> ->]|[Hne ->]]); [cbn in Hk'; destruct Hk'; discriminate|];
           apply NONE; [exact Hm0 | congruence | exact Hk'].
    -   apply Forall_forall. intros m' Hm' Hk'. destruct s0; rewrite <- Es in Hm'.
      2: { apply KINDS; assumption. }
      all: destruct (in_rekind _ _ _ Hm') as (m0 & Hm0 & [[-> ->]|[Hne ->]]); [cbn in Hk'; discriminate|];
           apply KINDS; assumption.
    - rewrite (sp_res _ _ _ _ _ SPo), (sp_maps _ _ _ _ _ SPo). exact Xtotsz.
    -   rewrite (sp_isp _ _ _ _ _ SPo). exact Xisp.
    - rewrite (sp_brk _ _ _ _ _ SPo). exact Xbrk.
    - rewrite (sp_brk _ _ _ _ _ SPo), (sp_sbrk _ _ _ _ _ SPo). exact Xsbrk.
    -   destruct (sl_charge s); lia.
    - exact Xabytes.
    -   destruct Xminv as [N1 N2 N3 N4 N5].
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
      + left. reflexivity.
    -   intros x Hh Hmx Hna Hlz Hgh.
      destruct (Z_lt_le_dec (bv_unsigned x) lo) as [Hlt|Hge]; [|destruct (Z_lt_le_dec (bv_unsigned x) hi) as [Hlt2|Hge2]].
      + rewrite (proj1 SM x) by (unfold lo in *; lia). rewrite HIDOUT in Hh by lia. rewrite (sp_maps _ _ _ _ _ SPo) in Hmx.
        rewrite sl_noacc_out in Hna by lia. rewrite sl_lazy_out in Hlz by lia. exact (Xzero x Hh Hmx Hna Hlz Hgh).
      + rewrite sl_noacc_in in Hna by lia. rewrite (proj2 SM x) by (unfold lo, hi in *; rewrite Un; lia). rewrite Hna. reflexivity.
      + rewrite (proj1 SM x) by (unfold hi in *; rewrite Un; lia). rewrite HIDOUT in Hh by lia. rewrite (sp_maps _ _ _ _ _ SPo) in Hmx.
        rewrite sl_noacc_out in Hna by lia. rewrite sl_lazy_out in Hlz by lia. exact (Xzero x Hh Hmx Hna Hlz Hgh).
    -   eapply SINV_frame; [|exact Xsinv]. intros x Hx. apply (proj1 SM). pose proof (argH_high _ _ Hx). pose proof (utop_bounds E). unfold hi in *. rewrite Un. lia.
    -   rewrite (sp_noacc _ _ _ _ _ SPo), Xhna. unfold sl_hna, RNA.
      destruct s0; rewrite <- Es; cbn [sl_nn app hreplay]; unfold APSK.uE; rewrite Hae, HneX; reflexivity.
    -   rewrite (sp_lazy _ _ _ _ _ SPo), Xhlz. unfold sl_hlz, RLZ.
      destruct s0; rewrite <- Es; cbn [hreplay]; unfold APSK.uE; rewrite ?Hae, ?HneX; reflexivity.
    -   intros Ht. rewrite (sp_tid _ _ _ _ _ SPo). exact (Xtidv Ht).
  Qed.

End Slice.

Lemma kn_unfill_clip_ok : forall E M M' k b off ne,
  know_ok SEGS E M k ->
  (estart E (SA b off) + elenZ E ne <= img_lo A \/ img_hi A <= estart E (SA b off)) ->
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
  - rewrite APSK.kentry_apart_bp_eq in Hap. eapply kentry_apart_b_sem'; [exact HK | exact Hap].
Qed.

Lemma kn_rezero_ok_gen : forall E M M' k b off ne,
  know_ok SEGS E M k ->
  (estart E (SA b off) + elenZ E ne <= img_lo A \/ img_hi A <= estart E (SA b off)) ->
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
    try (rewrite APSK.kentry_apart_bp_eq in Hkeep; eapply kentry_keep_sem'; [exact HKK | eapply kentry_apart_b_sem'; [exact HK | exact Hkeep] | exact Hout]).
  -   cbn [kentry_ok] in HKK |- *. destruct HKK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. apply ZERO. apply Hz. exact Hi.
  -   eapply kentry_keep_sem'; [exact HKK | | exact Hout]. unfold kfoot_apart, kfoot. lia.
  - exact HKK.
  - exact HKK.
  -   cbn [kentry_ok] in HKK |- *. destruct HKK as [Hfl Hs]. split; [exact Hfl|]. intros d mm Hd Hdm. eapply store_ok_mono; [exact DEF | apply Hs; assumption].
  - exact HKK.
  -   cbn [kentry_ok] in HKK |- *. destruct HKK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. apply DEF. apply Hz. exact Hi.
Qed.

Lemma kn_rezero_clip_ok : forall E M M' k b off ne,
  know_ok SEGS E M k ->
  (estart E (SA b off) + elenZ E ne <= img_lo A \/ img_hi A <= estart E (SA b off)) ->
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
  (estart E (SA b off) + elenZ E ne <= img_lo A \/ img_hi A <= estart E (SA b off)) ->
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

Lemma vis_add_slice_ok : forall E cs1 cs2 (ea : expr) b off ne R FULL' model' (lo nZ : Z),
  CSOK E cs1 R FULL' model' ->
  vis_add A LIMIT cs1 ea ne (KWr (SA b off) ne :: KZero (SA b off) ne :: kn cs1) = Some cs2 ->
  kimg_in_hull A (kn cs1) ->
  uE E ea = lo -> estart E (SA b off) = lo -> elenZ E ne = nZ -> 0 <= lo -> 0 < nZ -> lo + nZ <= TOPC ->
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
  assert (Hfl : flat E (SA b off) (elenZ E ne)) by (unfold flat; rewrite Hest, Hne; unfold TOPC in Hhi; lia).
  constructor; [|constructor].
  - cbn [kentry_ok]. split; [exact Hfl|]. rewrite Hest, Hne. intros d w' Hd Hdw. destruct w' as [|w'']; [reflexivity|].
    apply store_ok_of_all; [rewrite u64_lit by (unfold TOPC in Hhi; lia); unfold TOPC in Hhi; lia|].
    intros x Hx. rewrite u64_lit in Hx by (unfold TOPC in Hhi; lia). unfold wview. rewrite (BYTE x) by lia. discriminate.
  - cbn [kentry_ok]. split; [exact Hfl|]. rewrite Hest, Hne. intros i Hi. apply BYTE. rewrite u64_lit by (unfold TOPC in Hhi; lia). lia.
  - pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC1) as HK1. unfold Mr in HK1 |- *.
    eapply know_ok_unhide'; [apply H_off_segments_cs' | exact Hkh | | | exact HK1].
    + intros y Hy. rewrite Ecs2 in Hy. eapply hid_cons_sub. exact Hy.
    + intros y Hy. apply hid_hull'. exact Hy.
Qed.

Lemma find_containing_sound : forall E M k ms kinds b off ne m,
  know_ok SEGS E M k -> find_containing k ms kinds b off ne = Some m ->
  In m ms /\ (In (am_kind m) kinds /\ is_fog m = false)
  /\ bv_unsigned (edenot E (am_base m)) <= estart E (SA b off)
  /\ estart E (SA b off) + elenZ E ne <= bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)).
Proof.
  intros E M k ms kinds b off ne m HK Hf. unfold find_containing in Hf. apply find_some in Hf as [Hin Hb].
  apply andb_prop in Hb as [Hk Hins]. apply andb_prop in Hk as [Hnf Hk]. apply negb_true_iff in Hnf.
  apply existsb_exists in Hk as (k0 & Hk0 & Hkk). apply APSK.mkind_eqb_eq in Hkk. subst k0.
  pose proof (xinside_sound SEGS E M k b off ne (am_base m) 0 (am_len m) HK Hins) as [I1 I2].
  unfold estart in I1, I2 |- *. cbn [a_base a_off] in *. unfold elenZ in *. repeat split; try assumption; lia.
Qed.

Lemma slice_args : forall E cs R FULL model b off ne nlo nhi kinds m,
  CSOK E cs R FULL model ->
  fixed_args A cs TOPC = Some (b, off, ne, nlo, nhi) ->
  find_containing (kn cs) (a_maps cs) kinds b off ne = Some m ->
  let addr := edenot E (reg cs 10) in
  let len := bv_unsigned (edenot E (reg cs 11)) in
  let nZ := page_round_up_Z len in
  let n := Z_to_bv 64 nZ in
  In m (a_maps cs) /\ (In (am_kind m) kinds /\ is_fog m = false)
  /\ getr R (Z_to_bv 5 (Z.of_nat 10)) = addr /\ getr R (Z_to_bv 5 (Z.of_nat 11)) = Z_to_bv 64 len /\ 0 < len < 2 ^ 64
  /\ edenot E ne = n /\ bv_unsigned n = nZ /\ 0 < nZ /\ nZ <= nhi /\ nZ mod 4096 = 0
  /\ bv_unsigned addr mod 4096 = 0 /\ 0 < bv_unsigned addr /\ (bv_unsigned addr + nZ <= img_lo A \/ img_hi A <= bv_unsigned addr)
  /\ estart E (SA b off) = bv_unsigned addr
  /\ bv_unsigned (edenot E (am_base m)) <= bv_unsigned addr
  /\ bv_unsigned addr + nZ <= bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m))
  /\ bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= utop E
  /\ map_contains (vm_maps (m_vmmaps model)) addr n = true
  /\ region_free (vm_reserved (m_vmmaps model)) addr n = true
  /\ overlap_sum (vm_maps (m_vmmaps model)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) <= nZ.
Proof.
  intros E cs R FULL model b off ne nlo nhi kinds m HC HFA Hf addr len nZ n.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  destruct (fixed_args_sound E cs R FULL model TOPC b off ne nlo nhi HC HFA) as (Hsp & HML & Hal & Hpos & Himg & Htop & R10 & _).
  destruct (mmap_len_sound E cs R FULL model ne nlo nhi HC HML) as (R11 & Hlen & Hne & Hnlo & HnZ & HnZal & _).
  fold addr in Hal, Hpos, Himg, Htop, R10. fold len in R11, Hlen, Hne, HnZ, HnZal. fold nZ in Hne, HnZ, HnZal. fold n in Hne.
  destruct (find_containing_sound E _ (kn cs) (a_maps cs) kinds b off ne m HK Hf) as (Hm & [Hkind Hnf] & I1 & I2).
  pose proof (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) as HB.
  pose proof (maps_match_In E _ _ m (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) Hm Hnf) as HIN.
  pose proof (proj1 (Forall_forall _ _) HB (amap_den E m) HIN) as (B1 & B2 & B3 & B4 & B5). cbn [amap_den fst snd] in B1, B2, B3, B4, B5.
  pose proof (u64_range (edenot E (am_base m))) as Rb. pose proof (utop_le_TOPC _ _ _ _ _ HC) as UT.
  assert (Hest : bv_unsigned addr = estart E (SA b off)).
  { unfold addr. apply (APSK.u_of_split E (reg cs 10) b off Hsp). unfold elenZ in I2. pose proof (u64_range (edenot E ne)). unfold TOPC in UT. lia. }
  unfold elenZ in I2. rewrite Hne in I2.
  pose proof (page_round_up_Z_bounds len ltac:(lia)) as PB. fold nZ in PB. unfold page_size in PB.
  assert (Un : bv_unsigned n = nZ).
  { unfold n. apply u64_lit. pose proof (u64_range (Z_to_bv 64 nZ)). fold n in H. unfold TOPC in *. lia. }
  rewrite Un in I2. rewrite Hne, Un in Himg.
  assert (Hmc : map_contains (vm_maps (m_vmmaps model)) addr n = true).
  { eapply map_contains_intro; [exact HIN | lia | rewrite Un; lia]. }
  split; [exact Hm|]. split; [split; [exact Hkind | exact Hnf]|].
  repeat (split; [first [assumption | lia | symmetry; assumption] |]).
  split; [apply reserved_free_hull_apart; [exact (co_res _ _ _ _ _ _ _ _ _ _ _ HC) | rewrite Un; exact Himg] |].
  rewrite Un. pose proof (overlap_sum_contained (vm_maps (m_vmmaps model)) (edenot E (am_base m)) (edenot E (am_len m)) (bv_unsigned addr) (bv_unsigned addr + nZ)
    (co_seps _ _ _ _ _ _ _ _ _ _ _ HC) HIN ltac:(lia) ltac:(lia) ltac:(lia)). lia.
Qed.

End Nodes.
