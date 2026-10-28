(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import MM_syscalls WStr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase AKit AKit2 ABytes AModelFacts ARep ARepKit ARepFrame ALayout AHeapP ARefill_iface RT_stubs
     F_apoison F_acache F_aalloc3 F_ammap F_aensure F_apopulate F_agetfrom F_arefill.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition newslots (nd : Z) (n : nat) : list Z := rev (map (fun j => nd + Z.of_nat j) (seq 0 n)).

Lemma newslots_length : forall nd n, length (newslots nd n) = n.
Proof. intros. unfold newslots. rewrite length_rev, length_map, length_seq. reflexivity. Qed.

Lemma newslots_In : forall nd n k, In k (newslots nd n) <-> nd <= k < nd + Z.of_nat n.
Proof.
  intros nd n k. unfold newslots. rewrite <- in_rev, in_map_iff. split.
  - intros (j & <- & Hj). apply in_seq in Hj. lia.
  - intros Hk. exists (Z.to_nat (k - nd)). split; [lia|]. apply in_seq. lia.
Qed.

Lemma newslots_NoDup : forall nd n, List.NoDup (newslots nd n).
Proof.
  intros nd n. unfold newslots. apply NoDup_rev. apply NoDup_map_NoDup_ForallPairs; [| apply seq_NoDup].
  intros a b _ _ E. lia.
Qed.

Lemma map_cw_newslots : forall c nd n, 1 <= c < K_NUM_CLASSES ->
  map (fun k => Z_to_bv 64 (acompact c k)) (newslots nd n) = fvals (nd * size_of_class c) (size_of_class c) n.
Proof.
  intros c nd n Hc. pose proof (size_of_class_facts c Hc) as [S1 S3].
  unfold newslots, fvals. rewrite map_rev, map_map. f_equal. apply map_ext. intros j.
  f_equal. unfold acompact. rewrite Z.shiftr_div_pow2 by lia. change (2^4) with 16.
  generalize S1 S3; clear; intros. Z.div_mod_to_equations. nia.
Qed.

Lemma NoDup_bound_length : forall (l : list Z) n, List.NoDup l -> (forall k, In k l -> 0 <= k < n) -> 0 <= n -> Z.of_nat (length l) <= n.
Proof.
  intros l n ND B N.
  assert (INCL : incl (map Z.to_nat l) (seq 0 (Z.to_nat n))).
  { intros x Hx. apply in_map_iff in Hx. destruct Hx as (k & <- & Hk). apply in_seq. specialize (B k Hk). lia. }
  apply NoDup_incl_length in INCL.
  - rewrite length_map, length_seq in INCL. lia.
  - apply NoDup_map_NoDup_ForallPairs; [| exact ND]. intros a b Ha Hb E. pose proof (B a Ha). pose proof (B b Hb). lia.
Qed.

Lemma nodup_app : forall {A} (a b : list A), List.NoDup a -> List.NoDup b -> (forall x, In x a -> ~ In x b) -> List.NoDup (a ++ b).
Proof.
  intros A a b NA NB D. induction a as [|x a IH]; cbn; [exact NB|].
  inversion NA; subst. constructor.
  - rewrite in_app_iff. intros [Hx|Hx]; [exact (H1 Hx)|]. exact (D x (or_introl eq_refl) Hx).
  - apply IH; [exact H2|]. intros y Hy. apply D. right; exact Hy.
Qed.

Lemma junk_sub : forall m A n A' n', junk_at m A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' -> junk_at m A' n'.
Proof.
  intros m A n A' n' J H1 H2 H3.
  destruct (junk_split m A (A' - A) (n - (A' - A)) ltac:(replace (A' - A + (n - (A' - A))) with n by lia; exact J) ltac:(lia) ltac:(lia)) as [_ J2].
  replace (A + (A' - A)) with A' in J2 by lia.
  destruct (junk_split m A' n' (n - (A' - A) - n') ltac:(replace (n' + (n - (A' - A) - n')) with (n - (A' - A)) by lia; exact J2) ltac:(lia) ltac:(lia)) as [J3 _].
  exact J3.
Qed.

Lemma fill_sub : forall m A n A' n' v, fill_at m A n v -> A <= A' -> A' + n' <= A + n -> 0 <= n' -> fill_at m A' n' v.
Proof.
  intros m A n A' n' v F H1 H2 H3. unfold fill_at in *.
  pose proof (rw_cells_split_CB bsegs m A [] (Z.to_nat n) (repeat (Z_to_bv 8 v) (Z.to_nat n)) [] [Z.to_nat (A' - A); Z.to_nat n'; Z.to_nat (n - (A' - A) - n')] F ltac:(cbn; lia)) as SP.
  cbn [app mk_CB_cells] in SP.
  rewrite !skipn_repeat' in SP. rewrite (firstn_repeat' _ (Z.to_nat n')) in SP by lia.
  apply (proj1 (rw_cells_app bsegs m A [_] [_; _])) in SP. destruct SP as [_ SP].
  apply (proj1 (rw_cells_app bsegs m _ [_] [_])) in SP. destruct SP as [SP _].
  cbn [cells_size csize Nat.add] in SP. rewrite Nat.add_0_r, Z2Nat.id in SP by lia.
  replace (A + (A' - A)) with A' in SP by lia. exact SP.
Qed.

Lemma fill_merge : forall m A a b v, fill_at m A a v -> fill_at m (A + a) b v -> 0 <= a -> 0 <= b -> fill_at m A (a + b) v.
Proof.
  intros m A a b v F1 F2 Ha Hb. unfold fill_at in *.
  pose proof (cb_app m A _ _ _ _ F1 ltac:(rewrite Z2Nat.id by lia; exact F2)) as CA.
  rewrite <- repeat_app in CA. replace (Z.to_nat a + Z.to_nat b)%nat with (Z.to_nat (a + b)) in CA by lia. exact CA.
Qed.

Lemma junk_of_u32arr : forall m A ws, u32arr bsegs m A ws -> junk_at m A (4 * Z.of_nat (length ws)).
Proof.
  intros m A ws AR. exists (u32s ws). apply rw_cells_of_u8arr' || idtac.
  pose proof (rw_cells_of_u8arr bsegs m A (u32s ws) (u8arr_of_u32arr bsegs m A ws AR)) as R.
  rewrite u32s_length in R. replace (Z.to_nat (4 * Z.of_nat (length ws))) with (4 * length ws)%nat by lia. exact R.
Qed.

Lemma junk_of_fill : forall m A n v, fill_at m A n v -> junk_at m A n.
Proof. intros m A n v F. eexists. exact F. Qed.

(* [comment removed for export] *)
Lemma u32arr_firstn : forall m A ws k, u32arr bsegs m A ws -> (k <= length ws)%nat -> u32arr bsegs m A (firstn k ws).
Proof.
  intros m A ws k [[B0 [B1 B]] [W0 [W1 W]]] K. rewrite u32s_length in B1. split.
  - split; [lia|]. split; [rewrite u32s_length, length_firstn; lia|].
    intros i Hi. rewrite u32s_length, length_firstn in Hi.
    rewrite <- (firstn_skipn k ws) in B. specialize (B i ltac:(rewrite u32s_length, length_app, length_firstn, length_skipn; lia)).
    rewrite u32s_app, nth_error_app1 in B by (rewrite u32s_length, length_firstn; lia). exact B.
  - split; [lia|]. split; [rewrite length_firstn; lia|]. intros i Hi. rewrite length_firstn in Hi. apply W. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xr (X : aconc) (c : Z) (fr ca : list Z) : aconc :=
  mkAConc (fun c' => if c' =? c then mkXClass fr ca else x_cls X c') (x_busy X).

Lemma busy_of_In_slots : forall X c k b, busy_of X c k = Some b -> In k (busy_slots X c).
Proof.
  intros X c k b Hb. destruct (busy_of_Some_facts X c k b Hb) as (HIn & HC & HK).
  unfold busy_slots. apply in_map_iff. exists b. split; [exact HK|]. apply filter_In. split; [exact HIn|]. apply Z.eqb_eq. exact HC.
Qed.

Lemma xr_busy_of : forall X c fr ca c' k, busy_of (xr X c fr ca) c' k = busy_of X c' k.
Proof. intros. reflexivity. Qed.
Lemma xr_busy_slots : forall X c fr ca c', busy_slots (xr X c fr ca) c' = busy_slots X c'.
Proof. intros. reflexivity. Qed.
Lemma xr_cls_eq : forall X c fr ca, x_cls (xr X c fr ca) c = mkXClass fr ca.
Proof. intros. unfold xr. cbn. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma xr_cls_ne : forall X c fr ca c', c' <> c -> x_cls (xr X c fr ca) c' = x_cls X c'.
Proof. intros X c fr ca c' NE. unfold xr. cbn. replace (c' =? c) with false by (symmetry; apply Z.eqb_neq; exact NE). reflexivity. Qed.


(* [comment removed for export] *)
Lemma alayout_res_disj : forall L, alayout_ok L ->
     (al_ctx L + 65536 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L)
  /\ (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L).
Proof.
  intros L H. pose proof (ad_ctx_res L H) as D1. pose proof (ad_t_res L H) as D2. pose proof (ao_space L H) as SB.
  pose proof (ao_ctx L H) as C. pose proof (ao_t L H) as T.
  unfold adisj, aobj, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472. lia.
Qed.

Lemma region_other_geo : forall L c c', alayout_ok L -> 1 <= c < 32 -> 1 <= c' < 32 -> c' <> c ->
  al_space_beg L <= aregion L c' /\ (aregion L c' + 4294967296 <= aregion L c \/ aregion L c + 4294967296 <= aregion L c') /\ aregion L c' + 4294967296 <= al_space_beg L + 137438953472
  /\ afreearr L c' = aregion L c' + 3758096384 /\ aregion_info L c' = al_space_beg L + 137438953472 + c' * 128 /\ acache_addr L c' = al_t L + 208 + c' * 80
  /\ aregion L c' mod 8 = 0 /\ (shad (aregion L c') + shlen 4294967296 <= shad (aregion L c) \/ shad (aregion L c + 4294967296) <= shad (aregion L c'))
  /\ 2201439137792 <= shad (aregion L c') /\ shad (aregion L c') + shlen 4294967296 <= 17594333495296
  /\ shad (afreearr L c') = shad (aregion L c') + shlen 3758096384.
Proof.
  intros L c c' ALO HC Hc' NE.
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *. change (2^37) with 137438953472 in *.
  unfold afreearr, aregion_info, acache_addr, aregion, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, ARI_STRIDE.
  change (2^32) with 4294967296. change (2^37) with 137438953472.
  assert (Q : exists q, al_space_beg L = 65536 * q) by (exists (al_space_beg L / 65536); Z.div_mod_to_equations; lia).
  destruct Q as [q Hq]. rewrite Hq in *.
  rewrite !shad_div, !shlen_div. unfold ASHOFF.
  replace ((65536 * q + c' * 4294967296) / 8) with (8192 * q + c' * 536870912) by (Z.div_mod_to_equations; lia).
  replace ((65536 * q + c * 4294967296) / 8) with (8192 * q + c * 536870912) by (Z.div_mod_to_equations; lia).
  replace ((65536 * q + c * 4294967296 + 4294967296) / 8) with (8192 * q + c * 536870912 + 536870912) by (Z.div_mod_to_equations; lia).
  replace ((65536 * q + c' * 4294967296 + 3758096384) / 8) with (8192 * q + c' * 536870912 + 469762048) by (Z.div_mod_to_equations; lia).
  change (4294967296 / 8) with 536870912. change (3758096384 / 8) with 469762048.
  assert (CC : c' + 1 <= c \/ c + 1 <= c') by lia.
  repeat split; lia.
Qed.

Section RefillP.
Variable H : aholes.
Hypothesis HL : ahole_laws H.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition store_refill_stmt : Prop :=
  forall (L : alayout) (RNG RNG' : footprint) (sp : word) (m m' : amem) (st st2 : astate) (X : aconc) (c lo : Z) (chunks0 : list word),
  alayout_ok L -> arng L RNG st -> AREP H L st X m ->
  1 <= c < K_NUM_CLASSES -> c_count (get_cls st c) = 0 ->
  ATOP <= lo -> lo <= bv_unsigned sp - AREFILL_STACK ->
  u32arr bsegs m (acache_addr L c + 16) chunks0 -> length chunks0 = 16%nat ->
  refill_ret L RNG sp st c lo (map (fun k => Z_to_bv 64 (acompact c k)) (xc_free (x_cls X c))) chunks0 (fun j => c_count (get_cls st j)) m st2 RNG' m' ->
  let n := max_cached c / 2 in
  let st_r := put_cls c (cls_set_count n (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2 in
  exists X', AREP H L st_r X' m' /\ arng L RNG' st_r
    /\ a_cinit st_r = true /\ c_count (get_cls st_r c) = max_count st_r c / 2 /\ 0 < max_count st_r c / 2
    /\ x_busy X' = x_busy X /\ (forall c', c' <> c -> x_cls X' c' = x_cls X c')
    /\ a_live st_r = a_live st /\ a_next st_r = a_next st /\ a_qloc st_r = a_qloc st /\ a_qloc_bytes st_r = a_qloc_bytes st
    /\ a_qglob st_r = a_qglob st /\ a_qglob_bytes st_r = a_qglob_bytes st /\ a_nsec st_r = a_nsec st /\ a_nres st_r = a_nres st
    /\ (forall c', c' <> c -> get_cls st_r c' = get_cls st c')
    /\ munch (arefill_W L st c (bv_unsigned sp)) m m' /\ wmono bsegs m m'.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n :=
  ([(sp - 672, sp); (RB + mu, RB + mu'); (SHU0, SHU1); (FA + 4 * nf, FA + mfa'); (SHF0, SHF1);
    (t + 2792, t + 2800); (t + 2800, t + 3168); (RI, RI + 8); (RI + 16, RI + 56); (RI + 68, RI + 69); (RI + 72, RI + 80);
    (CA, CA + 4); (CA + 16, CA + 16 + 4 * n)]%Z) (only parsing).

Lemma outside_app : forall l1 l2 x, outside (l1 ++ l2) x <-> outside l1 x /\ outside l2 x.
Proof. intros l1 l2 x. induction l1 as [|[lo hi] l1 IH]; cbn; tauto. Qed.

Lemma dj_app : forall l1 l2 A k, disjoint_from l1 A k -> disjoint_from l2 A k -> disjoint_from (l1 ++ l2) A k.
Proof. intros l1 l2 A k D1 D2. induction l1 as [|[lo hi] l1 IH]; cbn in *; [exact D2|]. destruct D1 as [D1 D1']. split; [exact D1| apply IH; exact D1']. Qed.

Section Kinds.
Variables (sp lo t ctx SB c RB FA RI CA mu mu' au nf mfa mfa' n SHU0 SHU1 SHF0 SHF1 : Z).
Definition rkfacts : Prop :=
     (ATOP <= lo /\ lo <= sp - 672 /\ sp <= 2^64)
  /\ (sclr t 4096 /\ iclr t 4096 /\ t + 4096 <= ATOP /\ sclr ctx 65536 /\ 6443008 <= ctx /\ ctx + 65536 <= ATOP /\ (ctx + 4096 <= t \/ t + 4096 <= ctx))   (* [comment removed for export] *)
  /\ (1 <= c <= 31 /\ CA = t + 208 + c * 80 /\ 1 <= n <= 8)
  /\ (17594333495296 <= SB /\ SB + 137438957568 <= ATOP /\ RB = SB + c * 4294967296 /\ FA = RB + 3758096384 /\ RI = SB + 137438953472 + c * 128)
  /\ (t + 4096 <= SB \/ SB + 137438957568 <= t) /\ (ctx + 65536 <= SB \/ SB + 137438957568 <= ctx)
  /\ (0 <= au /\ au <= mu /\ mu <= mu' /\ mu' <= 3758096384 /\ 0 <= nf /\ 4 * nf <= mfa /\ mfa <= mfa' /\ mfa' <= 536870912)
  /\ (2201439137792 <= SHU0 /\ SHU0 <= SHU1 /\ SHU1 <= SHF0 /\ SHF0 <= SHF1 /\ SHF1 <= 17594333495296).
Hypothesis KF : rkfacts.

Ltac kind := pose proof KF as KF'; unfold rkfacts, AIMG_HI in *; unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in KF';
  destruct KF' as (F_lo & F_t & F_c & F_sb & F_tsb & F_csb & F_mu & F_sh);
  cbn [disjoint_from]; repeat (split; [lia|]); first [lia | exact I].

(* [comment removed for export] *)
Lemma RK_img : forall A k, 65536 <= A -> 0 <= k -> A + k <= 6443008 -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
(* [comment removed for export] *)
Lemma RK_obj : forall A k, (A + k <= 2147446784 \/ 17594333495296 <= A) -> A + k <= ATOP -> 0 <= k ->
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= SB \/ SB + 137438957568 <= A) ->
  disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
(* [comment removed for export] *)
Lemma RK_tlow : forall A k, t <= A -> A + k <= t + 288 -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
Lemma RK_thigh : forall A k, t + 3168 <= A -> A + k <= t + 4096 -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
Lemma RK_tstat : forall A k, t + 2768 <= A -> A + k <= t + 2792 -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
(* [comment removed for export] *)
Lemma RK_rec : forall A k, t + 288 <= A -> A + k <= t + 2768 -> 0 <= k -> (A + k <= CA \/ CA + 4 <= A) -> (A + k <= CA + 16 \/ CA + 16 + 4 * n <= A) ->
  disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
(* [comment removed for export] *)
Lemma RK_reg_other : forall A k, SB <= A -> 0 <= k -> (A + k <= RB \/ RB + 4294967296 <= A) -> A + k <= SB + 137438953472 ->
  disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
(* [comment removed for export] *)
Lemma RK_slots : forall A k, RB <= A -> A + k <= RB + mu -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
(* [comment removed for export] *)
Lemma RK_gap : forall A k, RB + mu' <= A -> A + k <= FA + 4 * nf -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
(* [comment removed for export] *)
Lemma RK_ri : forall A k, SB + 137438953472 <= A -> A + k <= SB + 137438957568 -> 0 <= k ->
  (A + k <= RI \/ RI + 8 <= A) -> (A + k <= RI + 16 \/ RI + 56 <= A) -> (A + k <= RI + 68 \/ RI + 69 <= A) -> (A + k <= RI + 72 \/ RI + 80 <= A) ->
  disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
(* [comment removed for export] *)
Lemma RK_shlow : forall A k, 2201439137792 <= A -> A + k <= SHU0 -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
Lemma RK_shmid : forall A k, SHU1 <= A -> A + k <= SHF0 -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
Lemma RK_shhigh : forall A k, SHF1 <= A -> A + k <= 17594333495296 -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
(* [comment removed for export] *)
Lemma RK_stkhi : forall A k, sp <= A -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
End Kinds.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rrec (mu' au2 nfr mfa' n : Z) : aclass := mkAClass mu' au2 nfr mfa' n.

Lemma init_cache_fields : forall st,
  a_live (init_cache st) = a_live st /\ a_next (init_cache st) = a_next st /\ a_qloc (init_cache st) = a_qloc st
  /\ a_qloc_bytes (init_cache st) = a_qloc_bytes st /\ a_qglob (init_cache st) = a_qglob st /\ a_qglob_bytes (init_cache st) = a_qglob_bytes st
  /\ a_nsec (init_cache st) = a_nsec st /\ a_nres (init_cache st) = a_nres st /\ a_ptr_array (init_cache st) = a_ptr_array st
  /\ a_space_beg (init_cache st) = a_space_beg st /\ a_cinit (init_cache st) = true.
Proof. intros st. unfold init_cache. destruct (a_cinit st) eqn:E; cbn; repeat split; try reflexivity. exact E. Qed.

Lemma put_cls_fields : forall c r st,
  a_live (put_cls c r st) = a_live st /\ a_next (put_cls c r st) = a_next st /\ a_qloc (put_cls c r st) = a_qloc st
  /\ a_qloc_bytes (put_cls c r st) = a_qloc_bytes st /\ a_qglob (put_cls c r st) = a_qglob st /\ a_qglob_bytes (put_cls c r st) = a_qglob_bytes st
  /\ a_nsec (put_cls c r st) = a_nsec st /\ a_nres (put_cls c r st) = a_nres st /\ a_ptr_array (put_cls c r st) = a_ptr_array st
  /\ a_space_beg (put_cls c r st) = a_space_beg st /\ a_cinit (put_cls c r st) = a_cinit st.
Proof. intros. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma awf_refill : forall L st X c mu' ncnt mfa' n,
  let r := get_cls st c in let S := size_of_class c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  let nd := ndist st c in let nf2 := nf + ncnt in let au2 := au + ncnt * S in
  let FL2 := xc_free (x_cls X c) ++ newslots nd (Z.to_nat ncnt) in
  let st_r := put_cls c (rrec mu' au2 (nf2 - n) mfa' n) (init_cache st) in
  let X' := xr X c (firstn (Z.to_nat (nf2 - n)) FL2) (skipn (Z.to_nat (nf2 - n)) FL2) in
  awf L st X -> 1 <= c < K_NUM_CLASSES -> c_count r = 0 ->
  mu <= mu' <= K_FREEARR_OFF -> mu' mod K_USER_MAP = 0 -> 0 <= ncnt -> au2 <= mu' ->
  4 * nf2 <= mfa' <= K_FREEARR_MAX -> mfa <= mfa' -> mfa' mod K_FREEARR_MAP = 0 ->
  1 <= n <= nf2 -> 2 * n = max_cached c ->
  awf L st_r X'.
Proof.
  intros L st X c mu' ncnt mfa' n. cbv zeta.
  intros WF HC CNT0 MUB MUM NC0 NCS NEWB NEWM NEWMOD N N2.
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  pose proof (size_of_class_facts c HC) as [SZ16 SZM].
  pose proof (init_cache_fields st) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
  set (st1 := init_cache st) in *.
  set (S := size_of_class c) in *. set (nd := ndist st c) in *.
  set (FL2 := xc_free (x_cls X c) ++ newslots nd (Z.to_nat ncnt)) in *.
  assert (XC0 : xc_cache (x_cls X c) = []).
  { destruct (xc_cache (x_cls X c)) as [|y l] eqn:E; [reflexivity|]. exfalso. rewrite ?E in LENC. cbn [length] in LENC. clear -LENC CNT0. lia. }
  assert (NDE : nd * S <= c_allocated_user (get_cls st c) < nd * S + S /\ 0 <= nd).
  { subst nd S. unfold ndist. generalize A1 SZ16; clear; intros. Z.div_mod_to_equations. nia. }
  destruct NDE as [NDE ND0].
  assert (AUE : c_allocated_user (get_cls st c) = nd * S) by (subst nd S; unfold ndist; generalize A3 A1 SZ16 NDE; clear; intros; Z.div_mod_to_equations; nia).
  assert (ND2 : ndist (put_cls c (rrec mu' (c_allocated_user (get_cls st c) + ncnt * S) (c_num_freed (get_cls st c) + ncnt - n) mfa' n) st1) c = nd + ncnt).
  { unfold ndist. rewrite get_cls_put_cls_eq. cbn [c_allocated_user rrec]. fold S. rewrite AUE.
    generalize SZ16 ND0 NC0; clear; intros. rewrite <- Z.mul_add_distr_r, Z.div_mul by lia. reflexivity. }
  assert (LFL2 : Z.of_nat (length FL2) = c_num_freed (get_cls st c) + ncnt) by (subst FL2; rewrite length_app, newslots_length; clear -LENF NC0; lia).
  unfold awf.
  cbn [a_space_beg a_ptr_array a_live a_next put_cls set_cls].
  rewrite E10, E9.
  split; [exact SBE|]. split; [exact PAE|]. split; [exact SAL|]. split; [exact SLO|]. split; [exact SHI|].
  split.
  { (* [comment removed for export] *)
    intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE].
    - rewrite get_cls_put_cls_eq, xr_cls_eq. cbn [c_mapped_user c_allocated_user c_num_freed c_mapped_free_array c_count rrec xc_free xc_cache]. fold S.
      rewrite ND2. unfold max_count. cbn [a_cinit put_cls set_cls]. rewrite E11.
      rewrite xr_busy_slots.
      split; [clear -A1 NC0 NCS SZ16; nia|]. split; [exact (proj2 MUB)|]. split.
      { rewrite AUE. rewrite <- Z.mul_add_distr_r. apply Z_mod_mult. }
      split; [exact MUM|]. split; [clear -N NC0 A5; lia|]. split; [clear -NEWB N; lia|]. split; [exact NEWMOD|].
      split; [rewrite length_firstn; clear -LFL2 N NC0 A5; lia|].
      split; [rewrite length_skipn; clear -LFL2 N NC0 A5; lia|].
      split; [clear -N N2; lia|].
      rewrite app_assoc, firstn_skipn.
      split.
      + (* [comment removed for export] *)
        subst FL2. rewrite XC0 in ND. cbn [app] in ND. rewrite <- app_assoc.
        eapply Permutation.Permutation_NoDup; [apply Permutation.Permutation_app_swap_app|].
        apply nodup_app; [apply newslots_NoDup | exact ND |].
        intros x Hx Hx'. apply newslots_In in Hx. rewrite Z2Nat.id in Hx by exact NC0.
        specialize (RANGE x ltac:(rewrite XC0; cbn [app]; exact Hx')). unfold ndist in RANGE. fold S nd in RANGE. clear -Hx RANGE. lia.
      + intros k0 Hk. subst FL2. rewrite <- app_assoc, in_app_iff, in_app_iff in Hk.
        destruct Hk as [Hk|[Hk|Hk]].
        * specialize (RANGE k0 ltac:(apply in_app_iff; left; exact Hk)). unfold ndist in RANGE. fold S nd in RANGE. clear -RANGE NC0; lia.
        * apply newslots_In in Hk. rewrite Z2Nat.id in Hk by exact NC0. clear -Hk ND0; lia.
        * specialize (RANGE k0 ltac:(rewrite XC0; cbn [app]; apply in_app_iff; right; exact Hk)). unfold ndist in RANGE. fold S nd in RANGE. clear -RANGE NC0; lia.
    - rewrite (get_cls_put_cls_ne c c') by exact NE. rewrite (xr_cls_ne X c _ _ c' NE), xr_busy_slots.
      subst st1. rewrite init_cache_cls. unfold ndist. rewrite (get_cls_put_cls_ne c c') by exact NE. rewrite init_cache_cls.
      unfold max_count. cbn [a_cinit put_cls set_cls]. rewrite E11.
      destruct (PERC c' Hc') as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & BLENF & BLENC & BCNTB & BND & BRANGE).
      pose proof (max_cached_range c' ltac:(unfold K_NUM_CLASSES in Hc'; clear -Hc'; lia)) as [MCR' _].
      unfold max_count in BCNTB. unfold ndist in BRANGE.
      repeat lazymatch goal with |- _ /\ _ => split end; try assumption; try (clear -B1 B6 BCNTB MCR'; lia).
      destruct (a_cinit st); clear -BCNTB MCR'; lia. }
  split.
  { intros c' Hc'. rewrite (get_cls_put_cls_ne c c') by (intros ->; exact (Hc' HC)). subst st1. rewrite init_cache_cls. apply OUTC. exact Hc'. }
  cbn [x_busy xr]. rewrite E1, E2.
  split; [exact BUSY|]. split; [exact LIVE|]. split; [exact FRESH|]. exact UNIQ.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma refill_store : store_refill_stmt.
Proof.
  unfold store_refill_stmt.
  intros L RNG RNG' sp m m' st st2 X c lo chunks0 ALO ARNG AR HC CNT0 CEIL LO CH LCH RR.
  (* [comment removed for export] *)
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  destruct THR as (T0c & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  destruct (CLS c HC) as (RCELLS & FARR & SLOTS & SSH). destruct (AVL c HC) as [AZU AZF].
  destruct RCELLS as (MTX16 & REG & RJ4 & EXH & RJ56). destruct FARR as (FL & FJ & FSJ).
  destruct SLOTS as [SL UND]. destruct SSH as [SSL SUND].
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof TL1 as TL1u; unfold sclr, KLS in TL1u. pose proof TL4 as TL4u; unfold iclr, AIMG_LO, AIMG_HI in TL4u.   (* [comment removed for export] *)
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof CL1 as CL1u; unfold sclr, KLS in CL1u.   (* [comment removed for export] *)
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof (size_of_class_facts c HC) as [SZ16 SZM].
  pose proof (max_cached_range c ltac:(unfold K_NUM_CLASSES in HC; clear -HC; lia)) as [MCR MCE].
  assert (XC0 : xc_cache (x_cls X c) = []).
  { destruct (xc_cache (x_cls X c)) as [|y l] eqn:E; [reflexivity|]. exfalso. rewrite ?E in LENC. cbn [length] in LENC. clear -LENC CNT0. lia. }
  (* [comment removed for export] *)
  destruct RR as (m1 & MU1 & WM1 & TR & RECS').
  unfold refill_tail_ret in TR. rewrite !init_cache_cls in TR. cbv zeta in TR.
  destruct TR as (FPLE & mu' & mfa' & ncnt & sj' & stm' & stn' & UD & MUB & MUM' & NCE & NC0 & NCS & FD & NEWB & NEWM & NEWMOD & NLE & AR2 & JR
                  & GC2 & ST2E & MUT & WMT & MIT & STT & MTX' & REG' & EXH' & STN' & STATS' & LSJ' & STM' & REC' & CH' & AZU' & AZF' & MC').
  unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *.
  change (2^37) with 137438953472 in *.
  (* [comment removed for export] *)
  set (S := size_of_class c) in *. set (n := max_cached c / 2) in *.
  set (mu := c_mapped_user (get_cls st c)) in *. set (au := c_allocated_user (get_cls st c)) in *.
  set (nf := c_num_freed (get_cls st c)) in *. set (mfa := c_mapped_free_array (get_cls st c)) in *.
  set (nd := ndist st c) in *.
  set (FL2 := xc_free (x_cls X c) ++ newslots nd (Z.to_nat ncnt)).
  set (fr := firstn (Z.to_nat (nf + ncnt - n)) FL2). set (ca := skipn (Z.to_nat (nf + ncnt - n)) FL2).
  set (X' := xr X c fr ca).
  assert (N : 1 <= n <= 8 /\ 2 * n = max_cached c) by (subst n; clear -MCR MCE; Z.div_mod_to_equations; lia). destruct N as [N N2].
  assert (NDE : nd * S <= au < nd * S + S /\ 0 <= nd /\ au = nd * S).
  { subst nd S au. unfold ndist. generalize A1 A3 SZ16; clear; intros. Z.div_mod_to_equations. nia. }
  destruct NDE as (NDE & ND0 & AUE).
  assert (GEO : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296
                /\ afreearr L c = al_space_beg L + c * 4294967296 + 3758096384 /\ acache_addr L c = al_t L + 208 + c * 80).
  { unfold aregion_info, afreearr, aregion, acache_addr, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, ARI_STRIDE. change (2^32) with 4294967296. change (2^37) with 137438953472. repeat split; reflexivity. }
  destruct GEO as (RIE & RBE & FAE & CAE).
  (* [comment removed for export] *)
  assert (STR : put_cls c (cls_set_count n (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2
                = put_cls c (rrec mu' (au + ncnt * S) (nf + ncnt - n) mfa' n) (init_cache st)).
  { rewrite GC2. cbn [c_num_freed cls_set_num_freed cls_set_count c_mapped_user c_allocated_user c_mapped_free_array c_count]. unfold rrec.
    destruct ST2E as [E|E]; rewrite E at 1; [reflexivity| apply put_cls_put_cls]. }
  set (st_r := put_cls c (rrec mu' (au + ncnt * S) (nf + ncnt - n) mfa' n) (init_cache st)) in *. rewrite STR.
  pose proof (init_cache_fields st) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
  assert (GR : get_cls st_r c = rrec mu' (au + ncnt * S) (nf + ncnt - n) mfa' n) by (subst st_r; apply get_cls_put_cls_eq).
  assert (GO : forall c', c' <> c -> get_cls st_r c' = get_cls st c') by (intros c' NE; subst st_r; rewrite (get_cls_put_cls_ne c c') by exact NE; apply init_cache_cls).
  assert (CIR : a_cinit st_r = true) by (subst st_r; cbn; exact E11).
  assert (ND2 : ndist st_r c = nd + ncnt).
  { unfold ndist. rewrite GR. cbn [c_allocated_user rrec]. fold S. rewrite AUE. generalize SZ16 ND0 NC0; clear; intros. rewrite <- Z.mul_add_distr_r, Z.div_mul by lia. reflexivity. }
  (* [comment removed for export] *)
  set (RB := aregion L c) in *. set (FA := afreearr L c) in *. set (RI := aregion_info L c) in *. set (CA := acache_addr L c) in *.
  set (SHU0 := shad (RB + mu)) in *. set (SHU1 := SHU0 + shlen (mu' - mu)) in *.
  set (SHF0 := shad (FA + mfa)) in *. set (SHF1 := SHF0 + shlen (mfa' - mfa)) in *.
  assert (SHE : SHU1 = shad (RB + mu') /\ SHF1 = shad (FA + mfa') /\ shad RB + shlen mu = SHU0 /\ shad FA + shlen mfa = SHF0
                /\ 2201439137792 <= shad RB /\ shad RB <= SHU0 /\ SHU0 <= SHU1 /\ SHU1 + shlen (3758096384 - mu') = shad FA /\ shad FA <= SHF0 /\ SHF0 <= SHF1
                /\ SHF1 + shlen (536870912 - mfa') = shad (RB + 4294967296) /\ shad (RB + 4294967296) <= 17594333495296
                /\ SHU1 <= shad FA /\ SHF1 <= shad (RB + 4294967296)
                /\ shad RB = shad (al_space_beg L) + c * 536870912 /\ shad (RB + 4294967296) = shad (al_space_beg L) + (c + 1) * 536870912
                /\ shad (al_space_beg L) + 32 * 536870912 <= 17594333495296).
  { subst SHU1 SHU0 SHF1 SHF0. rewrite RBE, FAE. rewrite !shad_div, !shlen_div. unfold ASHOFF.
    clear -SP1 SP2 SP3 HC MUB A1 A2 A4 MUM' A5 A6 A7 NEWB NEWM NEWMOD. Z.div_mod_to_equations. lia. }
  destruct SHE as (SHE1 & SHE2 & SHE3 & SHE4 & SH1 & SH2 & SH3 & SH4 & SH5 & SH6 & SH7 & SH8 & SH12 & SH13 & SH9 & SH10 & SH11).
  assert (KF : rkfacts (bv_unsigned sp) lo (al_t L) (al_ctx L) (al_space_beg L) c RB FA RI CA mu mu' au nf mfa mfa' n SHU0 SHU1 SHF0 SHF1).
  { unfold rkfacts. pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
    clear -CEIL LO SPR TL1 TL2 TL4 CL1 CL2 CL3 CL5 HC CAE N SP1 SP2 RBE FAE RIE TSP SCX A1 MUB A5 A6 NEWB NEWM SH1 SH2 SH3 SH5 SH6 SH8 SH12 SH13.
    unfold AIMG_HI in CL3. unfold iclr, AIMG_LO, AIMG_HI in TL4 |- *. repeat split; first [assumption | lia]. }   (* [comment removed for export] *)
  assert (MUALL : munch (Wr (bv_unsigned sp) RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 (al_t L) RI CA n ++ ic_W L 1 31) m m').
  { eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MUT]].
    - unfold sub_fp. intros x Hx. apply outside_app in Hx. destruct Hx as [H13 HW]. cbn [outside] in H13 |- *. split; [exact (proj1 H13) | exact HW].
    - unfold sub_fp. intros x Hx. apply outside_app in Hx. destruct Hx as [H13 _]. subst CA. exact H13. }
  pose proof (wmono_trans _ _ _ _ WM1 WMT) as WMALL.
  (* [comment removed for export] *)
  assert (ICW_far : forall A k, (A + k <= al_t L \/ al_t L + 4096 <= A) -> disjoint_from (ic_W L 1 31) A k).
  { intros A k HA. apply ic_W_disjoint_gen; [unfold acache_addr; clear -HA; lia | clear; cbn; lia | clear; lia]. }
  assert (ICW_t : forall A k, (A + k <= al_t L + 292 \/ al_t L + 2768 <= A) -> disjoint_from (ic_W L 1 31) A k).
  { intros A k HA. apply ic_W_disjoint_gen; [unfold acache_addr; clear -HA; lia | clear; cbn; lia | clear; lia]. }
  (* [comment removed for export] *)
  assert (FLE : map (fun k => Z_to_bv 64 (acompact c k)) FL2 = map (fun k => Z_to_bv 64 (acompact c k)) (xc_free (x_cls X c)) ++ fvals au S (Z.to_nat ncnt)).
  { subst FL2. rewrite map_app. f_equal. rewrite AUE. apply map_cw_newslots. unfold K_NUM_CLASSES; exact HC. }
  rewrite <- FLE in AR2, CH'.
  assert (LFL2 : length FL2 = Z.to_nat (nf + ncnt)) by (subst FL2; rewrite length_app, newslots_length; clear -LENF NC0 A5; lia).
  assert (MOD8 : mu mod 8 = 0 /\ mu' mod 8 = 0 /\ mfa mod 8 = 0 /\ mfa' mod 8 = 0 /\ au mod 8 = 0 /\ S mod 8 = 0 /\ RB mod 8 = 0 /\ FA mod 8 = 0).
  { rewrite RBE, FAE, AUE. clear -A4 MUM' A7 NEWMOD SZM SP3 ND0. Z.div_mod_to_equations. nia. }
  destruct MOD8 as (M8a & M8b & M8c & M8d & M8e & M8f & M8g & M8h).
  (* [comment removed for export] *)
  assert (BIGJ : junk_at m' (RB + au) (mu' - au)).
  { assert (J1 : junk_at m' (RB + au) (mu - au)).
    { eapply junk_frame; [exact UND | exact MUALL | exact WMALL |]. intros _.
      apply dj_app; [eapply (RK_slots _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -A1; lia | apply ICW_far; clear -A1 A2 TSP RBE HC; lia]. }
    destruct UD as [Emu|(_ & _ & Emu & ZN & _)].
    - rewrite Emu. exact J1.
    - replace (mu' - au) with ((mu - au) + (mu' - mu)) by (clear; lia). apply junk_merge; [exact J1 | | clear -A1; lia | clear -MUB; lia].
      replace (RB + au + (mu - au)) with (RB + mu) by (clear; lia). eexists. exact ZN. }
  assert (BIGF : fill_at m' (shad (RB + au)) (shlen (mu' - au)) 0xfa).
  { assert (F1 : fill_at m' (shad (RB + au)) (shlen (mu - au)) 0xfa).
    { eapply fill_frame; [exact SUND | exact MUALL | exact WMALL |]. intros _.
      assert (B : shad (RB + au) + shlen (mu - au) <= SHU0 /\ 2201439137792 <= shad (RB + au) /\ 0 <= shlen (mu - au)).
      { subst SHU0. rewrite !shad_div, !shlen_div in *. unfold ASHOFF in *. clear -A1 SH1 M8g M8e M8a. Z.div_mod_to_equations. lia. }
      apply dj_app; [eapply (RK_shlow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -B; lia | apply ICW_far; clear -B TL1u SH2 SH3 SH12 SH5 SH6 SH13 SH8; lia]. }
    destruct UD as [Emu|(_ & _ & Emu & _ & FI & _)].
    - rewrite Emu. exact F1.
    - replace (shlen (mu' - au)) with (shlen (mu - au) + shlen (mu' - mu)) by (rewrite !shlen_div; clear -M8a M8b M8e A1 MUB; Z.div_mod_to_equations; lia).
      apply fill_merge; [exact F1 | | rewrite shlen_div; clear -A1 M8a M8e; Z.div_mod_to_equations; lia | rewrite shlen_div; clear -MUB; Z.div_mod_to_equations; lia].
      replace (shad (RB + au) + shlen (mu - au)) with (shad (RB + mu)) by (rewrite !shad_div, shlen_div; clear -A1 M8a M8e M8g; Z.div_mod_to_equations; lia).
      exact FI. }
  (* [comment removed for export] *)
  assert (RCc : aregion_cells L st_r m' c).
  { unfold aregion_cells. cbv zeta. fold RI. rewrite GR. cbn [c_num_freed c_mapped_free_array c_allocated_user c_mapped_user rrec]. fold S.
    pose proof MTX16 as M2. rw_split M2 1%nat M2a M2b. clear M2a.
    eapply cells_frame in M2b; [| exact MUALL | exact WMALL | cbn [cells_size csize Nat.add];
      apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]].
    split. { rw_join MTX' M2b M16. exact M16. }
    split; [exact REG'|].
    split. { eapply junk_frame; [exact RJ4 | exact MUALL | exact WMALL |]. intros _.
             apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]. }
    split; [exact EXH'|].
    destruct (junk_split m (RI + 72) 8 48 RJ56 ltac:(clear; lia) ltac:(clear; lia)) as [_ J48].
    replace 56 with (8 + 48) by reflexivity. apply junk_merge; [| | clear; lia | clear; lia].
    - pose proof (junk_of_cells m' _ _ STN') as J8. cbn in J8. exact J8.
    - eapply junk_frame; [exact J48 | exact MUALL | exact WMALL |]. intros _.
      apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]. }
  (* [comment removed for export] *)
  assert (FAc : afreearray L st_r X' m' c).
  { unfold afreearray. cbv zeta. fold FA. rewrite GR. cbn [c_num_freed c_mapped_free_array rrec]. subst X'. rewrite xr_cls_eq. cbn [xc_free].
    split; [| split].
    - subst fr. rewrite <- firstn_map. apply u32arr_firstn; [exact AR2 | rewrite length_map, LFL2; clear -N NLE NC0 A5; lia].
    - replace (mfa' - 4 * (nf + ncnt - n)) with (4 * Z.of_nat (length (skipn (Z.to_nat (nf + ncnt - n)) FL2)) + (mfa' - 4 * (nf + ncnt)))
        by (rewrite length_skipn, LFL2; clear -N NLE NC0 A5; lia).
      apply junk_merge; [| | clear; lia | clear -NEWB; lia].
      + pose proof (u32arr_skipn m' FA _ (Z.to_nat (nf + ncnt - n)) AR2 ltac:(rewrite length_map, LFL2; clear -N NLE NC0 A5; lia)) as SK.
        replace (FA + 4 * Z.of_nat (Z.to_nat (nf + ncnt - n))) with (FA + 4 * (nf + ncnt - n)) in SK by (clear -N NLE NC0 A5; lia).
        rewrite skipn_map in SK. apply junk_of_u32arr in SK. rewrite length_map in SK. exact SK.
      + rewrite length_skipn, LFL2. replace (FA + 4 * (nf + ncnt - n) + 4 * Z.of_nat (Z.to_nat (nf + ncnt) - Z.to_nat (nf + ncnt - n))) with (FA + 4 * (nf + ncnt)) by (clear -N NLE NC0 A5; lia).
        exact JR.
    - (* [comment removed for export] *)
      assert (FS1 : junk_at m' (shad FA) (shlen mfa)).
      { eapply junk_frame; [exact FSJ | exact MUALL | exact WMALL |]. intros _.
        apply dj_app; [eapply (RK_shmid _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite <- ?SHE4; clear -SH12 SHE4 A5 A6 M8c; rewrite ?shlen_div in *; Z.div_mod_to_equations; lia
                      | apply ICW_far; clear -SHE4 SH5 SH6 SH13 SH8 SH1 SH2 SH3 SH12 TL1u; rewrite ?shlen_div in *; Z.div_mod_to_equations; lia]. }
      destruct FD as [Emfa|(_ & Emfa & FI & _)].
      + rewrite Emfa. exact FS1.
      + replace (shlen mfa') with (shlen mfa + shlen (mfa' - mfa)) by (rewrite !shlen_div; clear -M8c M8d NEWM A5 A6; Z.div_mod_to_equations; lia).
        apply junk_merge; [exact FS1 | rewrite SHE4; eapply junk_of_fill; exact FI | rewrite shlen_div; clear -A5 A6; Z.div_mod_to_equations; lia | rewrite shlen_div; clear -NEWM; Z.div_mod_to_equations; lia]. }
  (* [comment removed for export] *)
  assert (SLOTK : forall k, 0 <= k -> aslot_addr L c k = RB + k * S /\ (k < nd -> k * S + S <= au) /\ (nd <= k < nd + ncnt -> au <= k * S /\ k * S + S <= au + ncnt * S)
                            /\ shad (aslot_addr L c k) = shad RB + shlen (k * S) /\ shad (aslot_addr L c k) + shlen S = shad RB + shlen (k * S + S)).
  { intros k Hk. assert (E : aslot_addr L c k = RB + k * S) by reflexivity. rewrite E.
    assert (KS8 : (k * S) mod 8 = 0) by (clear -M8f Hk; Z.div_mod_to_equations; nia).
    split; [reflexivity|]. split; [rewrite AUE; clear -Hk SZ16; intros; nia|]. split; [rewrite AUE; clear -Hk SZ16; intros; nia|].
    rewrite !shad_div, !shlen_div. clear -KS8 M8g M8f Hk SZ16. Z.div_mod_to_equations. nia. }
  assert (NEWFREE : forall k, nd <= k -> busy_of X c k = None).
  { intros k Hk. destruct (busy_of X c k) as [b|] eqn:Bk; [exfalso| reflexivity].
    apply busy_of_In_slots in Bk. specialize (RANGE k ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Bk)).
    unfold ndist in RANGE. fold S au nd in RANGE. clear -RANGE Hk. lia. }
  assert (SLc : aslots L st_r X' m' c).
  { unfold aslots. cbv zeta. rewrite ND2, GR. cbn [c_allocated_user c_mapped_user rrec]. fold S RB. subst X'. split.
    - intros k Hk. rewrite xr_busy_of. destruct (SLOTK k ltac:(clear -Hk; lia)) as (AE & KLO & KHI & _ & _).
      destruct (Z_lt_le_dec k nd) as [KL|KG].
      + specialize (SL k ltac:(clear -Hk KL; lia)). specialize (KLO KL).
        destruct (busy_of X c k) as [b|] eqn:Bk.
        * destruct (busy_of_Some_facts X c k b Bk) as (BIn & BC & BK).
          eapply (aslot_busy_frame L _ m m' MUALL WMALL); [exact SL | exact (awf_fits L st X b WF BIn) |].
          unfold xb_alloc. rewrite BC, BK, AE. fold S.
          apply dj_app; [eapply (RK_slots _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -KLO Hk A1 SZ16; nia | apply ICW_far; clear -KLO Hk A1 A2 SZ16 TSP RBE HC; nia].
        * eapply junk_frame; [exact SL | exact MUALL | exact WMALL |]. intros _. rewrite AE.
          apply dj_app; [eapply (RK_slots _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -KLO Hk A1 SZ16; nia | apply ICW_far; clear -KLO Hk A1 A2 SZ16 TSP RBE HC; nia].
      + rewrite (NEWFREE k KG). specialize (KHI ltac:(clear -KG Hk; lia)). rewrite AE.
        eapply junk_sub; [exact BIGJ | clear -KHI | clear -KHI NCS | clear -SZ16]; lia.
    - eapply junk_sub; [exact BIGJ | clear -NC0 SZ16; nia | clear; lia | clear -NCS; lia]. }
  (* [comment removed for export] *)
  assert (SSc : aslot_shadow L st_r X' m' c).
  { unfold aslot_shadow. cbv zeta. rewrite ND2, GR. cbn [c_allocated_user c_mapped_user rrec]. fold S RB. subst X'. split.
    - intros k Hk. rewrite xr_busy_of. destruct (SLOTK k ltac:(clear -Hk; lia)) as (AE & KLO & KHI & SHA & SHB).
      destruct (Z_lt_le_dec k nd) as [KL|KG].
      + specialize (SSL k ltac:(clear -Hk KL; lia)). specialize (KLO KL).
        eapply cells_frame; [exact SSL | exact MUALL | exact WMALL |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (rewrite shlen_div; clear -SZ16; Z.div_mod_to_equations; lia).
        assert (B : shad RB + shlen (k * S + S) <= SHU0 /\ 2201439137792 <= shad RB + shlen (k * S)).
        { rewrite <- SHE3. rewrite !shlen_div. clear -KLO A1 SH1 Hk SZ16. Z.div_mod_to_equations. nia. }
        rewrite SHA.
        apply dj_app; [eapply (RK_shlow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); [clear -B; lia | rewrite <- SHA, SHB; clear -B; lia | rewrite shlen_div; clear -SZ16; Z.div_mod_to_equations; lia]
                      | apply ICW_far; rewrite <- SHA, SHB; clear -B SHA SHB TL1u TL4u SH2 SH3 SH12 SH5 SH6 SH13 SH8; lia].
      + rewrite (NEWFREE k KG). specialize (KHI ltac:(clear -KG Hk; lia)). cbn [slot_shadow_bytes]. rewrite SHA.
        eapply fill_sub; [exact BIGF | | | rewrite shlen_div; clear -SZ16; Z.div_mod_to_equations; lia].
        * rewrite shad_div, (shad_div RB), shlen_div. clear -KHI M8g M8e A1. Z.div_mod_to_equations. nia.
        * rewrite (shad_div (RB + au)), (shad_div RB), !shlen_div. clear -KHI NCS M8g M8e M8f A1 SZ16 Hk. Z.div_mod_to_equations. nia.
    - eapply fill_sub; [exact BIGF | | | rewrite shlen_div; clear -NCS; Z.div_mod_to_equations; lia].
      + rewrite !shad_div. clear -NC0 SZ16 M8g M8e; Z.div_mod_to_equations; nia.
      + rewrite !shad_div, !shlen_div. clear -NC0 NCS SZ16 M8g M8e M8f A1; Z.div_mod_to_equations; nia. }
  (* [comment removed for export] *)
  assert (AVc : ashadow_avail L st_r m' c).
  { unfold ashadow_avail. cbv zeta. rewrite GR. cbn [c_mapped_user c_mapped_free_array rrec]. fold RB FA. split; [exact AZU' | exact AZF']. }
  assert (ACc : acache_cells L st_r X' m' c).
  { unfold acache_cells. cbv zeta. fold CA. rewrite GR. cbn [c_count rrec]. subst X'. rewrite xr_cls_eq. cbn [xc_cache].
    unfold max_count. rewrite CIR. exists (skipn (Z.to_nat n) chunks0).
    split; [exact REC'|]. split.
    - subst ca. rewrite <- skipn_map. exact CH'.
    - subst ca. rewrite !length_skipn, LFL2, LCH. clear -N NLE NC0 A5; lia. }
  (* [comment removed for export] *)
  assert (CLS' : forall c', 1 <= c' < 32 -> c' <> c ->
            aregion_cells L st_r m' c' /\ afreearray L st_r X' m' c' /\ aslots L st_r X' m' c' /\ aslot_shadow L st_r X' m' c' /\ ashadow_avail L st_r m' c' /\ acache_cells L st_r X' m' c').
  { intros c' Hc' NE. destruct (CLS c' Hc') as (RC2 & FA2 & SL2 & SS2). pose proof (AVL c' Hc') as AV2. destruct (CACHES c' Hc') as [tl (RH & RCH & RLEN)].
    destruct (PERC c' Hc') as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & BLENF & BLENC & BCNTB & BND & BRANGE).
    pose proof (size_of_class_facts c' Hc') as [SZ' SZM'].
    pose proof (GO c' NE) as G'.
    pose proof (region_other_geo L c c' ALO HC Hc' NE) as REGD. change (aregion L c) with RB in REGD.
    destruct REGD as (RD1 & RD2 & RD3 & RD4 & RD5 & RD6 & RD7 & RD8 & RD9 & RD10 & RD11).
    (* [comment removed for export] *)
    assert (DJR : forall A k, aregion L c' <= A -> A + k <= aregion L c' + 4294967296 -> 0 <= k ->
                   disjoint_from (Wr (bv_unsigned sp) RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 (al_t L) RI CA n ++ ic_W L 1 31) A k).
    { intros A k HA HB Hk. apply dj_app; [eapply (RK_reg_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk RD1 RD2 RD3; lia
                                        | apply ICW_far; clear -HA HB Hk RD1 RD3 TSP; lia]. }
    assert (DJS : forall A k, shad (aregion L c') <= A -> A + k <= shad (aregion L c') + shlen 4294967296 -> 0 <= k ->
                   disjoint_from (Wr (bv_unsigned sp) RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 (al_t L) RI CA n ++ ic_W L 1 31) A k).
    { intros A k HA HB Hk. apply dj_app; [| apply ICW_far; clear -HA HB Hk RD9 RD10 TL1u; lia].
      destruct RD8 as [LOW|HIGH].
      - eapply (RK_shlow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk LOW RD9 SH2; lia.
      - eapply (RK_shhigh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk HIGH RD10 SH13; lia. }
    assert (DJI : disjoint_from (Wr (bv_unsigned sp) RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 (al_t L) RI CA n ++ ic_W L 1 31) (aregion_info L c') 128).
    { apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RD5, ?RIE; clear -Hc' NE HC; lia | apply ICW_far; rewrite ?RD5; clear -Hc' SP1 TSP; lia]. }
    split; [| split; [| split; [| split; [| split]]]].
    - eapply (aregion_cells_frame L _ m m' MUALL WMALL st); [exact RC2 | rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | exact DJI].
    - eapply (afreearray_frame L _ m m' MUALL WMALL st st_r X); [exact FA2 | rewrite G'; reflexivity | rewrite G'; reflexivity | subst X'; rewrite (xr_cls_ne X c _ _ c' NE); reflexivity
        | exact BLENF | exact B5 | | clear -B6; lia |].
      + apply DJR; rewrite ?RD4; clear -B5 B6 B2; lia.
      + apply DJS; rewrite ?RD11, ?shlen_div; try (clear -B2 B5 B6; Z.div_mod_to_equations; lia).
    - eapply (aslots_update L _ m m' MUALL WMALL st st_r X _ c' (-1)); [exact SL2 | unfold ndist; rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | | |].
      + intros k Hk _. subst X'. rewrite xr_busy_of. split; [reflexivity|]. split.
        * destruct (slot_in_region L st c' k ltac:(clear -SZ'; lia) ltac:(clear -B1; lia) Hk) as (Q1 & Q2 & Q3).
          apply DJR; [exact Q1 | clear -Q2 B1 B2; lia | clear -SZ'; lia].
        * intros b Hb. destruct (busy_of_Some_facts X c' k b Hb) as (BIn & BC & BK). split; [exact BC|]. split; [exact BK|]. exact (awf_fits L st X b WF BIn).
      + intros POS. apply DJR; clear -B1 B2 POS; lia.
      + intros HK. exfalso. clear -HK. lia.
    - eapply (aslot_shadow_update L _ m m' MUALL WMALL st st_r X _ c' (-1)); [exact SS2 | unfold ndist; rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | | | | rewrite shlen_div; clear -SZ'; Z.div_mod_to_equations; lia].
      + intros k Hk _. subst X'. rewrite xr_busy_of. split; [reflexivity|].
        destruct (slot_in_region L st c' k ltac:(clear -SZ'; lia) ltac:(clear -B1; lia) Hk) as (Q1 & Q2 & Q3).
        apply DJS.
        * apply shad_mono. exact Q1.
        * rewrite !shad_div, !shlen_div in *. clear -Q1 Q2 B1 B2 RD7. Z.div_mod_to_equations. lia.
        * rewrite shlen_div. clear -SZ'; Z.div_mod_to_equations; lia.
      + intros POS. apply DJS.
        * apply shad_mono. clear -B1; lia.
        * rewrite !shad_div, !shlen_div in *. clear -B1 B2 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
      + intros HK. exfalso. clear -HK. lia.
    - eapply (ashadow_avail_frame L _ m m' MUALL WMALL st); [exact AV2 | rewrite G'; reflexivity | rewrite G'; reflexivity | |]; unfold K_FREEARR_OFF, K_FREEARR_MAX.
      + intros POS. apply DJS.
        * apply shad_mono. clear -B1; lia.
        * rewrite !shad_div, !shlen_div in *. clear -B1 B2 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
      + intros POS. apply DJS.
        * apply shad_mono. rewrite RD4. clear -B5 B6; lia.
        * rewrite RD4. rewrite !shad_div, !shlen_div in *. clear -B5 B6 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
    - unfold acache_cells. cbv zeta. rewrite G'. unfold max_count. rewrite CIR. subst X'. rewrite (xr_cls_ne X c _ _ c' NE). exists tl.
      split; [exact (RECS' c' ltac:(clear -Hc'; lia) NE)|]. split; [| exact RLEN].
      eapply u32arr_frame; [exact RCH | exact MUALL | exact WMALL |]. rewrite length_app, length_map.
      replace (Z.of_nat (length (xc_cache (x_cls X c')) + length tl)) with 16 by (clear -RLEN; lia).
      apply dj_app; [eapply (RK_rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RD6, ?CAE; clear -Hc' NE HC N; lia | change (4 * 16) with 64; apply ic_W_disjoint_chunks]. }
  (* [comment removed for export] *)
  assert (BB : forall b, In b (x_busy X) ->
      al_space_beg L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + 137438953472
      /\ (xb_alloc L b + size_of_class (xb_class b) <= RB + mu \/ RB + 4294967296 <= xb_alloc L b)).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc.
    destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
    - rewrite EC in P5, P4, Q1, Q2 |- *.
      change (aregion L c) with RB in P5, P4. change (c_allocated_user (get_cls st c)) with au in P4, Q1. change (c_mapped_user (get_cls st c)) with mu in Q1, Q2.
      split; [clear -P5 RBE HC; lia|]. split; [clear -P4 A1 A2 RBE HC; lia|]. left. clear -P4 A1; lia.
    - pose proof (region_other_geo L c (xb_class b) ALO HC CLB NC) as (R1 & R2 & R3 & _). change (aregion L c) with RB in R2.
      split; [clear -P5 R1; lia|]. split; [clear -P4 Q1 Q2 R3; lia|].
      destruct R2 as [D|D]; [left; clear -D P4 Q1 Q2 A1; lia | right; clear -D P5; lia]. }
  (* [comment removed for export] *)
  assert (DJimg : forall A k, 65536 <= A -> 0 <= k -> A + k <= 6443008 ->
            disjoint_from (Wr (bv_unsigned sp) RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 (al_t L) RI CA n ++ ic_W L 1 31) A k).
  { intros A k H1 H2 H3. apply dj_app; [eapply (RK_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); assumption | apply ICW_far; clear -H1 H3 TL4u; lia]. }
  assert (DJt : forall A k, al_t L <= A -> 0 <= k ->
            (A + k <= al_t L + 288 \/ (al_t L + 2768 <= A /\ A + k <= al_t L + 2792) \/ (al_t L + 3168 <= A /\ A + k <= al_t L + 4096)) ->
            disjoint_from (Wr (bv_unsigned sp) RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 (al_t L) RI CA n ++ ic_W L 1 31) A k).
  { intros A k H1 H2 H3. apply dj_app; [| apply ICW_t; clear -H3; lia].
    destruct H3 as [H3|[H3|H3]];
      [ eapply (RK_tlow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK_tstat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK_thigh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)]; clear -H1 H2 H3; lia. }
  assert (DJctx : forall A k, al_ctx L <= A -> A + k <= al_ctx L + 4096 -> 0 <= k ->
            disjoint_from (Wr (bv_unsigned sp) RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 (al_t L) RI CA n ++ ic_W L 1 31) A k).
  { intros A k H1 H2 H3. apply dj_app; [| apply ICW_far; clear -H1 H2 H3 CL5; lia].
    pose proof CL1 as CL1'; unfold sclr, KLS in CL1'.
    eapply (RK_obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); atop_facts; clear -H1 H2 H3 CL1' CL2 CL5 SCX; lia. }
  (* [comment removed for export] *)
  assert (WF' : awf L st_r X').
  { subst st_r X' fr ca FL2. apply awf_refill; first [exact WF | exact HC | exact CNT0 | exact MUB | exact MUM' | exact NC0 | exact NCS | exact NEWB | exact NEWM | exact NEWMOD | exact N2 | clear -N NLE; lia]. }
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUALL | exact WMALL | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    repeat (apply Forall_cons; [cbn [fst snd]; first [apply DJimg; clear; lia | apply DJctx; clear; lia] |]). apply Forall_nil. }
  assert (EF : a_live st_r = a_live st /\ a_next st_r = a_next st /\ a_qloc st_r = a_qloc st /\ a_qloc_bytes st_r = a_qloc_bytes st
               /\ a_qglob st_r = a_qglob st /\ a_qglob_bytes st_r = a_qglob_bytes st /\ a_nsec st_r = a_nsec st /\ a_nres st_r = a_nres st
               /\ a_ptr_array st_r = a_ptr_array st /\ a_space_beg st_r = a_space_beg st).
  { subst st_r. destruct (put_cls_fields c (rrec mu' (au + ncnt * S) (nf + ncnt - n) mfa' n) (init_cache st)) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & _).
    rewrite P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, E1, E2, E3, E4, E5, E6, E7, E8, E9, E10. repeat split; reflexivity. }
  destruct EF as (EF1 & EF2 & EF3 & EF4 & EF5 & EF6 & EF7 & EF8 & EF9 & EF10).
  assert (INST' : ainstance L st_r m').
  { eapply ainstance_frame; [exact MUALL | exact WMALL | exact INST | exact EF8 | exact EF7 | | |]; apply DJimg; clear; unfold AINSTANCE; lia. }
  assert (THR' : athread L st_r X' m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0c | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia.
    - eapply cells_frame; [exact T40 | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia.
    - intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [exact ACc | exact (proj2 (proj2 (proj2 (proj2 (proj2 (CLS' c' Hc' NE))))))].
    - apply (junk_merge m' (al_t L + 2768) 24 8); [| | clear; lia | clear; lia].
      + destruct (junk_split m (al_t L + 2768) 24 8 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [J24 _].
        eapply junk_frame; [exact J24 | exact MUALL | exact WMALL | intros _; apply DJt; clear; lia].
      + replace (al_t L + 2768 + 24) with (al_t L + 2792) by (clear; lia). pose proof (junk_of_cells m' _ _ STM') as J. cbn in J. exact J.
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - eapply cells_frame; [exact UNW | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia. }
  (* [comment removed for export] *)
  assert (SHX : shlen 4294967296 = 536870912 /\ shad (RB + 4294967296) = shad RB + 536870912 /\ SHF1 <= shad RB + 536870912).
  { split; [rewrite shlen_div; reflexivity|]. clear -SH9 SH10 SH13. split; lia. }
  destruct SHX as (SX1 & SX2 & SX3).
  pose proof (ao_space L ALO) as RSP.
  set (WH := [(bv_unsigned sp - 672, bv_unsigned sp); (al_t L + 208, al_t L + 3168); (RI, RI + 128); (RB + mu, RB + 4294967296); (SHU0, shad RB + 536870912)]).
  assert (MUH : munch WH m m').
  { eapply munch_weaken; [| exact MUALL]. unfold sub_fp. intros x Hx. subst WH. cbn [outside] in Hx. destruct Hx as (O1 & O2 & O3 & O4 & O5 & _).
    apply outside_app. split.
    - cbn [outside]. clear -O1 O2 O3 O4 O5 SX3 SH2 SH3 SH12 SH5 SH6 MUB NEWB A5 A1 CAE RBE FAE HC N.
      repeat split; try exact I; lia.
    - apply ic_W_outside; [unfold acache_addr; clear -O2; lia | clear; cbn; lia | clear; lia]. }
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  assert (QU : quar_untouched L X WH).
  { unfold quar_untouched. subst WH. unfold AINSTANCE in *.
    repeat (apply Forall_cons; [cbn [fst snd];
      split; [clear -CEIL LO TL1u TL4u TL2 TSP SP1 SP2 RIE RBE HC MUB A1 SH1 SH2 SH9 SH11; lia|];
      split; [clear -CEIL LO TL1u TL4u TL2 TSP SP1 SP2 RIE RBE HC MUB A1 SH1 SH2 SH9 SH11; lia|];
      split; [clear -CEIL LO TL1u TL4u TL2 TSP SP1 SP2 RIE RBE HC MUB A1 SH1 SH2 SH9 SH11; lia|];
      split; [clear -CEIL LO TL1u TL4u TL2 TSP SP1 SP2 RIE RBE HC MUB A1 SH1 SH2 SH9 SH11; lia|];
      intros b Hb; destruct (BB b Hb) as (Bb1 & Bb2 & Bb3); destruct (xb_st b); [exact I| |];
      clear -Bb1 Bb2 Bb3 CEIL LO TL1u TL4u TL2 TSP SP1 SP2 RIE RBE HC MUB A1 SH1 SH2 SH9 SH11; lia |]).
    apply Forall_nil. }
  assert (QSM : quar_same st st_r X X').
  { unfold quar_same. rewrite EF3, EF4, EF5, EF6, EF10. repeat (split; [reflexivity|]). subst X'. unfold xr. cbn [x_busy].
    split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb]. }
  assert (HQ' : ah_quar H L st_r X' m').
  { eapply (hq_frame _ HL L st st_r X X' m m'); [exact HQ | exact MUH | exact WMALL | exact QU | exact QSM]. }
  assert (SU : sec_untouched L WH).
  { unfold sec_untouched, aknown. subst WH. unfold AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    (* [comment removed for export] *)
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha CEIL LO; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha TL1u TL4u TL2; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RIE HC; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RBE HC MUB A1; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha HC SH1 SH2 SH9 SH10 SH11; lia |].
    apply Forall_nil. }
  assert (SSM : sec_same st st_r).
  { unfold sec_same. rewrite EF7, EF8, EF9, EF1. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros; tauto|].
    rewrite (sec_chunks_of_eq st st_r EF1 EF3 EF5). apply Permutation_refl. }
  assert (HS' : ah_sec H L st_r X' m').
  { eapply (hs_frame _ HL L st st_r X X' m m'); [exact HS | exact MUH | exact WMALL | exact SU | exact SSM]. }
  assert (HD' : ah_depot H L m').
  { eapply (hd_frame _ HL L m m'); [exact HD | exact MUH | exact WMALL |]. subst WH.
    pose proof (ao_nodes L ALO) as (_ & ON1 & ON3 & ONs & _). pose proof (ao_store L ALO) as (_ & OS1 & OS3 & OSs & _). unfold sclr, KLS in ONs, OSs.
    pose proof (ad_nodes_res L ALO) as DNR. pose proof (ad_store_res L ALO) as DSR. pose proof (ad_t_nodes L ALO) as DTN. pose proof (ad_t_store L ALO) as DTS.
    unfold adisj in *.
    (* [comment removed for export] *)
    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; split; [| split];
      [ clear -Ha CEIL LO TL4u TL2 SP1 SP2 RSP RIE RBE HC MUB A1 SH1 SH2 SH9 SH11; lia
      | clear -Ha CEIL LO TL2 SP1 SP2 RSP RIE RBE HC MUB A1 SH1 SH2 SH9 SH11 ON1 ON3 ONs DNR DTN; lia
      | clear -Ha CEIL LO TL2 SP1 SP2 RSP RIE RBE HC MUB A1 SH1 SH2 SH9 SH11 OS1 OS3 OSs DSR DTS; lia ] |]). apply Forall_nil. }
  assert (AR' : AREP H L st_r X' m').
  { split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split.
    { intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE].
      - split; [exact RCc|]. split; [exact FAc|]. split; [exact SLc| exact SSc].
      - destruct (CLS' c' Hc' NE) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6). split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3| exact Y4]. }
    split; [exact HQ'|]. split; [exact HS'|]. split; [exact HD'|].
    split; [eapply arelro_frame; [exact MUALL | exact HRO | apply DJimg; clear; unfold ARELRO_LO, ARELRO_HI; lia]|].
    split; [eapply arep_rt2_frame; [exact MUALL | exact WMALL | exact RT2 | | |]; apply DJimg; clear; lia|].
    split; [| eapply arep_rt3_frame; [exact MUALL | exact WMALL | exact RT3 |]; unfold rt3_hulls;
              repeat (apply Forall_cons; [cbn [fst snd]; apply DJimg; clear; lia |]); apply Forall_nil].
    intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [exact AVc | exact (proj1 (proj2 (proj2 (proj2 (proj2 (CLS' c' Hc' NE))))))]. }
  (* [comment removed for export] *)
  assert (ARNG' : arng L RNG' st_r).
  { pose proof (arng_mono L RNG RNG' st FPLE ARNG) as AM.
    destruct AM as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & GC & GPA & GSC & GPSH).
    unfold arng. split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|].
    split; [exact G6|]. split; [exact G7|]. split; [exact G8|]. split; [exact G9|].
    split; [| split; [rewrite EF8; exact GPA| split; [rewrite (sec_chunks_of_eq st st_r EF1 EF3 EF5); exact GSC| exact GPSH]]].
    intros c' Hc'. cbv zeta. destruct (Z.eq_dec c' c) as [->|NE].
    - rewrite GR. cbn [c_mapped_user c_mapped_free_array rrec].
      destruct (GC c HC) as (R1 & R2 & R3 & R4).
      change (aregion L c) with RB in R1, R2 |- *. change (afreearr L c) with FA in R3, R4 |- *.
      change (c_mapped_user (get_cls st c)) with mu in R1, R2. change (c_mapped_free_array (get_cls st c)) with mfa in R3, R4.
      split; [| split; [| split]].
      + destruct UD as [Emu|(_ & _ & _ & _ & _ & RU & RSU & BW)]; [rewrite Emu; exact R1|].
        replace mu' with (mu + (mu' - mu)) by (clear; lia). apply rng_merge; [exact BW | clear -A1; lia | clear -MUB; lia | exact R1 | exact RU].
      + destruct UD as [Emu|(_ & _ & _ & _ & _ & RU & RSU & BW)]; [rewrite Emu; exact R2|].
        replace (shlen mu') with (shlen mu + shlen (mu' - mu)) by (rewrite !shlen_div; clear -M8a M8b; Z.div_mod_to_equations; lia).
        apply rng_merge; [exact BW | rewrite shlen_div; clear -A1; Z.div_mod_to_equations; lia | rewrite shlen_div; clear -MUB; Z.div_mod_to_equations; lia | exact R2 |].
        rewrite SHE3. exact RSU.
      + destruct FD as [Emfa|(_ & _ & _ & RF & RSF & BW)]; [rewrite Emfa; exact R3|].
        replace mfa' with (mfa + (mfa' - mfa)) by (clear; lia). apply rng_merge; [exact BW | clear -A5 A6; lia | clear -NEWM; lia | exact R3 | exact RF].
      + destruct FD as [Emfa|(_ & _ & _ & RF & RSF & BW)]; [rewrite Emfa; exact R4|].
        replace (shlen mfa') with (shlen mfa + shlen (mfa' - mfa)) by (rewrite !shlen_div; clear -M8c M8d; Z.div_mod_to_equations; lia).
        apply rng_merge; [exact BW | rewrite shlen_div; clear -A5 A6; Z.div_mod_to_equations; lia | rewrite shlen_div; clear -NEWM; Z.div_mod_to_equations; lia | exact R4 |].
        rewrite SHE4. exact RSF.
    - rewrite (GO c' NE). exact (GC c' Hc'). }
  (* [comment removed for export] *)
  exists X'.
  split; [exact AR'|]. split; [exact ARNG'|]. split; [exact CIR|].
  split; [rewrite GR; unfold max_count; rewrite CIR; cbn [c_count rrec]; subst n; reflexivity|].
  split; [unfold max_count; rewrite CIR; subst n; clear -N; lia|].
  split; [subst X'; reflexivity|].
  split; [intros c' NE; subst X'; apply xr_cls_ne; exact NE|].
  split; [exact EF1|]. split; [exact EF2|]. split; [exact EF3|]. split; [exact EF4|]. split; [exact EF5|]. split; [exact EF6|]. split; [exact EF7|]. split; [exact EF8|].
  split; [exact GO|].
  split; [| exact WMALL].
  eapply munch_weaken; [| exact MUH]. unfold sub_fp. intros x Hx. subst WH. unfold K_REGION in Hx. change (2^32) with 4294967296 in Hx.
  rewrite SX1 in Hx. cbn [outside] in Hx |- *. clear -Hx. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithStore.
Hypothesis STORE : store_refill_stmt.

Theorem arefill_from_store : refill_stmt H.
Proof.
  unfold refill_stmt.
  intros R k Q L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st X c lo
         ALO ARNG AR MI ST CEIL LO TP Ha0 Ha1 Ha2 Ha3 HC CNT0 RSTK KONT.
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  destruct THR as (T0c & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  destruct (CLS c HC) as (RCELLS & FARR & SLOTS & SSH). destruct (AVL c HC) as [AZU AZF].
  destruct RCELLS as (MTX16 & REG & RJ4 & EXH & RJ56). destruct FARR as (FL & FJ & FSJ).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof TL1 as TL1u; unfold sclr, KLS in TL1u. pose proof TL4 as TL4u; unfold iclr, AIMG_LO, AIMG_HI in TL4u.   (* [comment removed for export] *)
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof CL1 as CL1u; unfold sclr, KLS in CL1u.   (* [comment removed for export] *)
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof ARNG as ARNG0. destruct ARNG0 as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDTLS & RCLS & RPA & RSECS & RPSH).
  destruct (RCLS c HC) as (RREG & RSREG & RFA & RSFA).
  pose proof RT as RT0.
  destruct RT0 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
                    & PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
  destruct RT2 as (DPM & MLIM & RWCS).
  destruct INST as (I32 & I48 & I64 & I72 & I112 & I680 & I984 & I40 & I56).
  (* [comment removed for export] *)
  assert (MC : m3_cells L m).
  { unfold m3_cells, poison_cells, rmap_cells, AINSTANCE in *. repeat lazymatch goal with |- _ /\ _ => split end; assumption. }
  pose proof MTX16 as MTX. rw_split MTX 1%nat MTX MTXb. clear MTXb.
  destruct (junk_split m (aregion_info L c + 72) 8 48 RJ56 ltac:(lia) ltac:(lia)) as [STN8 _]. destruct (c8_of_junk m _ STN8) as [stn STN].
  destruct (junk_split m (al_t L + 2768) 24 8 CSTATS ltac:(lia) ltac:(lia)) as [_ STM8].
  replace (al_t L + 2768 + 24) with (al_t L + 2792) in STM8 by lia. destruct (c8_of_junk m _ STM8) as [stm STM].
  destruct FJ as [fj FJ'].
  destruct (CACHES c HC) as [tail (RECc & CH & LCH)]. cbv zeta in CH.
  assert (XC0 : xc_cache (x_cls X c) = []).
  { destruct (xc_cache (x_cls X c)) as [|y l] eqn:E; [reflexivity|]. exfalso. rewrite ?E in LENC. cbn [length] in LENC. clear -LENC CNT0. lia. }
  rewrite XC0 in CH, LCH. cbn [map app length] in CH, LCH.
  assert (NFA : c_num_freed (get_cls st c) <= c_allocated_user (get_cls st c) / size_of_class c).
  { rewrite <- LENF. apply NoDup_bound_length.
    - apply NoDup_app_remove_r in ND. exact ND.
    - intros k0 Hk. apply RANGE. apply in_app_iff. left. exact Hk.
    - unfold ndist in RANGE. apply Z.div_pos; [lia|]. pose proof (size_of_class_facts c HC); lia. }
  pose proof (size_of_class_facts c HC) as [SZ16 SZM].
  assert (FL31 : Forall (fun w : word => bv_unsigned w < 2^31) (map (fun k => Z_to_bv 64 (acompact c k)) (xc_free (x_cls X c)))).
  { apply Forall_forall. intros w Hw. apply in_map_iff in Hw. destruct Hw as (k0 & <- & Hk).
    pose proof (RANGE k0 ltac:(apply in_app_iff; left; exact Hk)) as KR. unfold ndist in KR.
    assert (B : 0 <= acompact c k0 < 2^28).
    { unfold acompact. unfold K_FREEARR_OFF in A2. generalize KR A1 A2 SZ16 SZM; clear; intros. Z.div_mod_to_equations. nia. }
    rewrite unsigned_lit; lia. }
  eapply refill_spec with (lo := lo) (L := L) (st := st) (cnt := fun j => c_count (get_cls st j)) (sj := sj) (stm := stm) (stn := stn) (fj := fj)
                          (fl := map (fun k => Z_to_bv 64 (acompact c k)) (xc_free (x_cls X c))) (chunks0 := tail);
  try lazymatch goal with
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => exact ST
       | |- ATOP <= _ => exact CEIL
       | |- _ <= bv_unsigned _ - _ => clear -LO; lia
       | |- mem_inv _ _ => exact MI
       | |- m3_cells _ _ => exact MC
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- rw_cells _ _ (aregion_info _ _ + 68) _ => exact EXH
       | |- rw_cells _ _ (aregion_info _ _ + 72) _ => exact STN
       | |- rw_cells _ _ (afreearr _ _ + _) _ => exact FJ'
       | |- rw_cells _ _ (al_t _ + 2792) _ => exact STM
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ (afreearr _ _) _ => exact FL
       | |- u32arr _ _ _ _ => exact CH
       | |- Forall _ _ => exact FL31
       | |- length (map _ _) = _ => rewrite length_map; clear -LENF; lia
       | |- length _ = _ => first [exact LSJ | exact LCH]
       | |- azero _ (shad (aregion _ _ + _)) _ => exact AZU
       | |- azero _ (shad (afreearr _ _ + _)) _ => exact AZF
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => eapply rng_sub'; [exact RRI|]; unfold aregion_info, ARI_STRIDE, K_SPACE_EXTRA; clear -HC; unfold K_NUM_CLASSES in HC; lia
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ (al_ctx _) _ => eapply rng_sub'; [exact RCTX|]; clear; lia
       | |- rng _ (al_t _) _ => exact RT4
       | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3]
       | |- _ \/ _ => first [exact CL5 | exact TSP | clear -SCX; unfold K_SPACE_SIZE, K_SPACE_EXTRA in *; lia]
       | |- forall j, _ -> arec_hdr _ _ _ _ _ _ => intros j Hj; destruct (CACHES j ltac:(unfold K_NUM_CLASSES; clear -Hj; lia)) as [tl (RH & _ & _)]; exact RH
       | |- forall st2, _ => idtac
       end.
  all: lazymatch goal with
       | |- forall _, _ => idtac
       | _ => first [assumption | clear -A1 A2 A3 A4 A5 A6 A7 NFA HC SP1 SP2 SP3 TL1u TL4u TL2 TL3 CL1 CL1u CL2 CNT0; unfold K_NUM_CLASSES in *; lia]
       end.
  (* [comment removed for export] *)
  intros st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' RR.
  destruct (STORE L RNG RNG' sp m m' st st2 X c lo tail ALO ARNG AR HC CNT0 CEIL LO CH LCH RR)
    as (X' & AR' & ARNG' & CIN & CCNT & NPOS & XB & XC & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & GC & MU & WM).
  destruct RR as (m1 & _ & _ & TR & _).
  destruct TR as (FPLE & mu' & mfa' & ncnt & sj' & stm' & stn' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MIT & STT & _).
  unfold KKref. rewrite (take_is_apop c (max_cached c / 2) st2).
  eapply KONT. unfold ARefill_iface.refill_ret. split; [exact FPLE|]. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIT|]. split; [exact STT|]. split; [exact AR'|]. split; [exact ARNG'|].
  split; [exact CIN|]. split; [exact CCNT|]. split; [exact NPOS|]. split; [exact XB|]. split; [exact XC|].
  split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5|]. split; [exact L6|]. split; [exact L7|]. split; [exact L8|].
  exact GC.
Qed.
End WithStore.

(* [comment removed for export] *)
Theorem arefillP : refill_stmt H.
Proof. exact (arefill_from_store refill_store). Qed.
End RefillP.
End CANSEC1.
