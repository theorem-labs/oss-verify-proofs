(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout.
Import ListNotations.
Open Scope Z_scope.

Notation INSTANCE := 724696%Z.
Notation K_REGION := 4294967296%Z.
Notation FA_OFF := 3758096384%Z.
Notation K_FA_SIZE := 536870912%Z.
Notation K_MAP := 262144%Z.
Notation CACHE_OFF := 208%Z.
Notation CSTATS_OFF := 2768%Z.
Notation TSTATS_OFF := 2800%Z.
Notation KWL := 1152921504606846976%Z.

Definition class_size (c : Z) : Z :=
  if c =? 31 then 64
  else if c <=? 16 then 32 * c
  else let c' := c - 16 in let t := Z.shiftl 512 (Z.shiftr c' 1) in t + (Z.shiftr t 1) * (Z.land c' 1).
Definition max_count (c : Z) : Z := 2 * Z.max 1 (Z.min 8 (1024 / class_size c)).
Definition rup (x a : Z) : Z := ((x + a - 1) / a) * a.

Example class_size_samples : map class_size [1; 2; 16; 17; 18; 19; 24; 30; 31] = [32; 64; 512; 768; 1024; 1536; 8192; 65536; 64].
Proof. reflexivity. Qed.
Example max_count_samples : map max_count [1; 4; 5; 6; 7; 9; 11; 17; 24; 30; 31] = [16; 16; 12; 10; 8; 6; 4; 2; 2; 2; 16].
Proof. reflexivity. Qed.

Lemma range_check : forall (f : Z -> bool) (lo : Z) (n : nat),
  forallb f (map (fun i => lo + Z.of_nat i) (seq 0 n)) = true -> forall c, lo <= c < lo + Z.of_nat n -> f c = true.
Proof.
  intros f lo n H c Hc. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat (c - lo)). split; [lia|].
  apply in_seq. lia.
Qed.
Lemma class_size_pos : forall c, 1 <= c <= 31 -> 32 <= class_size c <= 65536.
Proof.
  intros c Hc. pose proof (range_check (fun c => (32 <=? class_size c) && (class_size c <=? 65536)) 1 31 ltac:(vm_compute; reflexivity) c ltac:(lia)) as H.
  cbn beta in H. apply andb_true_iff in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
Lemma class_size_mod16 : forall c, 1 <= c <= 31 -> class_size c mod 16 = 0.
Proof.
  intros c Hc. pose proof (range_check (fun c => class_size c mod 16 =? 0) 1 31 ltac:(vm_compute; reflexivity) c ltac:(lia)) as H.
  cbn beta in H. apply Z.eqb_eq in H. exact H.
Qed.
Lemma max_count_range : forall c, 1 <= c <= 31 -> 2 <= max_count c <= 16 /\ max_count c mod 2 = 0.
Proof.
  intros c Hc. pose proof (range_check (fun c => (2 <=? max_count c) && (max_count c <=? 16) && (max_count c mod 2 =? 0)) 1 31 ltac:(vm_compute; reflexivity) c ltac:(lia)) as H.
  cbn beta in H. apply andb_true_iff in H. destruct H as [H H3]. apply andb_true_iff in H. destruct H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.eqb_eq in H3. lia.
Qed.

Record pclass := mkPCL {
  p_nf : Z;
  p_mfa : Z;
  p_au : Z;
  p_mu : Z;
  p_nalloc : Z;
  p_nfreed : Z;
  p_fa : list Z;
  p_cnt : Z;
  p_chunks : list Z
}.
Definition pclass0 : pclass := mkPCL 0 0 0 0 0 0 [] 0 [].

Record prim := mkPRIM {
  pr_cls : list pclass;
  pr_inited : bool;
  pr_calloc : Z;
  pr_cmapped : Z
}.
Definition get_cls (P : prim) (c : Z) : pclass := nth (Z.to_nat c) (pr_cls P) pclass0.
Fixpoint set_nth {A} (i : nat) (x : A) (l : list A) : list A :=
  match l, i with [], _ => [] | _ :: t, O => x :: t | h :: t, S i' => h :: set_nth i' x t end.
Definition set_cls (P : prim) (c : Z) (k : pclass) : prim := mkPRIM (set_nth (Z.to_nat c) k (pr_cls P)) (pr_inited P) (pr_calloc P) (pr_cmapped P).

Definition efa_new (k : pclass) (total : Z) : Z := if 4 * total <=? p_mfa k then p_mfa k else rup (4 * total) K_MAP.
Definition ensure_fa (k : pclass) (total : Z) : pclass :=
  mkPCL (p_nf k) (efa_new k total) (p_au k) (p_mu k) (p_nalloc k) (p_nfreed k) (p_fa k) (p_cnt k) (p_chunks k).

Definition pop_mu (k : pclass) (c requested : Z) : Z :=
  let total := p_au k + requested * class_size c in
  if total <=? p_mu k then p_mu k else p_mu k + rup (total - p_mu k) K_MAP.
Definition pop_new (k : pclass) (c requested : Z) : Z := (pop_mu k c requested - p_au k) / class_size c.
Definition carve (au sz : Z) (n : nat) : list Z := rev (map (fun i => (au + Z.of_nat i * sz) / 16) (seq 0 n)).
Definition populate (k : pclass) (c requested : Z) : pclass :=
  let mu' := pop_mu k c requested in let sz := class_size c in
  let newc := pop_new k c requested in
  let k1 := ensure_fa (mkPCL (p_nf k) (p_mfa k) (p_au k) mu' (p_nalloc k) (p_nfreed k) (p_fa k) (p_cnt k) (p_chunks k)) (p_nf k + newc) in
  mkPCL (p_nf k + newc) (p_mfa k1) (p_au k + newc * sz) mu' (p_nalloc k) (p_nfreed k)
        (p_fa k ++ carve (p_au k) sz (Z.to_nat newc)) (p_cnt k) (p_chunks k).

Definition gfa_pre (k : pclass) (c n : Z) : pclass := if p_nf k <? n then populate k c (n - p_nf k) else k.
Definition get_from_allocator (k : pclass) (c n : Z) : pclass * list Z :=
  let k1 := gfa_pre k c n in
  let base := p_nf k1 - n in
  (mkPCL base (p_mfa k1) (p_au k1) (p_mu k1) (p_nalloc k1 + n) (p_nfreed k1) (firstn (Z.to_nat base) (p_fa k1)) (p_cnt k1) (p_chunks k1),
   skipn (Z.to_nat base) (p_fa k1)).

Definition refill (k : pclass) (c : Z) : pclass :=
  let n := max_count c / 2 in let '(k1, got) := get_from_allocator k c n in
  mkPCL (p_nf k1) (p_mfa k1) (p_au k1) (p_mu k1) (p_nalloc k1) (p_nfreed k1) (p_fa k1) n got.
Definition cache_alloc_cls (k : pclass) (c : Z) : pclass * Z :=
  let k1 := if p_cnt k =? 0 then refill k c else k in
  (mkPCL (p_nf k1) (p_mfa k1) (p_au k1) (p_mu k1) (p_nalloc k1) (p_nfreed k1) (p_fa k1) (p_cnt k1 - 1) (firstn (Z.to_nat (p_cnt k1 - 1)) (p_chunks k1)),
   nth (Z.to_nat (p_cnt k1 - 1)) (p_chunks k1) 0).
Definition cache_alloc (P : prim) (c : Z) : prim * Z :=
  let '(k1, v) := cache_alloc_cls (get_cls P c) c in
  (mkPRIM (set_nth (Z.to_nat c) k1 (pr_cls P)) true (pr_calloc P + class_size c) (pr_cmapped P + (p_mu k1 - p_mu (get_cls P c))), v).

Definition return_to_allocator (k : pclass) (vals : list Z) : pclass :=
  let n := Z.of_nat (length vals) in let k1 := ensure_fa k (p_nf k + n) in
  mkPCL (p_nf k + n) (p_mfa k1) (p_au k) (p_mu k) (p_nalloc k) (p_nfreed k + n) (p_fa k ++ vals) (p_cnt k) (p_chunks k).
Definition cache_dealloc_cls (k : pclass) (c v : Z) : pclass :=
  let k1 := if p_cnt k =? max_count c
            then let h := max_count c / 2 in
                 let kr := return_to_allocator k (skipn (Z.to_nat (p_cnt k - h)) (p_chunks k)) in
                 mkPCL (p_nf kr) (p_mfa kr) (p_au kr) (p_mu kr) (p_nalloc kr) (p_nfreed kr) (p_fa kr) (p_cnt k - h) (firstn (Z.to_nat (p_cnt k - h)) (p_chunks k))
            else k in
  mkPCL (p_nf k1) (p_mfa k1) (p_au k1) (p_mu k1) (p_nalloc k1) (p_nfreed k1) (p_fa k1) (p_cnt k1 + 1) (p_chunks k1 ++ [v]).
Definition cache_dealloc (P : prim) (c v : Z) : prim :=
  mkPRIM (set_nth (Z.to_nat c) (cache_dealloc_cls (get_cls P c) c v) (pr_cls P)) true (pr_calloc P - class_size c) (pr_cmapped P).

Definition pclass_wf (c : Z) (k : pclass) : Prop :=
  let sz := class_size c in
  p_nf k = Z.of_nat (length (p_fa k)) /\ p_cnt k = Z.of_nat (length (p_chunks k)) /\ 0 <= p_cnt k <= max_count c
  /\ 4 * p_nf k <= p_mfa k /\ 0 <= p_mfa k <= K_FA_SIZE /\ p_mfa k mod K_MAP = 0
  /\ 0 <= p_au k <= p_mu k /\ p_mu k <= FA_OFF /\ p_mu k mod K_MAP = 0 /\ p_au k mod sz = 0 /\ p_mu k - p_au k < sz + K_MAP
  /\ NoDup (p_fa k ++ p_chunks k)
  /\ Forall (fun v => 0 <= v /\ 16 * v + sz <= p_au k /\ (16 * v) mod sz = 0) (p_fa k ++ p_chunks k)
  /\ 0 <= p_nalloc k /\ 0 <= p_nfreed k.

Section R.
Context {HC : HasCeiling}.
Variable AL : alayout.
Notation SPACE := (al_space AL).
Notation THR := (at_thr (al_thread AL)).
Definition RIB : Z := al_space AL + K_SPACE.
Definition region (c : Z) : Z := al_space AL + c * K_REGION.
Definition fa_base (c : Z) : Z := region c + FA_OFF.
Definition pcl_addr (c : Z) : Z := at_thr (al_thread AL) + CACHE_OFF + 80 * c.
Definition ri_addr (c : Z) : Z := RIB + 128 * c.

Definition prim_env (m : mem) : Prop :=
  rw_cells asegs m 724728   [C8 (wz (al_space AL)); C4 (wz 4294967295); C4 (wz 0); C8 (wz RIB); C1 (Z_to_bv 8 0)].

Definition ri_cells (mtx : Z) (k : pclass) (j8 j64 j88 j96 j104 j112 : word) (jpad : list byte) : list cell :=
  [C8 (wz mtx); C8 j8; C8 (wz (p_nf k)); C8 (wz (p_mfa k)); C8 (wz (p_au k)); C8 (wz 0); C8 (wz (p_mu k)); C8 (wz 0);
   C4 j64; C1 (Z_to_bv 8 0); CB 3 jpad; C8 (wz (p_nalloc k)); C8 (wz (p_nfreed k)); C8 j88; C8 j96; C8 j104; C8 j112; CB 8 (repeat (Z_to_bv 8 0) 8)].
Definition ri_rep (m : mem) (c : Z) (k : pclass) : Prop :=
  exists j8 j64 j88 j96 j104 j112 jpad, rw_cells asegs m (ri_addr c) (ri_cells 0 k j8 j64 j88 j96 j104 j112 jpad).

Definition pcl_rep (m : mem) (inited : bool) (c : Z) (k : pclass) : Prop :=
  rw_cells asegs m (pcl_addr c) [C4 (wz (p_cnt k)); C4 (wz (if inited then max_count c else 0)); C8 (wz (if inited then class_size c else 0))]
  /\ exists ws, u32arr asegs m (pcl_addr c + 16) ws /\ length ws = 16%nat /\ firstn (length (p_chunks k)) ws = map wz (p_chunks k).

Definition fa_rep (m : mem) (c : Z) (k : pclass) : Prop :=
  exists ws, u32arr asegs m (fa_base c) ws /\ 4 * Z.of_nat (length ws) = p_mfa k /\ firstn (length (p_fa k)) ws = map wz (p_fa k).

Definition tail_rep (m : mem) (c : Z) (k : pclass) : Prop :=
  (exists j, rw_cells asegs m (region c + p_au k) [CB (Z.to_nat (p_mu k - p_au k)) j])
  /\ rw_cells asegs m (sh (region c + p_au k)) [CB (Z.to_nat ((p_mu k - p_au k) / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat ((p_mu k - p_au k) / 8)))].

Definition free_chunk (m : mem) (c v : Z) : Prop :=
  (exists j, rw_cells asegs m (region c + 16 * v) [CB (Z.to_nat (class_size c)) j])
  /\ rw_cells asegs m (sh (region c + 16 * v)) [CB (Z.to_nat (class_size c / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat (class_size c / 8)))].

Definition cls_rep (m : mem) (inited : bool) (c : Z) (k : pclass) : Prop :=
  pclass_wf c k /\ ri_rep m c k /\ pcl_rep m inited c k /\ fa_rep m c k /\ tail_rep m c k
  /\ (forall v, In v (p_fa k ++ p_chunks k) -> free_chunk m c v).

Definition RPRIM (P : prim) (m : mem) : Prop :=
  length (pr_cls P) = 32%nat /\ prim_env m
  /\ (forall c, 1 <= c <= 31 -> cls_rep m (pr_inited P) c (get_cls P c))
  /\ rw_cells asegs m (at_thr (al_thread AL) + CSTATS_OFF + 16) [C8 (wz (pr_calloc P)); C8 (wz (pr_cmapped P))]
  /\ (exists ts, rw_cells asegs m (at_thr (al_thread AL) + TSTATS_OFF) [CB 368 ts]).

Definition pcl_fam (m : mem) (P : prim) (ci : Z) : Prop :=
  forall c, 1 <= c <= 31 -> pcl_rep m (c <? ci) c (get_cls P c).

#[using="Type"] Lemma pcl_fam_inited : forall m P, pcl_fam m P 32 -> forall c, 1 <= c <= 31 -> pcl_rep m true c (get_cls P c).
Proof. intros m P F c Hc. specialize (F c Hc). replace (c <? 32) with true in F by (symmetry; apply Z.ltb_lt; lia). exact F. Qed.
#[using="Type"] Lemma pcl_fam_start : forall m P, (forall c, 1 <= c <= 31 -> pcl_rep m false c (get_cls P c)) -> pcl_fam m P 1.
Proof. intros m P F c Hc. replace (c <? 1) with false by (symmetry; apply Z.ltb_ge; lia). apply F. exact Hc. Qed.

#[using="Type"] Lemma pcl_fam_step : forall m m' P ci,
  pcl_fam m P ci -> 1 <= ci <= 31 ->
  munch [(pcl_addr ci + 4, pcl_addr ci + 16)] m m' -> wmono asegs m m' ->
  rw_cells asegs m' (pcl_addr ci) [C4 (wz (p_cnt (get_cls P ci))); C4 (wz (max_count ci)); C8 (wz (class_size ci))] ->
  pcl_fam m' P (ci + 1).
Proof.
  intros m m' P ci F Hci MU WM NEW c Hc. unfold pcl_addr in *.
  destruct (Z.eq_dec c ci) as [->|NE].
  - replace (ci <? ci + 1) with true by (symmetry; apply Z.ltb_lt; lia). split; [exact NEW|].
    destruct (F ci Hci) as [_ (ws & AR & L & FX)]. exists ws. split; [| split; assumption].
    eapply u32arr_transport; [exact AR| exact MU| exact WM|]. cbn [disjoint_from]. rewrite L. unfold pcl_addr. lia.
  - destruct (F c Hc) as [CE (ws & AR & L & FX)].
    replace (c <? ci + 1) with (c <? ci) by (destruct (Z.ltb_spec c ci), (Z.ltb_spec c (ci + 1)); try reflexivity; lia).
    split.
    + eapply rw_cells_transport; [exact CE| exact MU| exact WM|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. unfold pcl_addr. lia.
    + exists ws. split; [| split; assumption].
      eapply u32arr_transport; [exact AR| exact MU| exact WM|]. cbn [disjoint_from]. rewrite L. unfold pcl_addr. lia.
Qed.

#[using="Type"] Lemma region_range : forall c, 1 <= c <= 31 -> al_space AL + K_REGION <= region c /\ region c + K_REGION <= al_space AL + K_SPACE.
Proof. intros c Hc. unfold region. change K_SPACE with (32 * K_REGION). nia. Qed.
End R.
