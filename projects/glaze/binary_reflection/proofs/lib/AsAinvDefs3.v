(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.RunLim OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BackingAlgebra.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Cells.
  Variable SEGS : list Segment.
  Definition cellZ (M : mem) (a : Z) (n : nat) (v : Z) : Prop := cellN SEGS M a n v.
  Definition byteZ (M : mem) (a : Z) (b : Z) : Prop := cellN SEGS M a 1 b.
  (* [comment removed for export] *)
  Definition writableZ (M : mem) (lo hi : Z) : Prop :=
    forall i, lo <= i < hi -> M (Z_to_bv 64 i) <> None /\ store_ok SEGS M (Z_to_bv 64 i) 1%nat = true.
  (* [comment removed for export] *)
  Definition fillZ (M : mem) (lo hi : Z) (b : Z) : Prop := forall i, lo <= i < hi -> byteZ M i b.
  (* [comment removed for export] *)
  Definition cells_hold (M : mem) (cs : list (Z * nat * Z)) : Prop :=
    Forall (fun c => cellZ M (fst (fst c)) (snd (fst c)) (snd c)) cs.
End Cells.

(* [comment removed for export] *)
Lemma w_succ : forall a, 0 <= a -> a + 1 < 2 ^ 64 -> (Z_to_bv 64 a + 1)%bv = Z_to_bv 64 (a + 1).
Proof.
  intros a H0 H1. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  change (bv_unsigned (1 : bv 64)) with 1.
  (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap, bv_modulus in G in change_no_check G' end). change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite (Z.mod_small a) by lia. rewrite !Z.mod_small by lia. reflexivity.
Qed.

Lemma rdn_S : forall segs M (a : word) n,
  rdn segs M a (S n) = match rdn segs M a 1 with
                       | Some [b] => match rdn segs M (a + 1)%bv n with Some r => Some (b :: r) | None => None end
                       | _ => None end.
Proof.
  intros segs M a n. (lazymatch goal with |- ?G => let G' := eval cbn [rdn] in G in change_no_check G' end).
  destruct (match M a with Some b => Some b | None => seg_rom segs a end); reflexivity.
Qed.

Lemma w2le_zero : forall n, word_to_le_bytes n (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) n.
Proof.
  intros n. (lazymatch goal with |- ?G => let G' := eval unfold word_to_le_bytes in G in change_no_check G' end). rewrite Z_to_bv_unsigned. change (bv_wrap 64 0) with 0.
  induction n as [|n IH]; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); [reflexivity|]. rewrite Z.shiftr_0_l. rewrite IH. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fill_cellN_zero : forall segs M lo hi, (forall i, lo <= i < hi -> cellN segs M i 1 0) ->
  forall n a, lo <= a -> a + Z.of_nat n <= hi -> 0 <= lo -> hi < 2 ^ 64 -> cellN segs M a n 0.
Proof.
  intros segs M lo hi F n. induction n as [|n IH]; intros a Ha Hn L0 Hhi.
  - (lazymatch goal with |- ?G => let G' := eval unfold cellN in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). reflexivity.
  - unfold cellN in *. rewrite rdn_S. pose proof (F a ltac:(lia)) as F1. unfold cellN in F1. cbn [word_to_le_bytes Z_to_le_bytes] in F1.
    rewrite F1. rewrite w_succ by lia. rewrite (IH (a + 1)) by lia.
    rewrite !w2le_zero. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cellN_frame : forall segs M M' a n v, cellN segs M a n v -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  (forall i, a <= i < a + Z.of_nat n -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> cellN segs M' a n v.
Proof.
  intros segs M M' a n v H Ha Hn EQ. unfold cellN in *. rewrite <- H. apply rdn_ext.
  - rewrite (u_Z2bv a); lia.
  - intros x Hx. rewrite (u_Z2bv a) in Hx by lia.
    pose proof (u64_range x) as R. replace x with (Z_to_bv 64 (bv_unsigned x)).
    + apply EQ. lia.
    + apply bv_eq. rewrite u_Z2bv by lia. reflexivity.
Qed.

Lemma store_ok1_some : forall segs M (a : word), M a <> None -> store_ok segs M a 1%nat = true.
Proof.
  intros segs M a H. (lazymatch goal with |- ?G => let G' := eval cbn [store_ok] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold wview in G in change_no_check G' end). destruct (M a); [reflexivity | exfalso; exact (H eq_refl)].
Qed.

Section CellFrames.
  Variable SEGS : list Segment.
  Lemma cellZ_frame : forall M M' a n v, cellZ SEGS M a n v -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
    (forall i, a <= i < a + Z.of_nat n -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> cellZ SEGS M' a n v.
  Proof. intros. unfold cellZ in *. eapply cellN_frame; eauto. Qed.
  Lemma byteZ_frame : forall M M' a b, byteZ SEGS M a b -> 0 <= a -> a + 1 < 2 ^ 64 ->
    M' (Z_to_bv 64 a) = M (Z_to_bv 64 a) -> byteZ SEGS M' a b.
  Proof. intros M M' a b H Ha Hn EQ. unfold byteZ in *. eapply cellN_frame; eauto. intros i Hi. replace i with a by lia. exact EQ. Qed.
  Lemma fillZ_frame : forall M M' lo hi b, fillZ SEGS M lo hi b -> 0 <= lo -> hi < 2 ^ 64 ->
    (forall i, lo <= i < hi -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> fillZ SEGS M' lo hi b.
  Proof. intros M M' lo hi b H Hlo Hhi EQ i Hi. eapply byteZ_frame; [exact (H i Hi) | lia | lia | apply EQ; lia]. Qed.
  (* [comment removed for export] *)
  Lemma writableZ_frame : forall M M' lo hi, writableZ SEGS M lo hi ->
    (forall i, lo <= i < hi -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i) \/ M' (Z_to_bv 64 i) <> None) -> writableZ SEGS M' lo hi.
  Proof.
    intros M M' lo hi W EQ i Hi. destruct (W i Hi) as [D S]. destruct (EQ i Hi) as [E | NN].
    - split; [rewrite E; exact D|]. revert S. (lazymatch goal with |- ?G => let G' := eval cbn [store_ok] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold wview in G in change_no_check G' end). rewrite E. intros S; exact S.
    - split; [exact NN|]. apply store_ok1_some. exact NN.
  Qed.
  Lemma cells_hold_frame : forall M M' cs, cells_hold SEGS M cs ->
    Forall (fun c => 0 <= fst (fst c) /\ fst (fst c) + Z.of_nat (snd (fst c)) < 2 ^ 64) cs ->
    (forall c i, In c cs -> fst (fst c) <= i < fst (fst c) + Z.of_nat (snd (fst c)) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    cells_hold SEGS M' cs.
  Proof.
    intros M M' cs H R EQ. unfold cells_hold in *. rewrite Forall_forall in *. intros c Hc.
    destruct (R c Hc) as [R1 R2]. apply (cellZ_frame M M'); [exact (H c Hc) | exact R1 | exact R2 |]. intros i Hi. exact (EQ c i Hc Hi).
  Qed.
End CellFrames.

(* [comment removed for export] *)
Lemma fill_cellZ_zero : forall SEGS M lo hi, fillZ SEGS M lo hi 0 ->
  forall a n, lo <= a -> a + Z.of_nat n <= hi -> 0 <= lo -> hi < 2 ^ 64 -> cellZ SEGS M a n 0.
Proof. intros SEGS M lo hi F a n H1 H2 H3 H4. (lazymatch goal with |- ?G => let G' := eval unfold cellZ in G in change_no_check G' end). apply (fill_cellN_zero SEGS M lo hi F n a H1 H2 H3 H4). Qed.

(* [comment removed for export] *)
Definition in_ivz (l : list (word * word)) (a : Z) : Prop := exists b n, In (b, n) l /\ bv_unsigned b <= a < bv_unsigned b + bv_unsigned n.
(* [comment removed for export] *)
Definition pg_in_ivz (l : list (word * word)) (a : Z) : Prop := 0 <= a < 2 ^ 64 /\ page_in_ranges (page_base (Z_to_bv 64 a)) l = true.

Definition RoundUp (x m : Z) : Z := ((x + m - 1) / m) * m.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rz_log (n : Z) : Z :=
  if n <=? 48 then 0 else if n <=? 96 then 1 else if n <=? 448 then 2 else if n <=? 3968 then 3
  else if n <=? 16128 then 4 else if n <=? 32256 then 5 else if n <=? 64512 then 6 else 7.
Definition rz (n : Z) : Z := 16 * 2 ^ rz_log n.
Definition rounded (n : Z) : Z := RoundUp (Z.max n 8) 8.
Definition needed (n : Z) : Z := rounded n + rz n.                 (* [comment removed for export] *)
Definition is_primary (n : Z) : bool := needed n <=? 65536.       (* [comment removed for export] *)
(* [comment removed for export] *)
Definition sec_needed (n : Z) : Z := rounded n + 2 * rz n.
Definition sec_map_size (n : Z) : Z := RoundUp (sec_needed n) PG + PG.
Definition sec_user_off (n : Z) : Z := PG + rz n.                  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition pgdn (z : Z) : Z := z / PG * PG.
Definition pgup (z : Z) : Z := (z + (PG - 1)) / PG * PG.
Definition sec_hull_lo (mp : Z) : Z := pgdn (sh_lo mp).
Definition sec_hull_hi (mp n : Z) : Z := pgup (sh_hi mp (sec_map_size n)).
Definition sec_hull (mp n : Z) : Z := sec_hull_hi mp n - sec_hull_lo mp.
Definition sec_naa (mp n : Z) : list (Z * Z) := [(sec_hull_lo mp, sec_hull_hi mp n)].
Definition sec_inner_lo (mp : Z) : Z := pgup (sh_lo mp).
Definition sec_inner_hi (mp n : Z) : Z := pgdn (sh_hi mp (sec_map_size n)).
Definition sec_edges (mp n : Z) : list (Z * Z) := [(sec_hull_lo mp, sec_inner_lo mp); (sec_inner_hi mp n, sec_hull_hi mp n)].
Lemma pgdn_le : forall z, pgdn z <= z < pgdn z + PG.
Proof. intros z. (lazymatch goal with |- ?G => let G' := eval unfold pgdn, PG in G in change_no_check G' end). Z.div_mod_to_equations. lia. Qed.
Lemma pgup_ge : forall z, z <= pgup z < z + PG.
Proof. intros z. (lazymatch goal with |- ?G => let G' := eval unfold pgup, PG in G in change_no_check G' end). Z.div_mod_to_equations. lia. Qed.
Lemma pgdn_mod : forall z, pgdn z mod PG = 0.
Proof. intros z. (lazymatch goal with |- ?G => let G' := eval unfold pgdn, PG in G in change_no_check G' end). apply Z_mod_mult. Qed.
Lemma pgup_mod : forall z, pgup z mod PG = 0.
Proof. intros z. (lazymatch goal with |- ?G => let G' := eval unfold pgup, PG in G in change_no_check G' end). apply Z_mod_mult. Qed.
Lemma pgup_pgdn : forall z, pgup z = pgdn z \/ pgup z = pgdn z + PG.
Proof. intros z. (lazymatch goal with |- ?G => let G' := eval unfold pgup, pgdn, PG in G in change_no_check G' end). Z.div_mod_to_equations. lia. Qed.
Lemma sec_edges_bytes : forall mp n, 0 <= A_bytes (sec_edges mp n) <= 2 * PG.
Proof.
  intros mp n. (lazymatch goal with |- ?G => let G' := eval cbn [A_bytes sec_edges fst snd] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold sec_inner_lo, sec_inner_hi, sec_hull_lo, sec_hull_hi in G in change_no_check G' end).
  pose proof (pgup_pgdn (sh_lo mp)). pose proof (pgup_pgdn (sh_hi mp (sec_map_size n))). unfold PG in *. lia.
Qed.


(* [comment removed for export] *)
Definition csize (c : Z) : Z :=
  if c <=? 16 then 32 * c
  else let t := 512 * 2 ^ ((c - 16) / 2) in if Z.odd (c - 16) then t + t / 2 else t.
(* [comment removed for export] *)
Definition class_of (s : Z) : Z :=
  if s <=? 512 then (s + 31) / 32
  else if s <=? 768 then 17 else if s <=? 1024 then 18 else if s <=? 1536 then 19 else if s <=? 2048 then 20
  else if s <=? 3072 then 21 else if s <=? 4096 then 22 else if s <=? 6144 then 23 else if s <=? 8192 then 24
  else if s <=? 12288 then 25 else if s <=? 16384 then 26 else if s <=? 24576 then 27 else if s <=? 32768 then 28
  else if s <=? 49152 then 29 else 30.

Definition BATCHCLASS : Z := 24.
Definition BATCHSZ : Z := 8192.
Definition BATCHCAP : Z := 1021.
(* [comment removed for export] *)
Definition cache_hint (c : Z) : Z := Z.max 1 (Z.min 8 (1024 / csize c)).
Definition cache_max (c : Z) : Z := 2 * cache_hint c.

(* [comment removed for export] *)
Definition KREGION : Z := 2 ^ 32.
Definition KSPACE : Z := 2 ^ 37.
Definition KUSERMAP : Z := 2 ^ 18.
Definition KFAMAP : Z := 2 ^ 18.
Definition KFAOFF : Z := 0xE0000000.
Definition KREGION_EXHAUST : Z := 0xE0000000.                    (* [comment removed for export] *)
Definition region_beg (spacebeg c : Z) : Z := spacebeg + c * KREGION.
Definition fa_beg (spacebeg c : Z) : Z := region_beg spacebeg c + KFAOFF.
(* [comment removed for export] *)
Definition chunk_addr (spacebeg c j : Z) : Z := region_beg spacebeg c + j * csize c.
(* [comment removed for export] *)
Definition compact_of (spacebeg c a : Z) : Z := (a - region_beg spacebeg c) / 16.
Definition chunk_of_compact (spacebeg c k : Z) : Z := region_beg spacebeg c + 16 * k.

(* [comment removed for export] *)
Definition prim_alloc_beg (p n : Z) : Z := p - rz n.


(* [comment removed for export] *)
Record depot := DEP {
  dp_nids : Z;                       (* [comment removed for export] *)
  dp_tab : Z -> Z;                   (* [comment removed for export] *)
  dp_hash : Z -> Z; dp_link : Z -> Z; dp_store : Z -> Z;   (* [comment removed for export] *)
  dp_nodeblocks : list Z;            (* [comment removed for export] *)
  dp_storeblocks : list Z;           (* [comment removed for export] *)
  dp_frames : Z;                     (* [comment removed for export] *)
  dp_stored : Z -> Z                 (* [comment removed for export] *)
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record as_boot := ASBOOT {
  bt_segs : list Segment;           (* [comment removed for export] *)
  bt_ia : as_addrs;                 (* [comment removed for export] *)
  bt_spacebeg : Z;                  (* [comment removed for export] *)
  bt_resv6 : Z; bt_resv6_len : Z;   (* [comment removed for export] *)
  bt_ptrarr : Z;                    (* [comment removed for export] *)
  bt_thread : Z;                    (* [comment removed for export] *)
  bt_tctx : Z;                      (* [comment removed for export] *)
  bt_fs : Z;                        (* [comment removed for export] *)
  bt_tls_fs : Z;                    (* [comment removed for export] *)
  bt_stack_top : Z; bt_stack_bottom : Z;   (* [comment removed for export] *)
  bt_nodes0 : Z;                    (* [comment removed for export] *)
  bt_store0 : Z;                    (* [comment removed for export] *)
  bt_dep0 : depot;                  (* [comment removed for export] *)
  bt_aa0 : list (Z * Z);            (* [comment removed for export] *)
  bt_tp : Z;                        (* [comment removed for export] *)
  bt_dtls : Z;                      (* [comment removed for export] *)
  bt_consts : list (Z * nat * Z);   (* [comment removed for export] *)
  bt_maps0 : list (word * word);    (* [comment removed for export] *)
  bt_noacc0 : list (word * word);   (* [comment removed for export] *)
  bt_lazy0 : list (word * word);    (* [comment removed for export] *)
  bt_mat0 : list word;              (* [comment removed for export] *)
  bt_eager0 : Z;                    (* [comment removed for export] *)
  bt_brk : word; bt_start_brk : word; bt_mmap_base : word; bt_init_sp : word; bt_reserved : list (word * word);
  bt_fixed : list (Z * Z)           (* [comment removed for export] *)
}.
Definition ia (bt : as_boot) : as_addrs := bt_ia bt.
Definition reginfo (bt : as_boot) (c : Z) : Z := bt_spacebeg bt + KSPACE + 128 * c.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition IASZ : Z := 0x81038.
Definition priv_cover (IA : as_addrs) (lo hi : Z) : Prop := exists plo phi, In (plo, phi) (ia_priv IA) /\ plo <= lo /\ hi <= phi.
(* [comment removed for export] *)
Definition const_cover (IA : as_addrs) (lo hi : Z) : Prop := exists plo phi, In (plo, phi) (ia_const IA) /\ plo <= lo /\ hi <= phi.
(* [comment removed for export] *)
Definition img_ranges (IA : as_addrs) (tls : Z) : list (Z * Z) :=
  [(ia_instance IA + 112, ia_instance IA + 992); (ia_depot_tab IA, ia_depot_tab IA + 0x400010 + 8 * 2 ^ 15);
   (ia_stackstore IA, ia_stackstore IA + 16 + 16 * 2 ^ 12); (ia_ialloc_flag IA, ia_ialloc_flag IA + 8);
   (ia_ialloc_inst IA, ia_ialloc_inst IA + IASZ); (tls, tls + 16); (ia_rtc_sb IA, ia_rtc_sb IA + 8); (ia_rtc_uar IA, ia_rtc_uar IA + 4)].
(* [comment removed for export] *)
Fixpoint seps (x : Z * Z) (l : list (Z * Z)) : Prop :=
  match l with [] => True | y :: t => (snd x <= fst y \/ snd y <= fst x) /\ seps x t end.
Fixpoint PW (l : list (Z * Z)) : Prop := match l with [] => True | x :: t => seps x t /\ PW t end.
Lemma seps_of_forall : forall x l, (forall y, In y l -> snd x <= fst y \/ snd y <= fst x) -> seps x l.
Proof. intros x l; induction l as [|y t IH]; intros H; [exact I|]. split; [apply H; left; reflexivity | apply IH; intros y' Hy'; apply H; right; exact Hy']. Qed.
Lemma PW_of_splits : forall l : list (Z * Z),
  (forall l1 x l2 y, l = l1 ++ x :: l2 -> In y (l1 ++ l2) -> snd x <= fst y \/ snd y <= fst x) -> PW l.
Proof.
  induction l as [|x t IH]; intros H; [exact I|]. split.
  - apply seps_of_forall. intros y Hy. exact (H [] x t y eq_refl Hy).
  - apply IH. intros l1 x' l2 y E Hy. apply (H (x :: l1) x' l2 y); [rewrite E; reflexivity | right; exact Hy].
Qed.

(* [comment removed for export] *)
Definition img_dyn (IA : as_addrs) (a : Z) : Prop :=
  (ia_instance IA + 112 <= a < ia_instance IA + 728) \/ (ia_instance IA + 880 <= a < ia_instance IA + 888)
  \/ (ia_instance IA + 888 <= a < ia_instance IA + 920) \/ (ia_instance IA + 984 <= a < ia_instance IA + 992)
  \/ (ia_depot_tab IA <= a < ia_depot_tab IA + 0x400010 + 8 * 2 ^ 15)
  \/ (ia_stackstore IA <= a < ia_stackstore IA + 16 + 16 * 2 ^ 12)
  \/ (ia_ialloc_flag IA <= a < ia_ialloc_flag IA + 8)
  \/ (ia_ialloc_inst IA <= a < ia_ialloc_inst IA + IASZ).
Definition bt_ok (bt : as_boot) : Prop :=
  let IA := bt_ia bt in
  0 <= ia_img_lo IA /\ ia_img_hi IA <= AS_LO
  /\ (forall plo phi, In (plo, phi) (ia_priv IA) \/ In (plo, phi) (ia_const IA) -> ia_img_lo IA <= plo /\ phi <= ia_img_hi IA)
  /\ priv_cover IA (ia_instance IA + 112) (ia_instance IA + 985)
  /\ priv_cover IA (ia_depot_tab IA) (ia_depot_tab IA + 0x400010 + 8 * 2 ^ 15)
  /\ priv_cover IA (ia_stackstore IA) (ia_stackstore IA + 16 + 16 * 2 ^ 12)
  /\ priv_cover IA (ia_ialloc_flag IA) (ia_ialloc_flag IA + 8)                (* [comment removed for export] *)
  /\ priv_cover IA (ia_ialloc_inst IA) (ia_ialloc_inst IA + IASZ)
  /\ priv_cover IA (bt_tls_fs bt) (bt_tls_fs bt + 16)                        (* [comment removed for export] *)
  /\ Forall (fun c => priv_cover IA (fst (fst c)) (fst (fst c) + Z.of_nat (snd (fst c))) \/ const_cover IA (fst (fst c)) (fst (fst c) + Z.of_nat (snd (fst c)))) (bt_consts bt)
  /\ ia_img_lo IA <= ia_rtc_sb IA /\ ia_rtc_sb IA + 8 <= ia_img_hi IA /\ ia_img_lo IA <= ia_rtc_uar IA /\ ia_rtc_uar IA + 4 <= ia_img_hi IA
  (* [comment removed for export] *)
  /\ Forall (fun c => forall a, fst (fst c) <= a < fst (fst c) + Z.of_nat (snd (fst c)) -> ~ img_dyn IA a) (bt_consts bt)
  /\ (forall a, bt_tls_fs bt <= a < bt_tls_fs bt + 16 -> ~ img_dyn IA a)
  /\ (forall a, ia_rtc_sb IA <= a < ia_rtc_sb IA + 8 \/ ia_rtc_uar IA <= a < ia_rtc_uar IA + 4 -> ~ img_dyn IA a)
  (* [comment removed for export] *)
  /\ (forall l1 x l2 y, img_ranges IA (bt_tls_fs bt) = l1 ++ x :: l2 -> In y (l1 ++ l2) -> snd x <= fst y \/ snd y <= fst x).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record region := REG {
  r_mapped_user : Z;       (* [comment removed for export] *)
  r_alloc_user : Z;        (* [comment removed for export] *)
  r_mapped_fa : Z;         (* [comment removed for export] *)
  r_free : list Z;         (* [comment removed for export] *)
  r_uhole : bool;          (* [comment removed for export] *)
  r_fhole : bool           (* [comment removed for export] *)
}.
Definition region0 : region := REG 0 0 0 [] false false.

(* [comment removed for export] *)
Record batch := BATCH { ba_addr : Z; ba_items : list (Z * Z) }.
Definition ba_bytes (b : batch) : Z := BATCHSZ + fold_right (fun it acc => snd it + acc) 0 (ba_items b).
Definition q_bytes (q : list batch) : Z := fold_right (fun b acc => ba_bytes b + acc) 0 q.

(* [comment removed for export] *)
Record schunk := SCH { sc_map : Z; sc_n : Z (* [comment removed for export] *) }.
Definition sc_mapsz (s : schunk) : Z := sec_map_size (sc_n s).
Definition sc_user (s : schunk) : Z := sc_map s + sec_user_off (sc_n s).

Record ast := AST {
  a_reg : Z -> region;               (* [comment removed for export] *)
  a_cinit : bool;                    (* [comment removed for export] *)
  a_cache : Z -> list Z;             (* [comment removed for export] *)
  a_tq : list batch;                 (* [comment removed for export] *)
  a_gq : list batch;                 (* [comment removed for export] *)
  a_sec : list schunk;               (* [comment removed for export] *)
  a_nres : Z;                        (* [comment removed for export] *)
  a_dep : depot;
  a_hint : Z -> Z;                   (* [comment removed for export] *)
  a_ialloc : bool;                   (* [comment removed for export] *)
  a_aa : list (Z * Z);               (* [comment removed for export] *)
  a_kact : Z;                        (* [comment removed for export] *)
  a_shsec : Z                        (* [comment removed for export] *)
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Derived.
  Variable bt : as_boot.
  Variable st : ast.
  Variable Lc FF : list (Z * Z).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).

  (* [comment removed for export] *)
  Definition quar : list (Z * Z) := flat_map ba_items (a_tq st ++ a_gq st).


  Definition blk_class (n : Z) : Z := class_of (needed n).

  (* [comment removed for export] *)
  Definition carved (c a : Z) : Prop :=
    exists j, 0 <= j /\ (j + 1) * csize c <= r_alloc_user (a_reg st c) /\ a = chunk_addr SBEG c j.
  (* [comment removed for export] *)
  Definition registered (p n : Z) : Prop := exists s, In s (a_sec st) /\ sc_user s = p /\ sc_n s = n.

  (* [comment removed for export] *)
  Definition in_live_c (c a : Z) : Prop := exists p n, In (p, n) Lc /\ is_primary n = true /\ blk_class n = c /\ prim_alloc_beg p n = a.
  Definition in_quar_c (c a : Z) : Prop := exists m n, In (m, n) quar /\ is_primary n = true /\ blk_class n = c /\ prim_alloc_beg (m + 16) n = a.
  (* [comment removed for export] *)
  Definition in_cache_c (c a : Z) : Prop := exists k, In k (a_cache st c) /\ a = chunk_of_compact SBEG c k.
  Definition in_fa_c (c a : Z) : Prop := exists k, In k (r_free (a_reg st c)) /\ a = chunk_of_compact SBEG c k.
  Definition in_batch (a : Z) : Prop := exists b, In b (a_tq st ++ a_gq st) /\ ba_addr b = a.

  Definition partition_c (c : Z) : Prop :=
    (forall a, carved c a <-> (in_live_c c a \/ in_quar_c c a \/ in_cache_c c a \/ in_fa_c c a \/ (c = BATCHCLASS /\ in_batch a)))
    /\ (forall a, ~ (in_live_c c a /\ in_quar_c c a)) /\ (forall a, ~ (in_live_c c a /\ in_cache_c c a))
    /\ (forall a, ~ (in_live_c c a /\ in_fa_c c a)) /\ (forall a, ~ (in_quar_c c a /\ in_cache_c c a))
    /\ (forall a, ~ (in_quar_c c a /\ in_fa_c c a)) /\ (forall a, ~ (in_cache_c c a /\ in_fa_c c a))
    /\ (forall a, in_batch a -> c = BATCHCLASS -> ~ (in_live_c c a \/ in_quar_c c a \/ in_cache_c c a \/ in_fa_c c a))
    /\ List.NoDup (a_cache st c) /\ List.NoDup (r_free (a_reg st c)).
End Derived.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FRW : Z := 9.
(* [comment removed for export] *)
Definition AMAX : Z := 2 ^ 31.

(* [comment removed for export] *)
Fixpoint sum_classes (f : Z -> Z) (n : nat) : Z := match n with O => 0 | S k => f (Z.of_nat n) + sum_classes f k end.

(* [comment removed for export] *)
Definition dep0_ok (bt : as_boot) : Prop := dp_nids (bt_dep0 bt) <= 2 ^ 20 /\ 1 <= dp_frames (bt_dep0 bt) <= 2 ^ 20.

Section WFsec.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable st : ast.
  Variable Lc FF : list (Z * Z).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).

  Definition wf_region (c : Z) : Prop :=
    let r := a_reg st c in
    (* [comment removed for export] *)
    (0 <= r_alloc_user r <= r_mapped_user r
     /\ (r_mapped_user r - r_alloc_user r < csize c \/ KUSERMAP <= r_mapped_user r - r_alloc_user r < KUSERMAP + csize c)
     (* [comment removed for export] *)
     /\ r_alloc_user r <= AMAX)
    /\ r_mapped_user r mod KUSERMAP = 0 /\ r_mapped_user r + KUSERMAP <= KREGION_EXHAUST
    /\ r_alloc_user r mod csize c = 0
    /\ 0 <= r_mapped_fa r /\ r_mapped_fa r mod KFAMAP = 0 /\ 4 * Z.of_nat (length (r_free r)) <= r_mapped_fa r
    /\ r_mapped_fa r <= 2 ^ 29   (* [comment removed for export] *)
    /\ (forall k, In k (r_free r) -> 0 <= k < 2 ^ 32 /\ carved bt st c (chunk_of_compact SBEG c k))
    /\ partition_c bt st Lc c
    (* [comment removed for export] *)
    /\ (r_fhole r = true -> r_mapped_fa r + KFAMAP <= 2 ^ 29).
  Definition wf_regions : Prop :=
    (forall c, 1 <= c <= 30 -> wf_region c) /\ (forall c, ~ (1 <= c <= 30) -> a_reg st c = region0 /\ a_cache st c = []).

  Definition wf_cache : Prop :=
    forall c, 1 <= c <= 30 -> Z.of_nat (length (a_cache st c)) <= cache_max c
              (* [comment removed for export] *)
              /\ (a_cinit st = false -> a_cache st c = [] /\ r_alloc_user (a_reg st c) = 0)
              /\ (forall k, In k (a_cache st c) -> 0 <= k < 2 ^ 32 /\ carved bt st c (chunk_of_compact SBEG c k)).

  Definition wf_batch (b : batch) : Prop :=
    1 <= Z.of_nat (length (ba_items b)) <= BATCHCAP /\ carved bt st BATCHCLASS (ba_addr b)
    /\ (forall m n, In (m, n) (ba_items b) -> 1 <= n <= NMAX /\
          ((is_primary n = true /\ carved bt st (blk_class n) (prim_alloc_beg (m + 16) n))
           \/ (is_primary n = false /\ registered st (m + 16) n))).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition wf_batch0 (b : batch) : Prop :=
    0 <= Z.of_nat (length (ba_items b)) <= BATCHCAP /\ carved bt st BATCHCLASS (ba_addr b)
    /\ (forall m n, In (m, n) (ba_items b) -> 1 <= n <= NMAX /\
          ((is_primary n = true /\ carved bt st (blk_class n) (prim_alloc_beg (m + 16) n))
           \/ (is_primary n = false /\ registered st (m + 16) n))).
  Lemma wf_batch_0 : forall b, wf_batch b -> wf_batch0 b.
  Proof. intros b (L & CV & IT). split; [lia|]. exact (conj CV IT). Qed.
  Definition wf_quarantine_q (qt qg : Z) : Prop :=
    Forall wf_batch (a_tq st) /\ Forall wf_batch0 (a_gq st)
    /\ q_bytes (a_tq st) <= qt
    /\ q_bytes (a_gq st) <= qg
    /\ List.NoDup (map ba_addr (a_tq st ++ a_gq st))
    /\ List.NoDup (map fst (quar st)).
  Definition wf_quarantine : Prop := wf_quarantine_q (2 ^ 20) (2 ^ 28).

  Definition wf_secondary : Prop :=
    Z.of_nat (length (a_sec st)) <= a_nres st /\ a_nres st mod 2 ^ 14 = 0 /\ 0 <= a_nres st <= 2 ^ 20
    /\ (forall s, In s (a_sec st) -> 64513 <= sc_n s <= NMAX /\ sc_map s mod PG = 0)      (* [comment removed for export] *)
    /\ List.NoDup (map sc_map (a_sec st))
    (* [comment removed for export] *)
    /\ (forall s, In s (a_sec st) -> (In (sc_user s, sc_n s) Lc <-> ~ In (sc_user s - 16, sc_n s) (quar st)))
    /\ (forall p n, In (p, n) Lc -> is_primary n = false -> registered st p n)
    /\ (forall m n, In (m, n) (quar st) -> is_primary n = false -> registered st (m + 16) n).

  Definition wf_live : Prop :=
    (forall p n, In (p, n) Lc -> 1 <= n <= NMAX /\ p mod 16 = 0 /\ ablk_ok (bt_ia bt) p n /\
        (is_primary n = true -> carved bt st (blk_class n) (prim_alloc_beg p n)))
    /\ List.NoDup Lc /\ (forall p n p' n', In (p, n) Lc -> In (p', n') Lc -> (p, n) <> (p', n') -> p + n <= p' \/ p' + n' <= p).

  (* [comment removed for export] *)
  Definition fpos (f k : Z) : Z := (f - (bt_fs bt + 0x9000 + k * 2 ^ 20)) / FS k.
  Definition wf_fake : Prop :=
    (forall f k, In (f, k) FF -> 0 <= k <= KMAXCLASS /\ 0 <= fpos f k < FCAP k /\ f = fake_frame_addr (bt_fs bt) k (fpos f k))
    /\ List.NoDup FF /\ (forall k, 0 <= a_hint st k).

  Definition wf_depot : Prop :=
    let d := a_dep st in
    dp_nids (bt_dep0 bt) <= dp_nids d /\ dp_nids d <= dp_nids (bt_dep0 bt) + a_kact st / EVT   (* [comment removed for export] *)
    /\ dp_nids d < 2 ^ 31 - 1
    /\ (forall i, 0 <= i < 2 ^ 20 -> 0 <= dp_tab d i <= dp_nids d)
    /\ (forall id, 1 <= id <= dp_nids d -> 0 <= dp_link d id < id /\ 0 <= dp_hash d id < 2 ^ 64 /\ 0 <= dp_store d id < 2 ^ 32)
    /\ Z.of_nat (length (dp_nodeblocks d)) = dp_nids d / 2 ^ 16        (* [comment removed for export] *)
    /\ 0 <= dp_frames d /\ Z.of_nat (length (dp_storeblocks d)) + 1 <= 2 ^ 12
    /\ dp_frames d <= dp_frames (bt_dep0 bt) + FRW * (a_kact st / EVT) + FRW * Z.of_nat (length (dp_storeblocks d))
         (* [comment removed for export] *)
    /\ Z.of_nat (length (dp_storeblocks d)) = Z.min (Z.max 0 ((dp_frames d - 1) / 2 ^ 20)) (2 ^ 12 - 1)   (* [comment removed for export] *)
    /\ (forall i, 0 <= dp_stored d i < 2 ^ 32)
    /\ (forall b, In b (dp_nodeblocks d ++ dp_storeblocks d) -> b mod PG = 0).                (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition sum_mu : Z := sum_classes (fun c => r_mapped_user (a_reg st c)) 30.
  Definition wf_meter : Prop :=
    0 <= a_kact st /\ 0 <= a_shsec st
    /\ a_shsec st + 2 * PG * Z.of_nat (length (a_sec st)) <= 2 * PG * (a_kact st / EVT)
    /\ sum_mu <= KUSERMAP * (a_kact st / EVT)
    /\ (forall c, 1 <= c <= 30 -> r_mapped_fa (a_reg st c) <= 4 * (r_mapped_user (a_reg st c) / csize c) + KFAMAP).

  (* [comment removed for export] *)
  Definition dyn_ranges : list (Z * Z) :=
    map (fun s => (sc_map s, sc_map s + sc_mapsz s)) (a_sec st)
    ++ map (fun b => (b, b + 2 ^ 20)) (dp_nodeblocks (a_dep st))
    ++ map (fun b => (b, b + 2 ^ 23)) (dp_storeblocks (a_dep st)).
  Definition all_ranges : list (Z * Z) := bt_fixed bt ++ dyn_ranges.
  Definition wf_maps : Prop :=
    (forall lo hi, In (lo, hi) all_ranges -> dyn_ok (bt_ia bt) lo hi /\ lo < hi /\ lo mod PG = 0 /\ hi mod PG = 0)
    /\ (forall l1 l2 lo hi lo' hi', all_ranges = l1 ++ (lo, hi) :: l2 -> In (lo', hi') (l1 ++ l2) -> hi <= lo' \/ hi' <= lo)
    /\ In (bt_resv6 bt, bt_resv6 bt + bt_resv6_len bt) (bt_fixed bt)   (* [comment removed for export] *)
    /\ bt_resv6 bt <= bt_spacebeg bt /\ bt_spacebeg bt + KSPACE + PG <= bt_resv6 bt + bt_resv6_len bt
    /\ In (bt_ptrarr bt, bt_ptrarr bt + 2 ^ 23) (bt_fixed bt)
    /\ In (bt_fs bt, bt_fs bt + FAKE_SIZE) (bt_fixed bt)
    /\ In (bt_thread bt, bt_thread bt + PG) (bt_fixed bt)
    /\ In (bt_nodes0 bt, bt_nodes0 bt + 2 ^ 20) (bt_fixed bt) /\ In (bt_store0 bt, bt_store0 bt + 2 ^ 23) (bt_fixed bt)
    /\ In (bt_tctx bt, bt_tctx bt + 0x10000) (bt_fixed bt)    (* [comment removed for export] *)
    (* [comment removed for export] *)
    /\ (forall a, pg_in_ivz (bt_lazy0 bt) a -> 0 <= a < CEIL -> ~ in_band a ->       (* [comment removed for export] *)
          (bt_resv6 bt <= a < bt_resv6 bt + bt_resv6_len bt) \/ (bt_ptrarr bt <= a < bt_ptrarr bt + 2 ^ 23) \/ (bt_store0 bt <= a < bt_store0 bt + 2 ^ 23))
    /\ (forall a, pg_in_ivz (bt_lazy0 bt) a -> 0 <= a < CEIL -> in_band a -> shmaps a \/ (AS_GAPLO <= a < AS_GAPHI))    (* [comment removed for export] *)
    (* [comment removed for export] *)
    /\ (forall a, bt_spacebeg bt + KSPACE <= a < bt_spacebeg bt + KSPACE + PG -> ~ pg_in_ivz (bt_lazy0 bt) a)
    (* [comment removed for export] *)
    /\ (forall b n a, In (b, n) (bt_maps0 bt) -> bv_unsigned b <= a < bv_unsigned b + bv_unsigned n ->
          ~ (bt_resv6 bt <= a < bt_resv6 bt + bt_resv6_len bt))
    (* [comment removed for export] *)
    /\ Forall (fun e : word * word => 0 < bv_unsigned (snd e)) (bt_maps0 bt)
    (* [comment removed for export] *)
    /\ In (bt_dtls bt, bt_dtls bt + PG) (bt_fixed bt)
    /\ (bt_store0 bt + 2 ^ 23 <= bt_ptrarr bt \/ bt_ptrarr bt + 2 ^ 23 <= bt_store0 bt)
    /\ (bt_dtls bt + PG <= bt_thread bt \/ bt_thread bt + PG <= bt_dtls bt)   (* [comment removed for export] *)
    (* [comment removed for export] *)
    /\ (forall b n lo hi, In (b, n) (bt_maps0 bt) -> In (lo, hi) dyn_ranges -> hi <= bv_unsigned b \/ bv_unsigned b + bv_unsigned n <= lo).

  Definition WFq (qt qg : Z) : Prop :=
    wf_regions /\ wf_cache /\ wf_quarantine_q qt qg /\ wf_secondary /\ wf_live /\ wf_fake /\ wf_depot /\ wf_meter /\ wf_maps
    (* [comment removed for export] *)
    /\ (bt_spacebeg bt mod 2 ^ 16 = 0 /\ Z.of_nat (length Lc) <= LMAX /\ PHI Lc <= GBUDGET)
    /\ bt_ok bt
    /\ dep0_ok bt.                 (* [comment removed for export] *)
  Definition WF : Prop := WFq (2 ^ 20) (2 ^ 28).
End WFsec.

(* [comment removed for export] *)
Lemma sum_classes_ext : forall (f g : Z -> Z) (n : nat),
  (forall c, 1 <= c <= Z.of_nat n -> f c = g c) -> sum_classes f n = sum_classes g n.
Proof.
  intros f g n. induction n as [|n IH]; intros H; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [sum_classes] in G in change_no_check G' end).
  rewrite (H (Z.of_nat (S n))) by lia. rewrite IH; [reflexivity|]. intros c Hc. apply H. lia.
Qed.
Lemma sum_classes_upd : forall (f g : Z -> Z) (n : nat) (c0 : Z),
  (forall c, 1 <= c <= Z.of_nat n -> c <> c0 -> f c = g c) -> 1 <= c0 <= Z.of_nat n ->
  sum_classes g n = sum_classes f n + (g c0 - f c0).
Proof.
  intros f g n. induction n as [|n IH]; intros c0 H Hc0; [lia|]. (lazymatch goal with |- ?G => let G' := eval cbn [sum_classes] in G in change_no_check G' end).
  destruct (Z.eq_dec (Z.of_nat (S n)) c0) as [E|NE].
  - rewrite <- E. rewrite (sum_classes_ext f g n); [lia|]. intros c Hc. apply H; lia.
  - rewrite (H (Z.of_nat (S n))) by lia. rewrite (IH c0); [lia | | lia]. intros c Hc Hne. apply H; lia.
Qed.



Section MeterTransfer.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Lemma sum_mu_ext : forall st st', (forall c, 1 <= c <= 30 -> r_mapped_user (a_reg st' c) = r_mapped_user (a_reg st c)) -> sum_mu st' = sum_mu st.
  Proof. intros st st' H. (lazymatch goal with |- ?G => let G' := eval unfold sum_mu in G in change_no_check G' end). apply sum_classes_ext. intros c Hc. apply H. lia. Qed.
  Lemma sum_mu_upd : forall st st' c0, 1 <= c0 <= 30 ->
    (forall c, 1 <= c <= 30 -> c <> c0 -> r_mapped_user (a_reg st' c) = r_mapped_user (a_reg st c)) ->
    sum_mu st' = sum_mu st + (r_mapped_user (a_reg st' c0) - r_mapped_user (a_reg st c0)).
  Proof.
    intros st st' c0 Hc0 H. (lazymatch goal with |- ?G => let G' := eval unfold sum_mu in G in change_no_check G' end).
    apply (sum_classes_upd (fun c => r_mapped_user (a_reg st c)) (fun c => r_mapped_user (a_reg st' c)) 30 c0); [| lia].
    intros c Hc Hne. symmetry. apply H; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma wf_meter_transfer : forall st st',
    a_kact st' = a_kact st -> a_shsec st' = a_shsec st -> length (a_sec st') = length (a_sec st) ->
    (forall c, 1 <= c <= 30 -> r_mapped_user (a_reg st' c) = r_mapped_user (a_reg st c) /\ r_mapped_fa (a_reg st' c) = r_mapped_fa (a_reg st c)) ->
    wf_meter st -> wf_meter st'.
  Proof.
    intros st st' EK ESH EL ER (M1 & M2 & M3 & M4 & M5). (lazymatch goal with |- ?G => let G' := eval unfold wf_meter in G in change_no_check G' end). rewrite EK, ESH, EL.
    rewrite (sum_mu_ext st st') by (intros c Hc; exact (proj1 (ER c Hc))).
    split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M4|].
    intros c Hc. destruct (ER c Hc) as [E1 E2]. rewrite E1, E2. exact (M5 c Hc).
  Qed.
End MeterTransfer.

(* [comment removed for export] *)
Lemma wf_batch0_mono : forall bt st st' b,
  (forall c a, carved bt st c a -> carved bt st' c a) -> (forall p n, registered st p n -> registered st' p n) ->
  wf_batch0 bt st b -> wf_batch0 bt st' b.
Proof.
  intros bt st st' b CV RG (B1 & B2 & B3). split; [exact B1|]. split; [exact (CV _ _ B2)|].
  intros m n Hin. destruct (B3 m n Hin) as (N1 & [[HP C] | [HP R]]); (split; [exact N1|]).
  - left. exact (conj HP (CV _ _ C)).
  - right. exact (conj HP (RG _ _ R)).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MAGIC : Z := 0xCC6E96B9CC6E96B9.
(* [comment removed for export] *)
Definition hdr1_ok (b : Z) : Prop := b = 0x11 \/ b = 0x91.
Definition rep_hdr (bt : as_boot) (M : mem) (p n state : Z) : Prop :=
  byteZ (bt_segs bt) M (p - 16) state /\ (exists b1, hdr1_ok b1 /\ byteZ (bt_segs bt) M (p - 15) b1)
  /\ cellZ (bt_segs bt) M (p - 14) 2 (n / 2 ^ 32) /\ cellZ (bt_segs bt) M (p - 12) 4 (n mod 2 ^ 32)
  /\ writableZ (bt_segs bt) M (p - 8) p /\ cellZ (bt_segs bt) M (p - 4) 4 0
  /\ (16 < rz n -> cellZ (bt_segs bt) M (p - rz n) 8 MAGIC /\ cellZ (bt_segs bt) M (p - rz n + 8) 8 (p - 16)).

(* [comment removed for export] *)
Definition rep_reginfo (bt : as_boot) (M : mem) (c : Z) (r : region) : Prop :=
  let a := reginfo bt c in
  cellZ (bt_segs bt) M a 8 0 /\ cellZ (bt_segs bt) M (a + 8) 8 0 /\ cellZ (bt_segs bt) M (a + 16) 8 (Z.of_nat (length (r_free r))) /\ cellZ (bt_segs bt) M (a + 24) 8 (r_mapped_fa r)
  /\ cellZ (bt_segs bt) M (a + 32) 8 (r_alloc_user r) /\ cellZ (bt_segs bt) M (a + 40) 8 0 /\ cellZ (bt_segs bt) M (a + 48) 8 (r_mapped_user r) /\ cellZ (bt_segs bt) M (a + 56) 8 0
  /\ byteZ (bt_segs bt) M (a + 68) 0 /\ writableZ (bt_segs bt) M a (a + 128).
(* [comment removed for export] *)
Definition rep_freearray (bt : as_boot) (M : mem) (c : Z) (r : region) : Prop :=
  (forall i k, nth_error (r_free r) i = Some k -> cellZ (bt_segs bt) M (fa_beg (bt_spacebeg bt) c + 4 * Z.of_nat i) 4 k)
  /\ writableZ (bt_segs bt) M (fa_beg (bt_spacebeg bt) c) (fa_beg (bt_spacebeg bt) c + r_mapped_fa r)
  /\ writableZ (bt_segs bt) M (region_beg (bt_spacebeg bt) c) (region_beg (bt_spacebeg bt) c + r_mapped_user r).

(* [comment removed for export] *)
Definition T_QC : Z := 80.  Definition T_PC : Z := 208.  Definition PC_SZ : Z := 80.  Definition T_UNW : Z := 3168.
Definition rep_list (bt : as_boot) (M : mem) (hd : Z) (q : list batch) : Prop :=      (* [comment removed for export] *)
  cellZ (bt_segs bt) M hd 8 (Z.of_nat (length q))
  /\ cellZ (bt_segs bt) M (hd + 8) 8 (match q with [] => 0 | b :: _ => ba_addr b end)
  /\ cellZ (bt_segs bt) M (hd + 16) 8 (match rev q with [] => 0 | b :: _ => ba_addr b end)
  /\ cellZ (bt_segs bt) M (hd + 24) 8 (q_bytes q).
(* [comment removed for export] *)
Definition rep_batches (bt : as_boot) (M : mem) (q : list batch) : Prop :=
  forall i b, nth_error q i = Some b ->
    cellZ (bt_segs bt) M (ba_addr b) 8 (match nth_error q (S i) with Some b' => ba_addr b' | None => 0 end)
    /\ cellZ (bt_segs bt) M (ba_addr b + 8) 8 (ba_bytes b) /\ cellZ (bt_segs bt) M (ba_addr b + 16) 8 (Z.of_nat (length (ba_items b)))
    /\ (forall j mn, nth_error (ba_items b) j = Some mn -> cellZ (bt_segs bt) M (ba_addr b + 24 + 8 * Z.of_nat j) 8 (fst mn))
    /\ writableZ (bt_segs bt) M (ba_addr b) (ba_addr b + BATCHSZ).
Definition rep_pclass (bt : as_boot) (M : mem) (T : Z) (cinit : bool) (c : Z) (ks : list Z) : Prop :=
  let a := T + T_PC + PC_SZ * c in
  cellZ (bt_segs bt) M a 4 (Z.of_nat (length ks))
  /\ cellZ (bt_segs bt) M (a + 4) 4 (if cinit then cache_max c else 0) /\ cellZ (bt_segs bt) M (a + 8) 8 (if cinit then csize c else 0)
  /\ (forall i k, nth_error ks i = Some k -> cellZ (bt_segs bt) M (a + 16 + 4 * Z.of_nat i) 4 k).
Definition rep_thread (bt : as_boot) (st : ast) (M : mem) : Prop :=
  let T := bt_thread bt in
  cellZ (bt_segs bt) M T 8 (bt_tctx bt) /\ cellZ (bt_segs bt) M (T + 8) 8 (bt_stack_top bt) /\ cellZ (bt_segs bt) M (T + 16) 8 (bt_stack_bottom bt)
  /\ byteZ (bt_segs bt) M (T + 40) 0 /\ cellZ (bt_segs bt) M (T + 72) 8 (bt_fs bt) /\ byteZ (bt_segs bt) M (T + T_UNW) 0
  /\ rep_list bt M (T + T_QC) (a_tq st)
  /\ (forall c, 1 <= c <= 30 -> rep_pclass bt M T (a_cinit st) c (a_cache st c))   (* [comment removed for export] *)
  /\ writableZ (bt_segs bt) M T (T + PG)
  /\ cellZ (bt_segs bt) M (bt_tctx bt + 152) 8 T /\ cellZ (bt_segs bt) M (bt_tctx bt + 8) 4 0
  (* [comment removed for export] *)
  /\ cellZ (bt_segs bt) M (T + 48) 8 (bt_tp bt + 0x738) /\ cellZ (bt_segs bt) M (T + 56) 8 (bt_tp bt + 0x814).

(* [comment removed for export] *)
Definition IB (bt : as_boot) : Z := ia_instance (bt_ia bt).
Definition rep_instance (bt : as_boot) (st : ast) (M : mem) : Prop :=
  let I := IB bt in
  cellZ (bt_segs bt) M (I + 112) 8 (a_nres st) /\ cellZ (bt_segs bt) M (I + 120) 8 (Z.of_nat (length (a_sec st))) /\ byteZ (bt_segs bt) M (I + 680) 0
  /\ byteZ (bt_segs bt) M (I + 880) 0 /\ byteZ (bt_segs bt) M (I + 881) 0 /\ byteZ (bt_segs bt) M (I + 984) 0
  /\ rep_list bt M (I + 888) (a_gq st)
  (* [comment removed for export] *)
  /\ (forall i s, nth_error (a_sec st) i = Some s -> cellZ (bt_segs bt) M (bt_ptrarr bt + 8 * Z.of_nat i) 8 (sc_map s))
  /\ writableZ (bt_segs bt) M (bt_ptrarr bt) (bt_ptrarr bt + 8 * a_nres st).
(* [comment removed for export] *)
Definition rep_secondary (bt : as_boot) (st : ast) (M : mem) : Prop :=
  forall i s, nth_error (a_sec st) i = Some s ->
    cellZ (bt_segs bt) M (sc_map s) 8 (sc_map s) /\ cellZ (bt_segs bt) M (sc_map s + 8) 8 (sc_mapsz s) /\ cellZ (bt_segs bt) M (sc_map s + 16) 8 (sec_needed (sc_n s))
    /\ cellZ (bt_segs bt) M (sc_map s + 24) 8 (Z.of_nat i) /\ writableZ (bt_segs bt) M (sc_map s) (sc_map s + sc_mapsz s).

(* [comment removed for export] *)
Definition rep_headers (bt : as_boot) (st : ast) (Lc : list (Z * Z)) (M : mem) : Prop :=
  (forall p n, In (p, n) Lc -> rep_hdr bt M p n 2)
  /\ (forall m n, In (m, n) (quar st) -> rep_hdr bt M (m + 16) n 3 /\ writableZ (bt_segs bt) M (m + 16) (m + 24)).

(* [comment removed for export] *)
Definition DEPOT_TAB (bt : as_boot) : Z := ia_depot_tab (bt_ia bt).
Definition DEPOT_NIDS (bt : as_boot) : Z := DEPOT_TAB bt + 0x400000.
Definition DEPOT_MAP1 (bt : as_boot) : Z := DEPOT_TAB bt + 0x400010.
Definition SSOBJ (bt : as_boot) : Z := ia_stackstore (bt_ia bt).
Definition node_blocks (bt : as_boot) (d : depot) : list Z := bt_nodes0 bt :: dp_nodeblocks d.
Definition store_blocks (bt : as_boot) (d : depot) : list Z := bt_store0 bt :: dp_storeblocks d.
Definition node_addr (bt : as_boot) (d : depot) (id : Z) : Z :=
  nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt d) 0 + 16 * (id mod 2 ^ 16).
Definition rep_depot (bt : as_boot) (st : ast) (M : mem) : Prop :=
  let d := a_dep st in let tab := DEPOT_TAB bt in let SG := bt_segs bt in
  (forall i, 0 <= i < 2 ^ 20 -> cellZ SG M (tab + 4 * i) 4 (dp_tab d i))
  /\ cellZ SG M (DEPOT_NIDS bt) 4 (dp_nids d) /\ byteZ SG M (DEPOT_NIDS bt + 8) 0
  /\ (forall i, 0 <= i < 2 ^ 15 -> cellZ SG M (DEPOT_MAP1 bt + 8 * i) 8 (nth (Z.to_nat i) (node_blocks bt d) 0))
  /\ (forall id, 1 <= id <= dp_nids d ->
        cellZ SG M (node_addr bt d id) 8 (dp_hash d id) /\ cellZ SG M (node_addr bt d id + 8) 4 (dp_link d id)
        /\ cellZ SG M (node_addr bt d id + 12) 4 (dp_store d id))
  /\ (forall b, In b (node_blocks bt d) -> writableZ SG M b (b + 2 ^ 20))
  /\ cellZ SG M (SSOBJ bt) 8 (dp_frames d)
  /\ (forall i, 0 <= i < 2 ^ 12 ->
        cellZ SG M (SSOBJ bt + 16 + 16 * i) 8 (nth (Z.to_nat i) (store_blocks bt d) 0)
        /\ cellZ SG M (SSOBJ bt + 24 + 16 * i) 4 (dp_stored d i) /\ byteZ SG M (SSOBJ bt + 28 + 16 * i) 0)
  /\ (forall b, In b (store_blocks bt d) -> writableZ SG M b (b + 2 ^ 23)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FSLOG : Z := 20.
Definition rep_fake (bt : as_boot) (st : ast) (FF : list (Z * Z)) (M : mem) : Prop :=
  let fs := bt_fs bt in
  (forall k, 0 <= k <= 10 -> cellZ (bt_segs bt) M (fs + 8 * k) 8 (a_hint st k))
  /\ byteZ (bt_segs bt) M (fs + 96) 0                                                   (* [comment removed for export] *)
  /\ (forall k pos, 0 <= k <= 10 -> 0 <= pos < FCAP k ->
        byteZ (bt_segs bt) M (fake_flag_addr fs k pos) (if existsb (fun fk => Z.eqb (fst fk) (fake_frame_addr fs k pos) && Z.eqb (snd fk) k) FF then 1 else 0))
  /\ (forall f k, In (f, k) FF -> cellZ (bt_segs bt) M (f + FS k - 8) 8 (fake_flag_addr fs k (fpos bt f k)))
  /\ writableZ (bt_segs bt) M fs (fs + FAKE_SIZE)
  /\ cellZ (bt_segs bt) M (bt_tls_fs bt) 8 fs
  /\ cellZ (bt_segs bt) M (fs + 88) 8 FSLOG                                          (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ cellZ (bt_segs bt) M (bt_tls_fs bt + 8) 8 (bt_dtls bt) /\ cellZ (bt_segs bt) M (bt_dtls bt + 24) 8 (bt_tp bt).

(* [comment removed for export] *)
Definition IA_FLAG (bt : as_boot) : Z := ia_ialloc_flag (bt_ia bt).
Definition IA_INST (bt : as_boot) : Z := ia_ialloc_inst (bt_ia bt).
Definition rep_ialloc (bt : as_boot) (st : ast) (M : mem) : Prop :=
  let i := IA_INST bt in
  byteZ (bt_segs bt) M (IA_FLAG bt) (if a_ialloc st then 1 else 0) /\ byteZ (bt_segs bt) M (IA_FLAG bt + 1) 0
  /\ fillZ (bt_segs bt) M (i + 8) (i + 8 + 0x40000) 0                                   (* [comment removed for export] *)
  /\ (a_ialloc st = true -> cellZ (bt_segs bt) M (i + 0x40dc0) 8 PG /\ cellZ (bt_segs bt) M (i + 0x40dc8) 8 (i + 0x40dd0)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Shadow.
  Variable bt : as_boot.
  Variable st : ast.
  Variable Lc : list (Z * Z).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  Definition FA : Z := 0xfa.   Definition FD : Z := 0xfd.
  (* [comment removed for export] *)
  Definition user_granule (p n g : Z) : Prop := p / 8 <= g < (p + n + 7) / 8.
  Definition live_granule (g : Z) : Prop := exists p n, In (p, n) Lc /\ user_granule p n g.

  Definition rep_shadow (M : mem) : Prop :=
    (* [comment removed for export] *)
    (forall c g, 1 <= c <= 30 ->
        (region_beg SBEG c) / 8 <= g < (region_beg SBEG c + r_mapped_user (a_reg st c)) / 8 ->
        ~ live_granule g -> byteZ (bt_segs bt) M (SB + g) (if (existsb (fun mn => (((fst mn + 16) / 8) <=? g) && (g <? ((fst mn + 16 + snd mn + 7) / 8))) (quar st)) then FD else FA))
    /\ (forall c g, 1 <= c <= 30 -> (fa_beg SBEG c) / 8 <= g < (fa_beg SBEG c + r_mapped_fa (a_reg st c)) / 8 -> byteZ (bt_segs bt) M (SB + g) FA)
    (* [comment removed for export] *)
    /\ (forall s g, In s (a_sec st) ->
          (sc_map s) / 8 <= g < (sc_map s + sc_mapsz s) / 8 -> ~ user_granule (sc_user s) (sc_n s) g -> byteZ (bt_segs bt) M (SB + g) FA)
    /\ (forall s g, In s (a_sec st) -> In (sc_user s - 16, sc_n s) (quar st) -> user_granule (sc_user s) (sc_n s) g -> byteZ (bt_segs bt) M (SB + g) FD)
    (* [comment removed for export] *)
    /\ (forall c g, 1 <= c <= 30 -> (region_beg SBEG c) / 8 <= g < (region_beg SBEG c + r_mapped_user (a_reg st c)) / 8 -> M (Z_to_bv 64 (SB + g)) <> None)
    /\ (forall s g, In s (a_sec st) -> (sc_map s) / 8 <= g < (sc_map s + sc_mapsz s) / 8 -> M (Z_to_bv 64 (SB + g)) <> None).
End Shadow.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Ledger.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable st : ast.
  Variable Lc : list (Z * Z).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation u := bv_unsigned.

  (* [comment removed for export] *)
  Definition dyn_maps : list (word * word) :=
    map (fun s => (Z_to_bv 64 (sc_map s), Z_to_bv 64 (sc_mapsz s))) (a_sec st)
    ++ map (fun b => (Z_to_bv 64 b, Z_to_bv 64 (2 ^ 20))) (dp_nodeblocks (a_dep st))
    ++ map (fun b => (Z_to_bv 64 b, Z_to_bv 64 (2 ^ 23))) (dp_storeblocks (a_dep st)).
  (* [comment removed for export] *)
  Definition committed (a : Z) : Prop :=
    (exists c, 1 <= c <= 30 /\ (region_beg SBEG c <= a < region_beg SBEG c + r_mapped_user (a_reg st c)
                                \/ fa_beg SBEG c <= a < fa_beg SBEG c + r_mapped_fa (a_reg st c)))
    \/ (bt_ptrarr bt <= a < bt_ptrarr bt + 8 * a_nres st).

  (* [comment removed for export] *)
  Definition holes (a : Z) : Prop :=
    exists c, 1 <= c <= 30 /\
      ((r_uhole (a_reg st c) = true /\
        region_beg SBEG c + r_mapped_user (a_reg st c) <= a < region_beg SBEG c + r_mapped_user (a_reg st c) + KUSERMAP)
       \/ (r_fhole (a_reg st c) = true /\
           fa_beg SBEG c + r_mapped_fa (a_reg st c) <= a < fa_beg SBEG c + r_mapped_fa (a_reg st c) + KFAMAP)).
  Definition in_resv6 (a : Z) : Prop := bt_resv6 bt <= a < bt_resv6 bt + bt_resv6_len bt.
  (* [comment removed for export] *)
  Definition frag_ok (iv : word * word) : Prop :=
    let lo := u (fst iv) in let hi := u (fst iv) + u (snd iv) in
    bt_resv6 bt <= lo /\ lo < hi /\ hi <= bt_resv6 bt + bt_resv6_len bt
    /\ (lo = bt_resv6 bt \/ (lo - SBEG) mod KUSERMAP = 0 \/ lo = SBEG + KSPACE + PG)
    /\ (hi = bt_resv6 bt + bt_resv6_len bt \/ (hi - SBEG) mod KUSERMAP = 0 \/ hi = SBEG + KSPACE + PG).

  (* [comment removed for export] *)
  Definition rep_ledger (mdl : Model) : Prop :=
    let h := m_vmmaps mdl in
    (exists F6 : list (word * word),
        Permutation (vm_maps h) (F6 ++ bt_maps0 bt ++ dyn_maps)
        /\ Forall frag_ok F6
        /\ (forall l1 x l2 y, F6 = l1 ++ x :: l2 -> In y (l1 ++ l2) ->
               u (fst x) + u (snd x) <= u (fst y) \/ u (fst y) + u (snd y) <= u (fst x))
        /\ (forall a, in_resv6 a -> (in_ivz F6 a <-> ~ holes a)))
    /\ (forall a, in_ivz (vm_noaccess h) a <-> (in_ivz (bt_noacc0 bt) a /\ ~ committed a /\ ~ holes a))
    /\ (forall a, pg_in_ivz (m_vm_lazy mdl) a <->
          ((pg_in_ivz (bt_lazy0 bt) a /\ ~ committed a /\ ~ holes a) \/ (exists b, In b (dp_storeblocks (a_dep st)) /\ b <= a < b + 2 ^ 23)))
    /\ Forall (fun iv => u (fst iv) mod PG = 0 /\ u (snd iv) mod PG = 0 /\ 0 < u (fst iv) /\ u (fst iv) + u (snd iv) <= CEIL
                       /\ (u (fst iv) + u (snd iv) <= ia_img_lo (bt_ia bt) \/ ia_img_hi (bt_ia bt) <= u (fst iv))) (m_vm_lazy mdl)
    /\ vm_reserved h = bt_reserved bt /\ vm_brk h = bt_brk bt /\ vm_start_brk h = bt_start_brk bt /\ vm_mmap_base h = bt_mmap_base bt
    /\ vm_init_sp h = bt_init_sp bt /\ page_floor (alloc_top h) = CEIL        (* [comment removed for export] *)
    /\ LMIN <= vm_limit h       (* [comment removed for export] *)
    (* [comment removed for export] *)
    /\ Forall (fun e : word * word => 0 < u (snd e)) (vm_noaccess h).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition KBASE : Z := 2 ^ 28 + 2 ^ 27.
  Definition prim_charge : Z :=
    sum_classes (fun c => let r := a_reg st c in r_mapped_user r + r_mapped_user r / 8 + r_mapped_fa r + r_mapped_fa r / 8) 30.
  (* [comment removed for export] *)
  Definition sec_charge : Z := fold_right (fun s acc => sc_mapsz s + sec_hull (sc_map s) (sc_n s) + acc) 0 (a_sec st).
  Definition depot_charge : Z := 2 ^ 20 * Z.of_nat (length (dp_nodeblocks (a_dep st))) + 2 ^ 23 * Z.of_nat (length (dp_storeblocks (a_dep st))).
  Definition rep_budget (mdl : Model) : Prop :=
    A_wf (a_aa st) /\ MInv (a_aa st) mdl
    /\ (forall lo hi, In (lo, hi) (SHC (bt_ia bt) (bt_fs bt)) -> range_allowed (a_aa st) lo hi)
    /\ (forall p n, In (p, n) Lc -> range_allowed (a_aa st) (sh_lo p) (sh_hi p n))
    /\ (forall c, 1 <= c <= 30 -> range_allowed (a_aa st) (sh_lo (region_beg SBEG c)) (sh_lo (region_beg SBEG c) + r_mapped_user (a_reg st c) / 8)
                              /\ range_allowed (a_aa st) (sh_lo (fa_beg SBEG c)) (sh_lo (fa_beg SBEG c) + r_mapped_fa (a_reg st c) / 8))
    /\ (forall s, In s (a_sec st) -> range_allowed (a_aa st) (sh_lo (sc_map s)) (sh_hi (sc_map s) (sc_mapsz s)))
    /\ (forall b, In b (bt_store0 bt :: dp_storeblocks (a_dep st)) -> range_allowed (a_aa st) b (b + 2 ^ 23))
    (* [comment removed for export] *)
    /\ eager_used mdl + A_bytes (a_aa st) <= KBASE + prim_charge + sec_charge + depot_charge + a_shsec st + 8 * a_nres st   (* [comment removed for export] *)
    (* [comment removed for export] *)
    /\ (forall s, In s (a_sec st) -> In (sec_hull_lo (sc_map s), sec_hull_hi (sc_map s) (sc_n s)) (a_aa st)).
End Ledger.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Top.
Context {RC : run_ceil}.
Definition Rep (bt : as_boot) (st : ast) (Lc FF : list (Z * Z)) (M : mem) (mdl : Model) : Prop :=
  cells_hold (bt_segs bt) M (bt_consts bt)
  /\ rep_instance bt st M /\ rep_thread bt st M
  /\ (forall c, 1 <= c <= 30 -> rep_reginfo bt M c (a_reg st c) /\ rep_freearray bt M c (a_reg st c))
  /\ rep_batches bt M (a_tq st) /\ rep_batches bt M (a_gq st)
  /\ rep_secondary bt st M /\ rep_headers bt st Lc M
  /\ rep_depot bt st M /\ rep_fake bt st FF M /\ rep_ialloc bt st M
  /\ rep_shadow bt st Lc M
  /\ rep_ledger bt st mdl /\ rep_budget bt st Lc mdl
  (* [comment removed for export] *)
  /\ (forall p n, In (p, n) Lc -> writableZ (bt_segs bt) M p (p + n) /\ writableZ (bt_segs bt) M (sh_lo p) (sh_hi p n))
  /\ (forall f k, In (f, k) FF -> writableZ (bt_segs bt) M (sh_lo f) (sh_hi f (FS k)))
  /\ cellZ (bt_segs bt) M (ia_rtc_sb (bt_ia bt)) 8 SB /\ cellZ (bt_segs bt) M (ia_rtc_uar (bt_ia bt)) 4 1
  (* [comment removed for export] *)
  /\ ((forall z, shmaps z -> M (Z_to_bv 64 z) <> None)
      /\ (a_gq st <> [] -> forall a : word, IB bt + 896 <= bv_unsigned a < IB bt + 904 -> M a <> None)).

Definition bounds (st : ast) (Lc : list (Z * Z)) (B C K : Z) : Prop :=
  0 <= PHI Lc <= B /\ Z.of_nat (length Lc) <= C /\ 0 <= a_kact st <= K.

(* [comment removed for export] *)
Definition NEV : Z := KCAP / EVT.
Definition MUMAX : Z := KUSERMAP * NEV.                                                              (* [comment removed for export] *)
Definition PRIMMAX : Z := MUMAX + MUMAX / 8 + (MUMAX / 8 + 30 * KFAMAP) + (MUMAX / 8 + 30 * KFAMAP) / 8.   (* [comment removed for export] *)
Definition QCAP : Z := 2 ^ 28 + 2 ^ 21.                                                              (* [comment removed for export] *)
(* [comment removed for export] *)
Definition SECMAPS : Z := GBUDGET + QCAP + 12296 * NEV.
Definition SECMAX : Z := SECMAPS + SECMAPS / 8.                                                      (* [comment removed for export] *)
Definition RESMAX : Z := 2 * PG * NEV.                                                               (* [comment removed for export] *)
Definition DEPOT0 : Z := 2 ^ 20 + 2 ^ 24.
Definition DEPOTMAX : Z := DEPOT0 + 88 * NEV + 2 ^ 20 + 2 ^ 24.
Definition ROOMSLACK : Z := 2 ^ 25.        (* [comment removed for export] *)
Definition BUDGET_TOTAL : Z := KBASE + PRIMMAX + SECMAX + DEPOTMAX + RESMAX + 2 ^ 23 + ROOMSLACK + 2 ^ 24.

Lemma budget_closed : BUDGET_TOTAL <= LMIN.
Proof. rewrite LMIN_val. vm_compute. intros H. discriminate H. Qed.


(* [comment removed for export] *)
Definition holes_le (h : option Z) (st : ast) : Prop :=
  forall c, (r_uhole (a_reg st c) = true \/ r_fhole (a_reg st c) = true) ->
            exists n, h = Some n /\ n <= 64512 /\ c = class_of (needed n).

(* [comment removed for export] *)
Definition AAINVP (P : ast -> Prop) (bt : as_boot) (Lc FF : list (Z * Z)) (B C K : Z) (M : mem) (mdl : Model) : Prop :=
  exists st, WF bt st Lc FF /\ Rep bt st Lc FF M mdl /\ (bounds st Lc B C K /\ P st) /\ BackingAlgebra.model_ivs_wf mdl.

(* [comment removed for export] *)
Definition AAINV_H (bt : as_boot) (h : option Z) := AAINVP (holes_le h) bt.
(* [comment removed for export] *)
Definition AAINV (bt : as_boot) := AAINV_H bt None.



End Top.
