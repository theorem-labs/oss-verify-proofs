(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LMeasure.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Definition mem := word -> option byte.
Definition meq (m1 m2 : mem) : Prop := forall x, m1 x = m2 x.

Lemma meq_refl : forall m, meq m m. Proof. intros m x; reflexivity. Qed.
Lemma meq_sym : forall m1 m2, meq m1 m2 -> meq m2 m1. Proof. intros m1 m2 H x; symmetry; apply H. Qed.
Lemma meq_trans : forall m1 m2 m3, meq m1 m2 -> meq m2 m3 -> meq m1 m3.
Proof. intros m1 m2 m3 H1 H2 x. rewrite H1. apply H2. Qed.

Lemma meq_write_to_mem : forall m1 m2 a bs, meq m1 m2 -> meq (write_to_mem m1 a bs) (write_to_mem m2 a bs).
Proof.
  intros m1 m2 a bs. revert m1 m2 a. induction bs as [|b bs IH]; intros m1 m2 a H; cbn; [exact H|].
  apply IH. intros x. destruct (bv_eqb x a); [reflexivity| apply H].
Qed.

Definition b0 : byte := Z_to_bv 8 0.

(* [comment removed for export] *)
Definition in_rangesb (L : list (word * word)) (x : word) : bool :=
  existsb (fun r => (bv_unsigned (fst r) <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned (fst r) + bv_unsigned (snd r))) L.

Lemma in_rangesb_true : forall L x, in_rangesb L x = true <->
  exists lo sz, In (lo, sz) L /\ bv_unsigned lo <= bv_unsigned x < bv_unsigned lo + bv_unsigned sz.
Proof.
  intros L x. unfold in_rangesb. rewrite existsb_exists. split.
  - intros ([lo sz] & Hin & Hb). cbn in Hb. exists lo, sz. split; [exact Hin| lia].
  - intros (lo & sz & Hin & Hb). exists (lo, sz). split; [exact Hin| cbn; lia].
Qed.

Lemma in_rangesb_false : forall L x, in_rangesb L x = false <->
  forall lo sz, In (lo, sz) L -> ~ (bv_unsigned lo <= bv_unsigned x < bv_unsigned lo + bv_unsigned sz).
Proof.
  intros L x. split.
  - intros H lo sz Hin Hr. enough (in_rangesb L x = true) by congruence. apply in_rangesb_true. eauto.
  - intros H. destruct (in_rangesb L x) eqn:E; [|reflexivity]. exfalso.
    apply in_rangesb_true in E. destruct E as (lo & sz & Hin & Hr). exact (H lo sz Hin Hr).
Qed.

Lemma in_rangesb_app : forall L1 L2 x, in_rangesb (L1 ++ L2) x = in_rangesb L1 x || in_rangesb L2 x.
Proof. intros. unfold in_rangesb. apply existsb_app. Qed.

(* [comment removed for export] *)
Definition lmem (zf : word -> bool) (mv : mem) : mem :=
  fun x => match mv x with
           | Some b => Some b
           | None => if zf x then Some b0 else None
           end.

Lemma lmem_some : forall zf mv x b, mv x = Some b -> lmem zf mv x = Some b.
Proof. intros zf mv x b H. unfold lmem. rewrite H. reflexivity. Qed.

Lemma lmem_ext : forall zf mv x, mv x <> None -> lmem zf mv x = mv x.
Proof. intros zf mv x H. unfold lmem. destruct (mv x); [reflexivity| congruence]. Qed.

Lemma lmem_false : forall mv, meq (lmem (fun _ => false) mv) mv.
Proof. intros mv x. unfold lmem. destruct (mv x); reflexivity. Qed.

Lemma lmem_write_to_mem : forall zf mv a bs,
  meq (write_to_mem (lmem zf mv) a bs) (lmem zf (write_to_mem mv a bs)).
Proof.
  intros zf mv a bs. revert mv a. induction bs as [|b bs IH]; intros mv a x; cbn; [reflexivity|].
  rewrite <- (IH (fun y => if bv_eqb y a then Some b else mv y) (a + 1)%bv x).
  revert x. apply meq_write_to_mem. intros y. unfold lmem.
  destruct (bv_eqb y a); reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.
Context {ACEIL : Ceil}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition noseg (x : word) : Prop :=
  forall s, In s segs ->
    ~ (Z.of_N (seg_base s) <= bv_unsigned x < Z.of_N (seg_base s) + Z.of_N (seg_size s)).

Lemma find_segment_noseg : forall x n, noseg x -> 0 < n -> find_segment segs (bv_unsigned x) n = None.
Proof.
  intros x n Hx Hn. unfold noseg in Hx. induction segs as [|s r IH] in Hx |- *; [reflexivity|].
  cbn. destruct (Z.leb_spec0 (Z.of_N (seg_base s)) (bv_unsigned x));
  destruct (Z.leb_spec0 (bv_unsigned x + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s))); cbn.
  - exfalso. apply (Hx s (or_introl eq_refl)). lia.
  - apply IH. intros s' Hs'. apply Hx. right; exact Hs'.
  - apply IH. intros s' Hs'. apply Hx. right; exact Hs'.
  - apply IH. intros s' Hs'. apply Hx. right; exact Hs'.
Qed.

Lemma memory_read_noseg : forall x n, noseg x -> (0 < n)%N -> memory_read segs x n = None.
Proof. intros x n Hx Hn. unfold memory_read. rewrite find_segment_noseg; [reflexivity| exact Hx| lia]. Qed.

Lemma seg_rom_noseg : forall x, noseg x -> seg_rom segs x = None.
Proof. intros x Hx. unfold seg_rom. rewrite memory_read_noseg; [reflexivity| exact Hx| lia]. Qed.

Lemma wview_noseg : forall m x, noseg x -> m x = None -> wview segs m x = None.
Proof. intros m x Hx Hm. unfold wview. rewrite Hm. rewrite find_segment_noseg; [reflexivity| exact Hx| lia]. Qed.

Lemma ro_addr_noseg : forall x, noseg x -> ro_addr segs x = false.
Proof. intros x Hx. unfold ro_addr. rewrite find_segment_noseg; [reflexivity| exact Hx| lia]. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zf_noseg (zf : word -> bool) : Prop := forall x, zf x = true -> noseg x /\ bv_unsigned x < TASK_SIZE.
Lemma zf_noseg_noseg : forall zf x, zf_noseg zf -> zf x = true -> noseg x.
Proof. intros zf x H E. exact (proj1 (H x E)). Qed.
Lemma zf_noseg_task : forall zf x, zf_noseg zf -> zf x = true -> bv_unsigned x < TASK_SIZE.
Proof. intros zf x H E. exact (proj2 (H x E)). Qed.
Definition lazy_noseg (L : list (word * word)) : Prop := forall x, in_rangesb L x = true -> noseg x.

Section ZF.
Variable zf : word -> bool.
Hypothesis HZ : zf_noseg zf.

Lemma mrd_lmem : forall mv x b,
  mrd segs mv x = Some b -> mrd segs (lmem zf mv) x = Some b.
Proof.
  intros mv x b H. unfold mrd, lmem in *. destruct (mv x); [exact H|].
  destruct (zf x) eqn:E; [|exact H].
  rewrite (seg_rom_noseg x (proj1 (HZ x E))) in H. discriminate.
Qed.

Lemma mrd_lmem_inv : forall mv x b,
  mrd segs (lmem zf mv) x = Some b ->
  mv x = Some b \/ (mv x = None /\ seg_rom segs x = Some b /\ zf x = false)
  \/ (mv x = None /\ zf x = true /\ b = b0).
Proof.
  intros mv x b H. unfold mrd, lmem in H. destruct (mv x) as [c|] eqn:E.
  - left. congruence.
  - destruct (zf x) eqn:E2.
    + right; right. injection H as <-. auto.
    + right; left. auto.
Qed.

Lemma wview_lmem : forall mv x, wview segs mv x <> None -> wview segs (lmem zf mv) x <> None.
Proof.
  intros mv x H. unfold wview, lmem in *. destruct (mv x); [exact H|].
  destruct (zf x); [discriminate| exact H].
Qed.

Lemma wview_lmem_zf : forall mv x, zf x = true -> wview segs (lmem zf mv) x <> None.
Proof. intros mv x H. unfold wview, lmem. destruct (mv x); [discriminate|]. rewrite H. discriminate. Qed.

Lemma bytes_at_lmem : forall mv a bs,
  bytes_at segs mv a bs -> bytes_at segs (lmem zf mv) a bs.
Proof.
  intros mv a bs (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros i Hi. pose proof (H i Hi) as Hb.
  destruct (nth_error bs i) as [b|] eqn:E; [| exfalso; apply nth_error_None in E; lia].
  apply mrd_lmem; assumption.
Qed.

Lemma wr_at_lmem : forall mv a n, wr_at segs mv a n -> wr_at segs (lmem zf mv) a n.
Proof.
  intros mv a n (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros i Hi. apply wview_lmem. apply H. exact Hi.
Qed.

Lemma cells_at_lmem : forall mv a cs,
  cells_at segs mv a cs -> cells_at segs (lmem zf mv) a cs.
Proof. intros mv a cs [Hwf Hb]. split; [exact Hwf|]. apply bytes_at_lmem; assumption. Qed.

Lemma rw_cells_lmem : forall mv a cs,
  rw_cells segs mv a cs -> rw_cells segs (lmem zf mv) a cs.
Proof. intros mv a cs [Hc Hw]. split; [apply cells_at_lmem; assumption| apply wr_at_lmem; assumption]. Qed.

Lemma ro_cells_lmem : forall mv a cs,
  ro_cells segs mv a cs -> ro_cells segs (lmem zf mv) a cs.
Proof. intros mv a cs H. apply cells_at_lmem; assumption. Qed.

Lemma stk_lmem : forall mv lo hi,
  stk segs mv lo hi -> stk segs (lmem zf mv) lo hi.
Proof.
  intros mv lo hi (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (H a Ha) as [Hw [b Hb]]. split; [apply wview_lmem; exact Hw|].
  exists b. apply mrd_lmem; assumption.
Qed.

Lemma mem_inv_lmem : forall mv,
  mem_inv segs mv -> mem_inv segs (lmem zf mv).
Proof.
  intros mv H x b Hx. unfold lmem in Hx. destruct (mv x) as [c|] eqn:E.
  - eapply H; eauto.
  - destruct (zf x) eqn:E2; [|discriminate]. right. split; [apply ro_addr_noseg; exact (proj1 (HZ x E2)) | exact (proj2 (HZ x E2))].
Qed.

Lemma bytes_at_lmem_zeros : forall mv a n,
  0 <= a -> a + Z.of_nat n <= 2^64 ->
  (forall i, 0 <= i < Z.of_nat n -> mv (wa (a + i)) = None /\ zf (wa (a + i)) = true) ->
  bytes_at segs (lmem zf mv) a (repeat b0 n).
Proof.
  intros mv a n H0 H1 H. split; [exact H0|]. rewrite repeat_length. split; [exact H1|].
  intros i Hi. destruct (H (Z.of_nat i) ltac:(lia)) as [Hm Hl].
  unfold mrd, lmem. rewrite Hm, Hl. symmetry. apply nth_error_repeat. exact Hi.
Qed.

Lemma wr_at_lmem_zf : forall mv a n,
  0 <= a -> a + n <= 2^64 ->
  (forall i, 0 <= i < n -> zf (wa (a + i)) = true) ->
  wr_at segs (lmem zf mv) a n.
Proof.
  intros mv a n H0 H1 H. split; [exact H0|]. split; [exact H1|].
  intros i Hi. apply wview_lmem_zf. apply H. exact Hi.
Qed.

End ZF.

(* [comment removed for export] *)
Lemma page_size_eq : page_size = 4096. Proof. reflexivity. Qed.

Lemma page_base_unsigned : forall x : word,
  bv_unsigned (page_base x) = bv_unsigned x / 4096 * 4096.
Proof.
  intros x. unfold page_base, page_base_of. rewrite page_size_eq. rewrite Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range 64 x) as Hx. change (bv_modulus 64) with (2^64) in Hx.
  apply bv_wrap_small. change (bv_modulus 64) with (2^64).
  pose proof (Z.div_mod (bv_unsigned x) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned x) 4096 ltac:(lia)). lia.
Qed.

Lemma page_base_le : forall x : word,
  bv_unsigned (page_base x) <= bv_unsigned x < bv_unsigned (page_base x) + 4096.
Proof.
  intros x. rewrite page_base_unsigned.
  pose proof (Z.div_mod (bv_unsigned x) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned x) 4096 ltac:(lia)). lia.
Qed.

Lemma page_in_ranges_true : forall p L, page_in_ranges p L = true <->
  exists lo sz, In (lo, sz) L /\ bv_unsigned lo <= bv_unsigned p /\ bv_unsigned p + page_size <= bv_unsigned lo + bv_unsigned sz.
Proof.
  intros p L. unfold page_in_ranges. rewrite existsb_exists. split.
  - intros ([lo sz] & Hin & Hb). cbn in Hb. apply andb_true_iff in Hb as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. exists lo, sz. auto.
  - intros (lo & sz & Hin & H1 & H2). exists (lo, sz). split; [exact Hin|]. cbn.
    rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.leb_le _ _) H2). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma page_in_ranges_bytes : forall L (x : word),
  page_in_ranges (page_base x) L = true -> in_rangesb L x = true.
Proof.
  intros L x H. apply page_in_ranges_true in H. destruct H as (lo & sz & Hin & H1 & H2).
  apply in_rangesb_true. exists lo, sz. split; [exact Hin|].
  pose proof (page_base_le x). rewrite page_size_eq in H2. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition gwin := list (Z * Z).

Definition in_winb (G : gwin) (x : word) : bool :=
  existsb (fun r => (fst r <=? bv_unsigned x) && (bv_unsigned x <? snd r)) G.

Lemma in_winb_true : forall G x, in_winb G x = true <-> exists lo hi, In (lo, hi) G /\ lo <= bv_unsigned x < hi.
Proof.
  intros G x. unfold in_winb. rewrite existsb_exists. split.
  - intros ([lo hi] & Hin & Hb). cbn in Hb. exists lo, hi. split; [exact Hin| lia].
  - intros (lo & hi & Hin & Hb). exists (lo, hi). split; [exact Hin| cbn; lia].
Qed.

Lemma in_winb_false : forall G x, in_winb G x = false <-> forall lo hi, In (lo, hi) G -> ~ (lo <= bv_unsigned x < hi).
Proof.
  intros G x. split.
  - intros H lo hi Hin Hr. enough (in_winb G x = true) by congruence. apply in_winb_true. eauto.
  - intros H. destruct (in_winb G x) eqn:E; [|reflexivity]. exfalso.
    apply in_winb_true in E. destruct E as (lo & hi & Hin & Hr). exact (H lo hi Hin Hr).
Qed.

Lemma in_winb_cons : forall r G x,
  in_winb (r :: G) x = ((fst r <=? bv_unsigned x) && (bv_unsigned x <? snd r)) || in_winb G x.
Proof. reflexivity. Qed.

Lemma in_winb_app : forall G1 G2 x, in_winb (G1 ++ G2) x = in_winb G1 x || in_winb G2 x.
Proof. intros. unfold in_winb. apply existsb_app. Qed.

Definition win_ok (r : Z * Z) : Prop :=
  0 <= fst r /\ fst r <= snd r /\ snd r <= 2^64 /\ fst r mod 4096 = 0 /\ snd r mod 4096 = 0.

(* [comment removed for export] *)
Fixpoint range_pages (lo : Z) (k : nat) : list word :=
  match k with
  | O => []
  | S k' => wa lo :: range_pages (lo + 4096) k'
  end.

Definition win_npages (r : Z * Z) : nat := Z.to_nat ((snd r - fst r) / 4096).
Definition win_pages (r : Z * Z) : list word := range_pages (fst r) (win_npages r).

Fixpoint gpages (G : gwin) : list word :=
  match G with
  | [] => []
  | r :: G' => win_pages r ++ gpages G'
  end.

Definition npages (G : gwin) : Z := Z.of_nat (length (gpages G)).

Lemma range_pages_length : forall lo k, length (range_pages lo k) = k.
Proof. intros lo k; revert lo; induction k; intros; cbn; [reflexivity| now rewrite IHk]. Qed.

Lemma range_pages_in : forall lo k (x : word),
  0 <= lo -> lo mod 4096 = 0 -> lo + 4096 * Z.of_nat k <= 2^64 ->
  lo <= bv_unsigned x < lo + 4096 * Z.of_nat k -> In (page_base x) (range_pages lo k).
Proof.
  intros lo k; revert lo; induction k as [|k IH]; intros lo x H0 Hal Hhi Hx; [lia|].
  cbn [range_pages]. destruct (Z.ltb_spec0 (bv_unsigned x) (lo + 4096)).
  - left. apply bv_eq. rewrite page_base_unsigned. rewrite wa_unsigned by lia.
    pose proof (Z.div_mod (bv_unsigned x) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned x) 4096 ltac:(lia)).
    pose proof (Z.div_mod lo 4096 ltac:(lia)). nia.
  - right. apply IH; lia.
Qed.

Lemma win_pages_in : forall r (x : word), win_ok r ->
  fst r <= bv_unsigned x < snd r -> In (page_base x) (win_pages r).
Proof.
  intros [lo hi] x (H0 & H1 & H2 & H3 & H4) Hx. cbn in *. unfold win_pages, win_npages. cbn.
  assert (E : 4096 * Z.of_nat (Z.to_nat ((hi - lo) / 4096)) = hi - lo).
  { rewrite Z2Nat.id by (apply Z.div_pos; lia).
    pose proof (Z.div_mod (hi - lo) 4096 ltac:(lia)).
    assert ((hi - lo) mod 4096 = 0).
    { rewrite Zminus_mod, H3, H4. reflexivity. }
    lia. }
  apply range_pages_in; lia.
Qed.

Lemma gpages_in : forall G x, Forall win_ok G -> in_winb G x = true -> In (page_base x) (gpages G).
Proof.
  intros G x HG Hx. induction HG as [|r G Hr HG IH]; [discriminate|].
  cbn. rewrite in_winb_cons in Hx. apply in_or_app. apply orb_true_iff in Hx as [Hx|Hx].
  - left. apply win_pages_in; [exact Hr|]. apply andb_true_iff in Hx as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. lia.
  - right. apply IH. exact Hx.
Qed.

Lemma npages_cons : forall r G, npages (r :: G) = Z.of_nat (win_npages r) + npages G.
Proof. intros. unfold npages. cbn. rewrite length_app. unfold win_pages. rewrite range_pages_length. lia. Qed.

Lemma npages_nonneg : forall G, 0 <= npages G.
Proof. intros. unfold npages. lia. Qed.

Lemma win_npages_eq : forall lo hi, win_ok (lo, hi) -> Z.of_nat (win_npages (lo, hi)) = (hi - lo) / 4096.
Proof. intros lo hi (H0 & H1 & _). unfold win_npages. cbn. rewrite Z2Nat.id; [reflexivity|]. cbn in *. apply Z.div_pos; lia. Qed.

(* [comment removed for export] *)
Record lghost := mkG { g_win : gwin; g_res : Z }.

(* [comment removed for export] *)
Definition eager_used (mo : Model) : Z :=
  live_bytes (maps_subtract_all (vm_backed_maps (m_vmmaps mo)) (m_vm_lazy mo)).

Lemma vm_backing_used_split : forall mo,
  vm_backing_used mo = eager_used mo + Z.of_nat (length (m_vm_materialized mo)) * page_size.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition BINV (mo : Model) (g : lghost) : Prop :=
  Forall win_ok (g_win g) /\ 0 <= g_res g /\
  eager_used mo + 4096 * npages (g_win g) + g_res g <= vm_limit (m_vmmaps mo).

Lemma BINV_res_le : forall mo G R R', BINV mo (mkG G R) -> 0 <= R' <= R -> BINV mo (mkG G R').
Proof. intros mo G R R' (H1 & H2 & H3) HR. unfold BINV in *. cbn in *. split; [exact H1|]. split; [lia|]. lia. Qed.

(* [comment removed for export] *)
Lemma BINV_open : forall mo G R lo hi,
  BINV mo (mkG G R) -> win_ok (lo, hi) -> 4096 * ((hi - lo) / 4096) <= R ->
  BINV mo (mkG ((lo, hi) :: G) (R - 4096 * ((hi - lo) / 4096))).
Proof.
  intros mo G R lo hi (H1 & H2 & H3) Hw HR. unfold BINV. cbn in *. split; [constructor; assumption|].
  rewrite npages_cons, win_npages_eq by exact Hw.
  pose proof Hw as (A & B & _). cbn in A, B.
  assert (0 <= (hi - lo) / 4096) by (apply Z.div_pos; lia).
  split; [lia|]. lia.
Qed.

(* [comment removed for export] *)
Definition lzf (mo : Model) : word -> bool :=
  fun x => in_rangesb (m_vm_lazy mo) x && negb (in_rangesb (vm_noaccess (m_vmmaps mo)) x).

Lemma lzf_lazy : forall mo x, lzf mo x = true -> in_rangesb (m_vm_lazy mo) x = true.
Proof. intros mo x H. unfold lzf in H. apply andb_true_iff in H. exact (proj1 H). Qed.

(* [comment removed for export] *)
Definition magree (zf : word -> bool) (X : word -> Prop) (mv mr : mem) : Prop :=
  forall x, mr x = lmem zf mv x \/ (mv x = None /\ noseg x /\ X x).

Lemma magree_of_meq : forall zf X mv mr, meq mr (lmem zf mv) -> magree zf X mv mr.
Proof. intros zf X mv mr H x. left. apply H. Qed.

Lemma magree_some : forall zf X mv mr x b, magree zf X mv mr -> mv x = Some b -> mr x = Some b.
Proof.
  intros zf X mv mr x b H Hx. destruct (H x) as [E | (E & _)]; [| congruence]. rewrite E. apply lmem_some. exact Hx.
Qed.

Lemma magree_seg : forall zf X mv mr x, magree zf X mv mr -> ~ noseg x -> mr x = lmem zf mv x.
Proof. intros zf X mv mr x H Hs. destruct (H x) as [E | (_ & E & _)]; [exact E| contradiction]. Qed.

Lemma magree_X_mono : forall zf (X X' : word -> Prop) mv mr,
  magree zf X mv mr -> (forall x, X x -> X' x) -> magree zf X' mv mr.
Proof. intros zf X X' mv mr H HX x. destruct (H x) as [E | (A & B & C)]; [left; exact E| right; auto]. Qed.

(* [comment removed for export] *)
Lemma magree_transfer : forall (zf zf' : word -> bool) (X X' : word -> Prop) mv mr mv' mr',
  magree zf X mv mr ->
  (forall x, mr' x = lmem zf' mv' x
             \/ (mr' x = mr x /\ mv' x = mv x /\ zf' x = zf x /\ (X x -> X' x))) ->
  magree zf' X' mv' mr'.
Proof.
  intros zf zf' X X' mv mr mv' mr' Hm H x. destruct (H x) as [E | (E1 & E2 & E3 & E4)]; [left; exact E|].
  destruct (Hm x) as [F | (F1 & F2 & F3)].
  - left. rewrite E1, F. unfold lmem. rewrite E2, E3. reflexivity.
  - right. rewrite E2. auto.
Qed.

(* [comment removed for export] *)
Definition lexc (mo : Model) (G : gwin) (x : word) : Prop := lzf mo x = false \/ in_winb G x = true.

(* [comment removed for export] *)
Definition lrel (mo : Model) (G : gwin) (mv mr : mem) : Prop :=
  magree (lzf mo) (lexc mo G) mv mr /\
  (forall x, in_rangesb (m_vm_lazy mo) x = true -> in_winb G x = false -> mv x = None).

Lemma lrel_some : forall mo G mv mr x b, lrel mo G mv mr -> mv x = Some b -> mr x = Some b.
Proof. intros mo G mv mr x b [H _] Hx. eapply magree_some; eassumption. Qed.

Lemma lrel_pool : forall mo G mv mr x, lrel mo G mv mr ->
  lzf mo x = true -> in_winb G x = false -> mr x = Some b0.
Proof.
  intros mo G mv mr x [H Hhid] Hz Hw. pose proof (Hhid x (lzf_lazy mo x Hz) Hw) as Hv.
  destruct (H x) as [E | (_ & _ & [E|E])]; [| congruence| congruence].
  rewrite E. unfold lmem. rewrite Hv, Hz. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lrel_vis_win : forall mo G mv mr x, lrel mo G mv mr ->
  in_rangesb (m_vm_lazy mo) x = true -> mv x <> None -> in_winb G x = true.
Proof.
  intros mo G mv mr x [_ H] HL Hv. destruct (in_winb G x) eqn:E; [reflexivity|].
  exfalso. apply Hv. apply H; assumption.
Qed.

(* [comment removed for export] *)
Definition vdom (mo : Model) (mv : mem) : Prop :=
  forall x, mv x <> None ->
    alloc_ceiling <= bv_unsigned x \/ ~ noseg x \/ in_rangesb (vm_maps (m_vmmaps mo)) x = true.

(* [comment removed for export] *)
Definition matok (G : gwin) (mat : list word) : Prop :=
  List.NoDup mat /\ forall p, In p mat -> In p (gpages G).

Lemma matok_length : forall G mat, matok G mat -> Z.of_nat (length mat) <= npages G.
Proof.
  intros G mat [Hnd Hin]. unfold npages. apply inj_le. apply NoDup_incl_length; [exact Hnd|].
  intros p Hp. apply Hin. exact Hp.
Qed.

Lemma matok_nil : forall G, matok G [].
Proof. intros G. split; [constructor| intros p []]. Qed.

Lemma matok_open : forall r G mat, matok G mat -> matok (r :: G) mat.
Proof. intros r G mat [A B]. split; [exact A|]. intros p Hp. cbn. apply in_or_app. right. apply B. exact Hp. Qed.

(* [comment removed for export] *)
Definition real (mo : Model) (mat : list word) : Model := with_vm_backing (m_vm_lazy mo) mat mo.

(* [comment removed for export] *)
Lemma in_rangesb_inzr : forall L (x : word), in_rangesb L x = inzr L (bv_unsigned x).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Record LOK (mo : Model) : Prop := mkLOK {
  lok_halt : m_halted mo = None;
  lok_resv : vm_reserved (m_vmmaps mo) = segments_reserved segs;
  (* [comment removed for export] *)
  lok_top : alloc_top (m_vmmaps mo) = alloc_ceiling;
  (* [comment removed for export] *)
  lok_maps_ceil : forall b k, In (b, k) (vm_maps (m_vmmaps mo)) -> bv_unsigned b + bv_unsigned k <= alloc_ceiling;
  lok_maps_pwd : pwd (vm_maps (m_vmmaps mo));
  lok_na_ceil : forall b k, In (b, k) (vm_noaccess (m_vmmaps mo)) -> bv_unsigned b + bv_unsigned k <= 2^64;   (* [comment removed for export] *)
  lok_lazy_ceil : forall lo sz, In (lo, sz) (m_vm_lazy mo) -> bv_unsigned lo + bv_unsigned sz <= alloc_ceiling;
  (* [comment removed for export] *)
  lok_lazy_noseg : lazy_noseg (m_vm_lazy mo);
  lok_lazy_maps : forall x : word, in_rangesb (m_vm_lazy mo) x = true -> in_rangesb (vm_maps (m_vmmaps mo)) x = true;
  lok_na_maps : forall x : word, in_rangesb (vm_noaccess (m_vmmaps mo)) x = true -> in_rangesb (vm_maps (m_vmmaps mo)) x = true
}.

Lemma lok_zf_noseg : forall mo, LOK mo -> zf_noseg (lzf mo).
Proof.
  intros mo H x Hx. pose proof (lzf_lazy mo x Hx) as HLz. split; [apply (lok_lazy_noseg mo H); exact HLz|].
  apply in_rangesb_true in HLz as (lo & sz & Hin & Hb). pose proof (lok_lazy_ceil mo H lo sz Hin) as Hc.
  pose proof (@alloc_ceiling_hi ACEIL). unfold TASK_SIZE. lia.
Qed.

(* [comment removed for export] *)
Definition no_wx : Prop :=
  (forall s, In s segs -> seg_executable s && seg_writable s = false)
  /\ (forall s, In s segs -> page_round_up_Z (Z.of_N (seg_base s) + Z.of_N (seg_size s)) < 2^64).

(* [comment removed for export] *)
Lemma seg_in_reservation : forall s (x : word), In s segs ->
  (forall s, In s segs -> page_round_up_Z (Z.of_N (seg_base s) + Z.of_N (seg_size s)) < 2^64) ->
  Z.of_N (seg_base s) <= bv_unsigned x < Z.of_N (seg_base s) + Z.of_N (seg_size s) ->
  in_rangesb (segments_reserved segs) x = true.
Proof.
  intros s x Hs Hok Hx. apply in_rangesb_true. unfold segments_reserved.
  exists (fst (segment_reservation s)), (snd (segment_reservation s)). split.
  - apply in_map_iff. exists s. split; [| exact Hs]. destruct (segment_reservation s); reflexivity.
  - pose proof (Hok s Hs) as Hhi. unfold segment_reservation. cbn [fst snd].
    unfold page_round_up_Z, page_round_down_Z in *. change page_size with 4096 in *.
    pose proof (N2Z.is_nonneg (seg_base s)). pose proof (N2Z.is_nonneg (seg_size s)).
    set (b := Z.of_N (seg_base s)) in *. set (sz := Z.of_N (seg_size s)) in *.
    assert (Hlo : 0 <= b / 4096 * 4096 <= b) by (Z.div_mod_to_equations; lia).
    assert (Hhi2 : b + sz <= (b + sz + 4096 - 1) / 4096 * 4096) by (Z.div_mod_to_equations; lia).
    rewrite !Z_to_bv_unsigned. rewrite !bv_wrap_small by (change (bv_modulus 64) with (2^64); lia). lia.
Qed.

Lemma region_free_false_of : forall maps (a n b sz : word) (x : word),
  region_free maps a n = true -> In (b, sz) maps ->
  bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n ->
  ~ (bv_unsigned b <= bv_unsigned x < bv_unsigned b + bv_unsigned sz).
Proof.
  intros maps a n b sz x Hf Hin Hx Hb. pose proof (region_free_In maps a n b sz Hf Hin) as Ho.
  unfold iv_overlap in Ho. apply andb_false_iff in Ho as [Ho|Ho]; apply Z.ltb_ge in Ho; lia.
Qed.

(* [comment removed for export] *)
Lemma region_free_noseg : forall maps a n (x : word), no_wx ->
  region_free (segments_reserved segs ++ maps) a n = true ->
  bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n -> noseg x.
Proof.
  intros maps a n x [_ Hok] Hf Hx s Hs Hsx.
  pose proof (seg_in_reservation s x Hs Hok Hsx) as Hr. apply in_rangesb_true in Hr as (lo & sz & Hin & Hlx).
  eapply (region_free_false_of _ a n lo sz x); [exact Hf| apply in_or_app; left; exact Hin| exact Hx| exact Hlx].
Qed.


(* [comment removed for export] *)
Lemma m_vm_lazy_wvb : forall l p mo, m_vm_lazy (with_vm_backing l p mo) = l. Proof. reflexivity. Qed.
Lemma m_vm_materialized_wvb : forall l p mo, m_vm_materialized (with_vm_backing l p mo) = p. Proof. reflexivity. Qed.
Lemma m_vmmaps_wvb : forall l p mo, m_vmmaps (with_vm_backing l p mo) = m_vmmaps mo. Proof. reflexivity. Qed.
Lemma m_halted_wvb : forall l p mo, m_halted (with_vm_backing l p mo) = m_halted mo. Proof. reflexivity. Qed.
Lemma m_fds_wvb : forall l p mo, m_fds (with_vm_backing l p mo) = m_fds mo. Proof. reflexivity. Qed.
Lemma m_fs_wvb : forall l p mo, m_fs (with_vm_backing l p mo) = m_fs mo. Proof. reflexivity. Qed.
Lemma m_tid_wvb : forall l p mo, m_tid (with_vm_backing l p mo) = m_tid mo. Proof. reflexivity. Qed.
Lemma wvb_wvb : forall l p l0 p0 mo, with_vm_backing l p (with_vm_backing l0 p0 mo) = with_vm_backing l p mo.
Proof. reflexivity. Qed.

Lemma with_vm_backing_id : forall mo,
  with_vm_backing (m_vm_lazy mo) (m_vm_materialized mo) mo = mo.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.   (* [comment removed for export] *)

Lemma vm_backing_used_wvb : forall l p mo,
  vm_backing_used (with_vm_backing l p mo) =
  live_bytes (maps_subtract_all (vm_backed_maps (m_vmmaps mo)) l) + Z.of_nat (length p) * page_size.
Proof. reflexivity. Qed.

Lemma real_lazy : forall mo mat, m_vm_lazy (real mo mat) = m_vm_lazy mo. Proof. reflexivity. Qed.
Lemma real_mat : forall mo mat, m_vm_materialized (real mo mat) = mat. Proof. reflexivity. Qed.
Lemma real_vmmaps : forall mo mat, m_vmmaps (real mo mat) = m_vmmaps mo. Proof. reflexivity. Qed.
Lemma real_halted : forall mo mat, m_halted (real mo mat) = m_halted mo. Proof. reflexivity. Qed.
Lemma real_fds : forall mo mat, m_fds (real mo mat) = m_fds mo. Proof. reflexivity. Qed.
Lemma real_fs : forall mo mat, m_fs (real mo mat) = m_fs mo. Proof. reflexivity. Qed.
Lemma real_tid : forall mo mat, m_tid (real mo mat) = m_tid mo. Proof. reflexivity. Qed.
Lemma real_real : forall mo mat mat', real (real mo mat) mat' = real mo mat'. Proof. reflexivity. Qed.
Lemma real_used : forall mo mat, vm_backing_used (real mo mat) = eager_used mo + Z.of_nat (length mat) * page_size.
Proof. reflexivity. Qed.
Lemma real_eager : forall mo mat, eager_used (real mo mat) = eager_used mo. Proof. reflexivity. Qed.
Lemma real_self : forall mo, real mo (m_vm_materialized mo) = mo.
Proof. intros. apply with_vm_backing_id. Qed.

End WithSegs.
