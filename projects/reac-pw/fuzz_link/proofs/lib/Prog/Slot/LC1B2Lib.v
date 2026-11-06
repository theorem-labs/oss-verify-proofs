(* reac-pw/fuzz_link, PLAIN image: segment B2 of the op_write arm (model_write's return at 0x13ff8
   to the call of free(own) at 0x1405c). This file holds the generic word, byte and memory facts the
   walk uses: literal words, byte-list equality at an address, the pointwise transport of a memory
   view across a call's footprint, and the two bounds a block outside the image's reserved segments
   gives (the shape of snprintf.v's img_free_bound, re-derived here so this file needs none of the
   printf layer). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import
  PropExec MState Mem Cells Exec Frame Step Tac Bytes Arr.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem printf_facts_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Literal words
   ========================================================================== *)

Lemma c1b2_uns : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (wz z) = z.
Proof. intros z H. unfold wz. apply unsigned_lit. exact H. Qed.

Lemma c1b2_wz_mod : forall a b, wz a = wz b -> a mod 2 ^ 64 = b mod 2 ^ 64.
Proof. intros a b E. unfold wz in E. rewrite <- (unsigned_lit_wrap a), <- (unsigned_lit_wrap b), E. reflexivity. Qed.

Lemma c1b2_wz_inj : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> wz a = wz b -> a = b.
Proof.
  intros a b Ha Hb E. apply c1b2_wz_mod in E. rewrite !Z.mod_small in E by lia. exact E.
Qed.

Lemma c1b2_wz_ne : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a <> b -> wz a <> wz b.
Proof. intros a b Ha Hb Hne E. apply Hne. exact (c1b2_wz_inj a b Ha Hb E). Qed.

(* a value that reads as a literal word is that literal, or lies outside [0, 2 ^ 64) *)
Lemma c1b2_mod_cases : forall p q, p mod 2 ^ 64 = q -> 0 <= q < 2 ^ 64 -> p = q \/ 2 ^ 64 <= p \/ p < 0.
Proof.
  intros p q H Hq.
  destruct (Z.lt_ge_cases p 0) as [Hn|Hn]; [right; right; exact Hn|].
  destruct (Z.lt_ge_cases p (2 ^ 64)) as [Hl|Hl]; [|right; left; exact Hl].
  left. rewrite <- H. symmetry. apply Z.mod_small. lia.
Qed.

(* ==========================================================================
   2. Lists and bytes
   ========================================================================== *)

Lemma c1b2_list_ext : forall (A : Type) (l1 l2 : list A), length l1 = length l2 ->
  (forall i, (i < length l1)%nat -> nth_error l1 i = nth_error l2 i) -> l1 = l2.
Proof.
  intros A l1. induction l1 as [|x l1 IH]; intros [|y l2] L H; cbn in L; try discriminate; [reflexivity|].
  pose proof (H 0%nat ltac:(cbn; lia)) as H0. cbn in H0. injection H0 as ->.
  f_equal. apply IH; [lia|]. intros i Hi. exact (H (S i) ltac:(cbn; lia)).
Qed.

Lemma c1b2_bytes_eq : forall m a bs bs', bytes_at rsegs m a bs -> bytes_at rsegs m a bs' ->
  length bs = length bs' -> bs = bs'.
Proof.
  intros m a bs bs' (A1 & A2 & A3) (B1 & B2 & B3) L.
  apply c1b2_list_ext; [exact L|]. intros i Hi.
  rewrite <- (A3 i Hi), <- (B3 i ltac:(lia)). reflexivity.
Qed.

Lemma c1b2_le8_inj : forall v w : word, le8 v = le8 w -> v = w.
Proof.
  intros v w E. rewrite <- (le_bytes_to_word_le8 v), <- (le_bytes_to_word_le8 w), E. reflexivity.
Qed.

Lemma c1b2_u64_same : forall m a p q, u64_at m a p -> u64_at m a q -> p mod 2 ^ 64 = q mod 2 ^ 64.
Proof.
  intros m a p q Hp Hq. unfold u64_at in Hp, Hq.
  assert (E : le8 (wz p) = le8 (wz q)).
  { eapply c1b2_bytes_eq; [exact Hp | exact Hq | rewrite !length_le8; reflexivity]. }
  apply c1b2_le8_inj in E. apply c1b2_wz_mod. exact E.
Qed.

(* a 4-byte slice read back as a word *)
Lemma c1b2_le4_of : forall bs, length bs = 4%nat -> le4 (wz (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L.
  assert (R : 0 <= bytes_le_to_Z bs < 2 ^ 32).
  { split; [apply bytes_le_to_Z_nonneg|].
    pose proof (bytes_le_to_Z_bound bs) as B. rewrite L in B. exact B. }
  unfold le4. rewrite c1b2_uns by lia. rewrite <- L. apply Z_to_le_bytes_to_Z.
Qed.

Lemma c1b2_slice_len : forall bs off n, 0 <= n -> 0 <= off ->
  (Z.to_nat off + Z.to_nat n <= length bs)%nat -> length (slice bs off n) = Z.to_nat n.
Proof.
  intros bs off n Hn Ho Hb. unfold slice. rewrite length_firstn, length_skipn. lia.
Qed.

(* ==========================================================================
   3. Reading memory
   ========================================================================== *)

Lemma c1b2_read8 : forall m a (v : word), bytes_at rsegs m a (le8 v) ->
  ov_read_bytes rsegs m (wa a) 8 = Some (le8 v).
Proof.
  intros m a v H.
  pose proof (bytes_at_read rsegs m a (le8 v) 0 8 H ltac:(lia) ltac:(rewrite length_le8; lia)) as R.
  rewrite Z.add_0_r in R. rewrite R. reflexivity.
Qed.

Lemma c1b2_read1 : forall m a b l, bytes_at rsegs m a (b :: l) ->
  ov_read_bytes rsegs m (wa a) 1 = Some [b].
Proof.
  intros m a b l H.
  pose proof (bytes_at_read rsegs m a (b :: l) 0 1 H ltac:(lia) ltac:(cbn; lia)) as R.
  rewrite Z.add_0_r in R. rewrite R. reflexivity.
Qed.

Lemma c1b2_read4_arr : forall m A bs off,
  u8arr rsegs m A bs -> 0 <= off -> (Z.to_nat off + 4 <= length bs)%nat ->
  ov_read_bytes rsegs m (wa (A + off)) 4 = Some (slice bs off 4).
Proof.
  intros m A bs off [HB _] Ho Hb.
  pose proof (bytes_at_read rsegs m A bs off 4 HB Ho Hb) as R. rewrite R. reflexivity.
Qed.

(* ==========================================================================
   4. Transport of a memory view across a call's footprint
   ========================================================================== *)

Definition c1b2_out (W : list ivl) (A n : Z) : Prop := forall x, A <= x < A + n -> outside W x.

Lemma c1b2_bytes_tr : forall W m m' A bs,
  bytes_at rsegs m A bs -> munch W m m' -> c1b2_out W A (Z.of_nat (length bs)) ->
  bytes_at rsegs m' A bs.
Proof.
  intros W m m' A bs (Ha & Hl & H) MU HO. split; [lia|]. split; [lia|].
  intros i Hi. unfold mrd. rewrite MU.
  - apply H. exact Hi.
  - rewrite wa_unsigned by lia. apply HO. lia.
Qed.

Lemma c1b2_u8arr_tr : forall W m m' A bs,
  u8arr rsegs m A bs -> munch W m m' -> wmono rsegs m m' -> c1b2_out W A (Z.of_nat (length bs)) ->
  u8arr rsegs m' A bs.
Proof.
  intros W m m' A bs [HB HW] MU WM HO.
  split; [eapply c1b2_bytes_tr; eassumption | eapply wr_at_transport; eassumption].
Qed.

Lemma c1b2_rwc_tr : forall W m m' A cs,
  rw_cells rsegs m A cs -> munch W m m' -> wmono rsegs m m' ->
  c1b2_out W A (Z.of_nat (cells_size cs)) -> rw_cells rsegs m' A cs.
Proof.
  intros W m m' A cs [[HWF HB] HW] MU WM HO. split; [split; [exact HWF|]|].
  - eapply c1b2_bytes_tr; [exact HB | exact MU |].
    rewrite cells_bytes_length by exact HWF. exact HO.
  - eapply wr_at_transport; eassumption.
Qed.

Lemma c1b2_cstr_tr : forall W m m' p nm,
  cstr_at m p nm -> munch W m m' -> c1b2_out W p (Z.of_nat (length nm) + 1) -> cstr_at m' p nm.
Proof.
  intros W m m' p nm [HB HN] MU HO. split; [|exact HN].
  eapply c1b2_bytes_tr; [exact HB | exact MU |].
  intros x Hx. apply HO. rewrite length_app in Hx. cbn [length] in Hx. lia.
Qed.

Lemma c1b2_u64_tr : forall W m m' a v,
  u64_at m a v -> munch W m m' -> c1b2_out W a 8 -> u64_at m' a v.
Proof.
  intros W m m' a v H MU HO. unfold u64_at in *.
  eapply c1b2_bytes_tr; [exact H | exact MU |]. rewrite length_le8. exact HO.
Qed.

Lemma c1b2_u32_tr : forall W m m' a v,
  u32_at m a v -> munch W m m' -> c1b2_out W a 4 -> u32_at m' a v.
Proof.
  intros W m m' a v H MU HO. unfold u32_at in *.
  eapply c1b2_bytes_tr; [exact H | exact MU |]. rewrite length_le4. exact HO.
Qed.

(* a call whose whole footprint is empty leaves memory as it was *)
Lemma c1b2_munch_triv : forall (a b : Z) m m', b <= a -> munch [(a, b)] m m' -> m' = m.
Proof.
  intros a b m m' Hab MU. apply functional_extensionality. intros x.
  apply MU. cbn [outside]. split; [lia | exact I].
Qed.

Lemma c1b2_munch_nil : forall m m', munch [] m m' -> m' = m.
Proof. intros m m' MU. apply functional_extensionality. intros x. apply MU. exact I. Qed.

(* ==========================================================================
   5. A block outside the image's reserved segments
      (the shape of snprintf.v's cov / img_free_bound, re-derived)
   ========================================================================== *)

Definition c1b2_ivs (l : list (word * word)) : list (Z * Z) :=
  map (fun s => (bv_unsigned (fst s), bv_unsigned (fst s) + bv_unsigned (snd s))) l.

Fixpoint c1b2_cov (L : list (Z * Z)) (cur : Z) : Z :=
  match L with [] => cur | (a, b) :: L' => c1b2_cov L' (if a <=? cur then Z.max cur b else cur) end.

Lemma c1b2_cov_in : forall L cur x, cur <= x < c1b2_cov L cur -> exists a b, In (a, b) L /\ a <= x < b.
Proof.
  induction L as [|[a b] L IH]; intros cur x Hx; cbn [c1b2_cov] in Hx; [lia|].
  revert Hx. destruct (a <=? cur) eqn:E; intros Hx.
  - apply Z.leb_le in E. destruct (Z.lt_ge_cases x (Z.max cur b)) as [H|H].
    + exists a, b. split; [left; reflexivity | lia].
    + destruct (IH (Z.max cur b) x ltac:(lia)) as (a' & b' & Hin & Hab).
      exists a', b'. split; [right; exact Hin | exact Hab].
  - destruct (IH cur x Hx) as (a' & b' & Hin & Hab).
    exists a', b'. split; [right; exact Hin | exact Hab].
Qed.

Definition C1B2_PAGES : Z := Eval vm_compute in c1b2_cov (c1b2_ivs (segments_reserved rsegs)) 0x10000.

Lemma c1b2_pages_eq : c1b2_cov (c1b2_ivs (segments_reserved rsegs)) 0x10000 = C1B2_PAGES.
Proof. vm_compute. reflexivity. Qed.

Lemma c1b2_pages_ge : 0x960e0 <= C1B2_PAGES.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma c1b2_img_free_bound : forall D n, 0 <= D -> 0 < n -> pf_img_free D n ->
  D + n <= 0x10000 \/ C1B2_PAGES <= D.
Proof.
  intros D n HD Hn F.
  assert (C : forall x, 0x10000 <= x < C1B2_PAGES -> exists s, In s (segments_reserved rsegs)
                /\ bv_unsigned (fst s) <= x < bv_unsigned (fst s) + bv_unsigned (snd s)).
  { intros x Hx. rewrite <- c1b2_pages_eq in Hx. destruct (c1b2_cov_in _ _ _ Hx) as (a & b & Hin & Hab).
    unfold c1b2_ivs in Hin. apply in_map_iff in Hin. destruct Hin as (s & Es & Hs).
    injection Es as Ea Eb. exists s. split; [exact Hs | lia]. }
  pose proof c1b2_pages_ge as PL.
  destruct (Z.lt_ge_cases D 0x10000) as [H1|H1].
  - destruct (Z.le_gt_cases (D + n) 0x10000) as [H2|H2]; [left; exact H2|].
    destruct (C 0x10000 ltac:(lia)) as (s & Hs & Hx). exfalso.
    apply (F (0x10000 - D) ltac:(lia) s Hs).
    replace (D + (0x10000 - D)) with 0x10000 by lia. exact Hx.
  - destruct (Z.lt_ge_cases D C1B2_PAGES) as [H2|H2]; [|right; exact H2].
    destruct (C D ltac:(lia)) as (s & Hs & Hx). exfalso.
    apply (F 0 ltac:(lia) s Hs). rewrite Z.add_0_r. exact Hx.
Qed.

(* every address of the image's globals misses a block the slot allocated *)
Lemma c1b2_blk_lo : forall S a n x, 0 < n -> blk_out S a n -> 0x10000 <= x < 0x960e0 ->
  ~ (a <= x < a + n).
Proof.
  intros S a n x Hn (H1 & H2 & HF) Hx.
  pose proof c1b2_pages_ge as PL.
  destruct (c1b2_img_free_bound a n ltac:(lia) Hn HF) as [H|H]; lia.
Qed.

Lemma c1b2_blk_hi : forall S a n, blk_out S a n -> a + n <= S - SLOT_STACK_Z.
Proof. intros S a n (_ & H & _). exact H. Qed.

Lemma c1b2_blk_lo0 : forall S a n, blk_out S a n -> 4096 <= a.
Proof. intros S a n (H & _ & _). exact H. Qed.
