(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMmergeL.v (commit 67deba317dfb, blob 7a69470f3120) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 17 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AFeq AFew AFeu AFgj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DMwalkIFA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMseg_mbe DMseg_mbh DMseg_mbc DMseg_mbt.

From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AB13.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Definition mergeb (c n : batch) : batch := mkBatch (b_self c) (b_items c ++ b_items n).
Definition emptyb (n : batch) : batch := mkBatch (b_self n) [].
Definition can_merge (c n : batch) : bool :=
  (length (b_items c) + length (b_items n) <=? Z.to_nat kBatchSlots)%nat.

Lemma mbcf_cons2 : forall f c n t, merge_batches_cf (S f) (c :: n :: t) =
  if can_merge c n then let '(r, e) := merge_batches_cf f (mergeb c n :: t) in (r, emptyb n :: e)
  else let '(r, e) := merge_batches_cf f (n :: t) in (c :: r, e).
Proof. reflexivity. Qed.

Lemma mbcf_fst_cons2 : forall f c n t, fst (merge_batches_cf (S f) (c :: n :: t)) =
  if can_merge c n then fst (merge_batches_cf f (mergeb c n :: t)) else c :: fst (merge_batches_cf f (n :: t)).
Proof.
intros f c n t. rewrite mbcf_cons2. destruct (can_merge c n).
- destruct (merge_batches_cf f (mergeb c n :: t)); reflexivity.
- destruct (merge_batches_cf f (n :: t)); reflexivity.
Qed.
Lemma mbcf_snd_cons2 : forall f c n t, snd (merge_batches_cf (S f) (c :: n :: t)) =
  if can_merge c n then emptyb n :: snd (merge_batches_cf f (mergeb c n :: t)) else snd (merge_batches_cf f (n :: t)).
Proof.
intros f c n t. rewrite mbcf_cons2. destruct (can_merge c n).
- destruct (merge_batches_cf f (mergeb c n :: t)); reflexivity.
- destruct (merge_batches_cf f (n :: t)); reflexivity.
Qed.

Lemma mbcf_short : forall f l, (length l < 2)%nat -> merge_batches_cf f l = (l, []).
Proof. intros [|f] [|b [|b' l]] H; cbn [length] in H; try lia; reflexivity. Qed.

Definition sumn (l : list chunk) : Z := fold_right (fun k acc => ck_n k + acc) 0 l.
Lemma sumn_app : forall l1 l2, sumn (l1 ++ l2) = sumn l1 + sumn l2.
Proof. induction l1 as [|k l IH]; intros l2; unfold sumn in *; cbn [app fold_right]; [lia|]. rewrite IH. lia. Qed.
Lemma b_bytes_sumn : forall b, b_bytes b = kBatchBytes + sumn (b_items b).
Proof. reflexivity. Qed.
Lemma b_bytes_merge : forall c n, b_bytes (mergeb c n) = b_bytes c + b_bytes n - kBatchBytes.
Proof. intros c n. rewrite !b_bytes_sumn. unfold mergeb. cbn [b_items]. rewrite sumn_app. lia. Qed.
Lemma b_bytes_empty : forall n, b_bytes (emptyb n) = kBatchBytes.
Proof. intros n. unfold b_bytes, emptyb. cbn [b_items fold_right]. lia. Qed.
Lemma sum_bytes_cons' : forall b l, sum_bytes (b :: l) = b_bytes b + sum_bytes l.
Proof. reflexivity. Qed.
Lemma sum_bytes_app' : forall l1 l2, sum_bytes (l1 ++ l2) = sum_bytes l1 + sum_bytes l2.
Proof. induction l1 as [|b l IH]; intros l2; cbn [app]; [reflexivity|]. rewrite !sum_bytes_cons', IH. lia. Qed.

Lemma mbcf_bytes : forall f l,
  sum_bytes (fst (merge_batches_cf f l)) + kBatchBytes * zl (snd (merge_batches_cf f l)) = sum_bytes l.
Proof.
induction f as [|f IH]; intros l; [cbn [merge_batches_cf fst snd]; unfold zl; cbn [length Z.of_nat]; lia|].
destruct l as [|c [|n t]]; [cbn [merge_batches_cf fst snd]; unfold zl; cbn [length Z.of_nat]; lia
  | cbn [merge_batches_cf fst snd]; unfold zl; cbn [length Z.of_nat]; lia|].
rewrite mbcf_fst_cons2, mbcf_snd_cons2. destruct (can_merge c n) eqn:E.
- pose proof (IH (mergeb c n :: t)) as H. unfold zl in *. cbn [length] in *. rewrite sum_bytes_cons' in H.
  rewrite !sum_bytes_cons', b_bytes_merge in *. lia.
- pose proof (IH (n :: t)) as H. unfold zl in *. rewrite !sum_bytes_cons' in *. lia.
Qed.
Lemma mbcf_items : forall f l, flat_map b_items (fst (merge_batches_cf f l)) = flat_map b_items l.
Proof.
induction f as [|f IH]; intros l; [reflexivity|].
destruct l as [|c [|n t]]; [reflexivity | reflexivity|].
rewrite mbcf_fst_cons2. destruct (can_merge c n).
- rewrite IH. unfold mergeb. cbn [flat_map b_items]. rewrite app_assoc. reflexivity.
- cbn [flat_map]. rewrite IH. reflexivity.
Qed.
Lemma mbcf_empty : forall f l, Forall (fun b => b_items b = []) (snd (merge_batches_cf f l)).
Proof.
induction f as [|f IH]; intros l; [constructor|].
destruct l as [|c [|n t]]; [constructor | constructor|].
rewrite mbcf_snd_cons2. destruct (can_merge c n); [constructor; [reflexivity | apply IH] | apply IH].
Qed.
Lemma mbcf_selfs : forall f l s,
  In s (map b_self l) <-> In s (map b_self (fst (merge_batches_cf f l)) ++ map b_self (snd (merge_batches_cf f l))).
Proof.
induction f as [|f IH]; intros l s; [cbn; rewrite app_nil_r; tauto|].
destruct l as [|c [|n t]]; [cbn; tauto | cbn; tauto|].
rewrite mbcf_fst_cons2, mbcf_snd_cons2. destruct (can_merge c n).
- rewrite in_app_iff in *. pose proof (IH (mergeb c n :: t) s) as H. rewrite in_app_iff in H.
  cbn [map In] in *. unfold mergeb, emptyb in *. cbn [b_self] in *. tauto.
- pose proof (IH (n :: t) s) as H. rewrite in_app_iff in *. cbn [map In] in *. tauto.
Qed.
Lemma mbcf_length : forall f l,
  length l = (length (fst (merge_batches_cf f l)) + length (snd (merge_batches_cf f l)))%nat.
Proof.
induction f as [|f IH]; intros l; [cbn; lia|].
destruct l as [|c [|n t]]; [reflexivity | reflexivity|].
rewrite mbcf_fst_cons2, mbcf_snd_cons2. destruct (can_merge c n).
- pose proof (IH (mergeb c n :: t)) as H. cbn [length] in *. lia.
- pose proof (IH (n :: t)) as H. cbn [length] in *. lia.
Qed.
Lemma mbcf_slots : forall f l,
  Forall (fun b => (length (b_items b) <= Z.to_nat kBatchSlots)%nat) l ->
  Forall (fun b => (length (b_items b) <= Z.to_nat kBatchSlots)%nat) (fst (merge_batches_cf f l)).
Proof.
induction f as [|f IH]; intros l Hl; [exact Hl|].
destruct l as [|c [|n t]]; [exact Hl | exact Hl|].
rewrite mbcf_fst_cons2. inversion Hl as [|? ? Hc Hnt]; subst. inversion Hnt as [|? ? Hn Ht]; subst.
destruct (can_merge c n) eqn:E.
- apply IH. constructor; [|exact Ht]. unfold can_merge in E. apply Nat.leb_le in E.
  unfold mergeb. cbn [b_items]. rewrite length_app. exact E.
- constructor; [exact Hc|]. apply IH. exact Hnt.
Qed.
Lemma mbcf_head : forall f b t, exists t',
  fst (merge_batches_cf f (b :: t)) = b :: t' \/
  exists its, fst (merge_batches_cf f (b :: t)) = mkBatch (b_self b) its :: t'.
Proof.
induction f as [|f IH]; intros b t; [exists t; left; reflexivity|].
destruct t as [|n t]; [exists []; left; reflexivity|].
rewrite mbcf_fst_cons2. destruct (can_merge b n).
- destruct (IH (mergeb b n) t) as (t' & [E | (its & E)]); exists t'; right.
  + exists (b_items b ++ b_items n). rewrite E. reflexivity.
  + exists its. rewrite E. reflexivity.
- exists (fst (merge_batches_cf f (n :: t))). left. reflexivity.
Qed.

Theorem mb_model_facts_ok : mb_model_facts.
Proof.
intros l. unfold MB. split; [apply mbcf_bytes|]. split; [apply mbcf_items|]. split; [apply mbcf_empty|].
split; [intros s; apply mbcf_selfs|]. split; [apply mbcf_length|]. split; [apply mbcf_slots|].
split.
- intros Hne. destruct l as [|b t]; [contradiction|].
  destruct (mbcf_head (length (b :: t)) b t) as (t' & [E | (its & E)]); rewrite E; discriminate.
- intros b t ->. exact (mbcf_head (length (b :: t)) b t).
Qed.

Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in
  pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kSpaceSize,
  TFIB_IMG_END, kBatchBytes, kBatchSlots, TFIB_TP, A_QUAR, A_ALLOCATOR, o_quar in *.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.

Section t.
Variable H0 : word -> bool.
Local Notation mr m := (mrestrict H0 m).
Lemma vm_keep : forall (P : Z -> Prop) (m m' : word -> option byte) a (n : nat) v,
  (forall x : word, ~ P (bv_unsigned x) -> m' x = m x) ->
  (forall i, 0 <= i < Z.of_nat n -> ~ P (a + i) /\ 0 <= a + i < 2 ^ 64) ->
  val_mem tfibsegs (mr m) a n v -> val_mem tfibsegs (mr m') a n v.
Proof.
intros P m m' a n v HM Hn Hv. eapply AF0x.val_mem_frame; [|exact Hv]. intros k Hk.
destruct (Hn (Z.of_nat k) ltac:(lia)) as [N1 N2].
apply HM. rewrite unsigned_lit_small by exact N2. exact N1.
Qed.
Lemma apresent_keep : forall (P : Z -> Prop) (m m' : word -> option byte) a,
  (forall x : word, ~ P (bv_unsigned x) -> m' x = m x) -> ~ P a -> 0 <= a < 2 ^ 64 ->
  apresent H0 m a -> apresent H0 m' a.
Proof.
intros P m m' a HM HP Ha (Hh & b & Hb). split; [exact Hh|]. exists b.
rewrite HM; [exact Hb|]. rewrite unsigned_lit_small by exact Ha. exact HP.
Qed.
Variable ly : alayout.
Variable iw : chunk -> Z.
Lemma bcell_keep : forall (P : Z -> Prop) m m' b z,
  (forall x : word, ~ P (bv_unsigned x) -> m' x = m x) ->
  (forall a, bcells_of ly b a -> ~ P a) -> 0 <= addrb ly b -> addrb ly b + kBatchBytes <= 2 ^ 64 ->
  (length (b_items b) <= 1021)%nat ->
  bcell ly iw (mr m) b z -> bcell ly iw (mr m') b z.
Proof.
intros P m m' b z HM HP A1 A2 HC (V0 & V8 & V16 & VS). unfold bcells_of, zl, kBatchBytes in *.
unfold bcell. splits.
- apply (vm_keep P m m' _ _ _ HM); [|exact V0]. intros i Hi. split; [apply HP; lia | lia].
- apply (vm_keep P m m' _ _ _ HM); [|exact V8]. intros i Hi. split; [apply HP; lia | lia].
- apply (vm_keep P m m' _ _ _ HM); [|exact V16]. intros i Hi. split; [apply HP; lia | lia].
- intros j k Hj. pose proof (proj1 (nth_error_Some (b_items b) j) ltac:(rewrite Hj; discriminate)) as LT.
  apply (vm_keep P m m' _ _ _ HM); [|exact (VS j k Hj)]. intros i Hi. split; [apply HP; lia | lia].
Qed.
Lemma lcn_keep : forall (P : Z -> Prop) m m' l z,
  (forall x : word, ~ P (bv_unsigned x) -> m' x = m x) ->
  (forall b, In b l -> (forall a, bcells_of ly b a -> ~ P a) /\ 0 <= addrb ly b /\
     addrb ly b + kBatchBytes <= 2 ^ 64 /\ (length (b_items b) <= 1021)%nat) ->
  lcn ly iw (mr m) l z -> lcn ly iw (mr m') l z.
Proof.
intros P m m' l z HM. induction l as [|b l IH]; intros HB Hl; [exact I|]. destruct Hl as [Hb Hl].
destruct (HB b (or_introl eq_refl)) as (B1 & B2 & B3 & B4). split.
- exact (bcell_keep P m m' b _ HM B1 B2 B3 B4 Hb).
- apply IH; [intros b' Hb'; exact (HB b' (or_intror Hb')) | exact Hl].
Qed.
End t.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variables (W : world tfibsegs) (ly : alayout) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variable mat0 : list word.
Variable iw : chunk -> Z.
Variable L0 : list batch.
Hypothesis HP : mb_pre W ly regs0 mem0 iw L0.
Local Notation spr := (bv_unsigned (getr regs0 2)).
Local Notation m0 := (mrestrict (w_H W) mem0).
Variables (b1 b2 : batch) (t : list batch).
Hypothesis HL : L0 = b1 :: b2 :: t.

Lemma ent_b : forall b, In b L0 ->
  kHighMemBeg <= addrb ly b /\ addrb ly b + kBatchBytes <= ASAN_CEIL /\ addrb ly b mod 8192 = 0 /\
  (1 <= length (b_items b) <= Z.to_nat kBatchSlots)%nat /\
  (addrb ly b + kBatchBytes <= spr - 16 \/ spr + 32 <= addrb ly b).
Proof. intros b Hb. exact (mb_bfacts _ _ _ _ _ _ HP b Hb). Qed.

Lemma ent_AF : forall (E : env) k0 Xv lo hi al, ew E k0 = w64 Xv -> 0 <= Xv < 2 ^ 64 -> lo <= Xv <= hi ->
  Xv mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E k0 (mkAF lo hi al).
Proof.
intros E k0 Xv lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64.
rewrite unsigned_lit_small by exact HX. repeat split; lia.
Qed.

Lemma ent_E32 : ew (Ereg regs0 (DMseg_mbe.XW (addrb ly b1) (addrb ly b2))) 32 = Z_to_bv 64 (addrb ly b1).
Proof. reflexivity. Qed.
Lemma ent_E33 : ew (Ereg regs0 (DMseg_mbe.XW (addrb ly b1) (addrb ly b2))) 33 = Z_to_bv 64 (addrb ly b2).
Proof. reflexivity. Qed.
Lemma ent_FH : DMseg_mbe.free_hyps W regs0 mem0 (addrb ly b1) (addrb ly b2).
Proof.
pose proof (mb_sp _ _ _ _ _ _ HP) as [S1 S2].
pose proof (mb_sp_al _ _ _ _ _ _ HP) as SAL.
assert (In1 : In b1 L0) by (rewrite HL; left; reflexivity).
assert (In2 : In b2 L0) by (rewrite HL; right; left; reflexivity).
destruct (ent_b b1 In1) as (F1 & F2 & F3 & _ & F5).
destruct (ent_b b2 In2) as (N1 & N2 & N3 & _ & _).
pose proof (mb_hdr _ _ _ _ _ _ HP) as (VH0 & VH8 & VH16 & VH24).
pose proof (mb_cells _ _ _ _ _ _ HP) as VC. rewrite HL in VC, VH8. cbn [lcn fa] in VC, VH8.
destruct VC as ((VN & _) & _).
assert (Usp : 0 <= spr < 2 ^ 64) by apply u64_range.
constructor.
- split; [exact S1 | numconst; lia].
- exact SAL.
- exact (mb_ra _ _ _ _ _ _ HP).
- exact (conj F1 (conj F2 F3)).
- exact (conj N1 (conj N2 N3)).
- rewrite restrict_mkst_fx. unfold DMseg_mbe.SS0, DMseg_mbe.SR0, DMseg_mbe.E0, w64.
  apply (entry_st_ok_full tfibsegs).
  + apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros XX; discriminate |] | intros XX; discriminate |].
    * cbn [sv_denot]. exact (mb_ra _ _ _ _ _ _ HP).
    * cbn [sv_denot]. exact (mb_a0 _ _ _ _ _ _ HP).
  + vm_compute. reflexivity.
  + unfold DMseg_mbe.REG0, DMseg_mbe.R_STK, DMseg_mbe.R_LH, DMseg_mbe.R_F.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    * apply (region_ok_stack tfibsegs _ _ 2%nat spr (-16)).
      -- rewrite (ew_Ereg_nat regs0 _ 2 2%bv eq_refl). reflexivity.
      -- numconst; lia.
      -- lia.
      -- intros a Ha. apply apresent_writable; [numconst; lia|].
         apply (mb_pres _ _ _ _ _ _ HP). lia.
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      split; [numconst; lia|]. split; [numconst; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs _ _ 0 (A_QUAR + 168) 8 (SOff 32%nat 0) (addrb ly b1)).
      -- cbn [sv_denot]. rewrite ent_E32, unsigned_lit_small by (numconst; lia). f_equal. lia.
      -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). numconst; lia.
      -- cbn. lia.
      -- rewrite Z.add_0_l. exact VH8.
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite ent_E32.
      rewrite unsigned_lit_small by (numconst; lia).
      split; [numconst; lia|]. split; [numconst; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs _ _ (addrb ly b1) 0 8 (SOff 33%nat 0) (addrb ly b2)).
      -- cbn [sv_denot]. rewrite ent_E33, unsigned_lit_small by (numconst; lia). f_equal. lia.
      -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). numconst; lia.
      -- cbn. lia.
      -- rewrite Z.add_0_r. exact VN.
  + apply pairwise_disjoint_of_extents.
    unfold DMseg_mbe.REG0, DMseg_mbe.R_STK, DMseg_mbe.R_LH, DMseg_mbe.R_F, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite (ew_Ereg_nat regs0 _ 2 2%bv eq_refl).
    rewrite ent_E32.
    rewrite unsigned_lit_small by (numconst; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    numconst. splits; lia.
  + split; [|split; exact I].
    unfold DMseg_mbe.FFE. cbn [f_atoms atoms_ok]. numconst.
    split. { apply (ent_AF _ 2%nat spr);
             [rewrite (ew_Ereg_nat regs0 _ 2 2%bv eq_refl); unfold w64; symmetry; apply Z_to_bv_bv_unsigned
             | lia | lia | | lia].
             change (2 ^ 4) with 16. exact SAL. }
    split. { apply (ent_AF _ 32%nat (addrb ly b1)); [reflexivity | lia | lia | change (2 ^ 13) with 8192; exact F3 | lia]. }
    split; [|exact I].
    apply (ent_AF _ 33%nat (addrb ly b2)); [reflexivity | lia | lia | change (2 ^ 13) with 8192; exact N3 | lia].
Qed.

Lemma ent_cells_apart : forall b a, In b L0 -> bcells_of ly b a ->
  ~ (spr - 16 <= a < spr + 32) /\ kHighMemBeg <= a /\ a + 1 <= ASAN_CEIL /\ bobj_of ly b a.
Proof.
intros b a Hb Ha. destruct (ent_b b Hb) as (B1 & B2 & B3 & (B4 & B5) & B6).
unfold bcells_of, bobj_of, zl in *. unfold kBatchSlots, kBatchBytes in *.
assert (Z.of_nat (length (b_items b)) <= 1021) by lia. lia.
Qed.
Lemma ent_hdr_low : A_QUAR + 192 <= kHighMemBeg.
Proof. numconst; lia. Qed.

Lemma ent_conv : forall W' c',
  DMseg_mbe.at_MBH W regs0 mem0 md0 (addrb ly b1) (addrb ly b2) W' c' ->
  mb_inv W ly regs0 mem0 md0 iw L0 [] b1 b2 t [] W' c'.
Proof.
intros W' c' HM. unfold DMseg_mbe.at_MBH in HM.
destruct HM as (EW & regs' & mem' & mat & Ec & R2 & R1 & RS & R10 & R12 & R14 & R5 & R15 & R16 & R17 & MQ & PR & VRA).
pose proof (mb_sp _ _ _ _ _ _ HP) as [S1 S2].
assert (Usp : 0 <= spr < 2 ^ 64) by apply u64_range.
pose proof (mb_hdr _ _ _ _ _ _ HP) as (VH0 & VH8 & VH16 & VH24).
pose proof (mb_tmp _ _ _ _ _ _ HP) as (VT0 & VT8 & VT16 & VT24).
pose proof (mb_cells _ _ _ _ _ _ HP) as VC.
pose proof ent_hdr_low as HLOW.

assert (KM : forall x : word, ~ (spr - 16 <= bv_unsigned x < spr) -> mem' x = mem0 x).
{ intros x Hx. apply MQ. unfold DMseg_mbe.WIN. exact Hx. }
assert (KV : forall a n v, (forall i, 0 <= i < Z.of_nat n -> ~ (spr - 16 <= a + i < spr) /\ 0 <= a + i < 2 ^ 64) ->
  val_mem tfibsegs m0 a n v -> val_mem tfibsegs (mrestrict (w_H W) mem') a n v).
{ intros a n v Hn Hv. exact (vm_keep (w_H W) (fun a => spr - 16 <= a < spr) mem0 mem' a n v KM Hn Hv). }
unfold mb_inv. split; [exact EW|].
split. { cbn [app]. rewrite HL. destruct (MB (b1 :: b2 :: t)); reflexivity. }
split. { cbn [app]. intros b Hb. rewrite HL. apply in_map. exact Hb. }
split. { intros b []. }
split. { cbn [app]. rewrite app_nil_r. rewrite <- HL. exact (mb_nodup _ _ _ _ _ _ HP). }
split. { cbn [app]. rewrite <- HL. apply Forall_forall. intros b Hb. destruct (ent_b b Hb) as (_ & _ & _ & (_ & Hl) & _). exact Hl. }
split. { cbn [app]. rewrite HL. reflexivity. }
split. { cbn [app]. unfold zl. cbn [length Z.of_nat]. rewrite HL. lia. }
exists regs', mem', mat. split; [exact Ec|].
split; [exact R2|]. split; [exact R1|].
split. { intros r Hr. apply RS. unfold DMseg_mbe.SREGS. unfold SREGSX in Hr. cbn [In] in Hr |- *. tauto. }
split; [exact R10|].
split. { rewrite (RS 11%bv ltac:(unfold DMseg_mbe.SREGS; cbn [In]; tauto)). exact (mb_a1 _ _ _ _ _ _ HP). }
split. { rewrite R12. unfold zl. cbn [length Z.of_nat]. f_equal. }
split; [exact R14|]. split; [exact R5|].
split; [rewrite R15; reflexivity|]. split; [rewrite R16; reflexivity|]. split; [rewrite R17; reflexivity|].
split.
{ intros x Hx. apply KM. intros Hw. apply Hx. left. lia. }
assert (HIN : forall b, In b (L0 ++ ([] ++ b1 :: b2 :: t) ++ []) -> In b L0).
{ intros b Hb. rewrite app_nil_l, app_nil_r in Hb. apply in_app_or in Hb as [H | H]; [exact H | rewrite HL; exact H]. }
split.
{ intros a Ha Hh. destruct (Z_lt_le_dec a spr) as [Hlt | Hge].
  - destruct Ha as [Hw | [Hq | (b & Hb & Hc)]].
    + apply PR; [unfold DMseg_mbe.WIN; lia | exact Hh].
    + lia.
    + pose proof (HIN b Hb) as HbL.
      destruct (ent_cells_apart b a HbL Hc) as (Ap & _ & _ & Ho).
      apply (apresent_keep (w_H W) (fun a => spr - 16 <= a < spr) mem0 mem' a KM); [lia | numconst; lia |].
      exact (mb_bpres _ _ _ _ _ _ HP b a HbL Ho).
  - assert (Ra : 0 <= a < 2 ^ 64).
    { destruct Ha as [Hw | [Hq | (b & Hb & Hc)]].
      - numconst; lia.
      - numconst; lia.
      - destruct (ent_cells_apart b a (HIN b Hb) Hc) as (_ & _ & A3 & _). numconst; lia. }
    apply (apresent_keep (w_H W) (fun a => spr - 16 <= a < spr) mem0 mem' a KM); [lia | exact Ra |].
    + destruct Ha as [Hw | [Hq | (b & Hb & Hc)]].
      * apply (mb_pres _ _ _ _ _ _ HP). exact Hw.
      * lia.
      * pose proof (HIN b Hb) as HbL.
        destruct (ent_cells_apart b a HbL Hc) as (_ & _ & _ & Ho). exact (mb_bpres _ _ _ _ _ _ HP b a HbL Ho). }
cbv zeta.
assert (NH : forall a n v, A_QUAR + 160 <= a -> a + Z.of_nat n <= A_QUAR + 192 ->
  val_mem tfibsegs m0 a n v -> val_mem tfibsegs (mrestrict (w_H W) mem') a n v).
{ intros a n v H1 H2 Hv. apply KV; [|exact Hv]. intros i Hi. numconst. split; lia. }
assert (NT : forall a n v, spr <= a -> a + Z.of_nat n <= spr + 32 ->
  val_mem tfibsegs m0 a n v -> val_mem tfibsegs (mrestrict (w_H W) mem') a n v).
{ intros a n v H1 H2 Hv. apply KV; [|exact Hv]. intros i Hi. numconst. split; lia. }
cbn [app].
split. { apply NH; [lia | cbn; lia |]. rewrite <- HL. exact VH0. }
split. { apply NH; [lia | cbn; lia |]. exact VH8. }
split. { apply NH; [lia | cbn; lia |]. rewrite <- HL. exact VH16. }
split. { apply NH; [lia | cbn; lia |]. exact VH24. }
split. { unfold zl. cbn [length Z.of_nat]. apply NT; [lia | cbn; lia | exact VT0]. }
split. { cbn [fa]. apply NT; [lia | cbn; lia | exact VT8]. }
split. { unfold la. cbn [rev]. apply NT; [lia | cbn; lia | exact VT16]. }
split. { unfold zl. cbn [length Z.of_nat]. rewrite Z.mul_0_r. apply NT; [lia | cbn; lia | exact VT24]. }
split; [exact VRA|].
split; [|exact I].
rewrite <- HL.
apply (lcn_keep (w_H W) ly iw (fun a => spr - 16 <= a < spr) mem0 mem' L0 0 KM); [|exact VC].
intros b Hb. destruct (ent_b b Hb) as (B1 & B2 & B3 & (B4 & B5) & B6).
split; [intros a Ha; destruct (ent_cells_apart b a Hb Ha) as (Ap & _); lia|].
unfold kBatchSlots in B5. numconst. splits; lia.
Qed.

Lemma ent_main : SRr tfibsegs W
  (mkCfg (mkst regs0 (w64 0x34554) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0))
  (mb_inv W ly regs0 mem0 md0 iw L0 [] b1 b2 t []).
Proof.
eapply SRr_mono; [exact (DMseg_mbe.segE W regs0 mem0 md0 (addrb ly b1) (addrb ly b2) mat0 ent_FH)|].
intros W' c' _ HM. exact (ent_conv W' c' HM).
Qed.
End e.

Theorem mb_inv_entry_ok {fx : YK11.FPState} {rc : YM05.RunCeil} : forall W ly regs0 mem0 md0 mat0 iw L0,
  mb_inv_entry_t W ly regs0 mem0 md0 mat0 iw L0.
Proof.
intros W ly regs0 mem0 md0 mat0 iw L0 HP b1 b2 t HL. unfold mb_inv_entry_t.
exact (ent_main W ly regs0 mem0 md0 mat0 iw L0 HP b1 b2 t HL).
Qed.

Lemma fa_app : forall ly l1 l2 z, fa ly (l1 ++ l2) z = fa ly l1 (fa ly l2 z).
Proof. intros ly [|b l1] l2 z; reflexivity. Qed.
Lemma lcn_app : forall ly iw m l1 l2 z, lcn ly iw m (l1 ++ l2) z <-> lcn ly iw m l1 (fa ly l2 z) /\ lcn ly iw m l2 z.
Proof.
intros ly iw m l1. induction l1 as [|b l1 IH]; intros l2 z; cbn [app lcn].
- tauto.
- rewrite fa_app, IH. tauto.
Qed.
Lemma la_app_cons : forall ly l b t, la ly (l ++ b :: t) = la ly (b :: t).
Proof.
intros ly l b t. unfold la. rewrite rev_app_distr. cbn [rev]. destruct (rev t) as [|x r]; cbn [app]; [|reflexivity].
destruct (rev l); reflexivity.
Qed.
Lemma la_cons2 : forall ly a b l, la ly (a :: b :: l) = la ly (b :: l).
Proof. intros ly a b l. exact (la_app_cons ly [a] b l). Qed.
Lemma la_snoc : forall ly l b, la ly (l ++ [b]) = addrb ly b.
Proof. intros ly l b. unfold la. rewrite rev_app_distr. reflexivity. Qed.
Lemma sv_off0e : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma zl_app : forall {A : Type} (l1 l2 : list A), zl (l1 ++ l2) = zl l1 + zl l2.
Proof. intros A l1 l2. unfold zl. rewrite length_app. lia. Qed.
Lemma zl_cons : forall {A : Type} (x : A) l, zl (x :: l) = 1 + zl l.
Proof. intros A x l. unfold zl. cbn [length]. lia. Qed.
Lemma zl_nil : forall {A : Type}, zl (@nil A) = 0.
Proof. reflexivity. Qed.
Lemma zl_nonneg : forall {A : Type} (l : list A), 0 <= zl l.
Proof. intros A l. unfold zl. lia. Qed.

Lemma MB_cons2 : forall c n t, MB (c :: n :: t) =
  if can_merge c n then (fst (MB (mergeb c n :: t)), emptyb n :: snd (MB (mergeb c n :: t)))
  else (c :: fst (MB (n :: t)), snd (MB (n :: t))).
Proof.
intros c n t. unfold MB. cbn [length]. rewrite mbcf_cons2. unfold can_merge.
destruct (_ <=? _)%nat; destruct (merge_batches_cf _ _); reflexivity.
Qed.
Lemma MB_one : forall b, MB [b] = ([b], []).
Proof. reflexivity. Qed.
Lemma sumn_nonneg : forall l, (forall k, In k l -> 0 <= ck_n k) -> 0 <= sumn l.
Proof.
induction l as [|k l IH]; intros H; unfold sumn in *; cbn [fold_right]; [lia|].
pose proof (H k (or_introl eq_refl)). pose proof (IH (fun k' Hk => H k' (or_intror Hk))). lia.
Qed.
Lemma sum_bytes_nonneg : forall l, (forall b', In b' l -> 0 <= b_bytes b') -> 0 <= sum_bytes l.
Proof.
induction l as [|x l IH]; intros H; [cbn; lia|]. rewrite sum_bytes_cons'.
pose proof (H x (or_introl eq_refl)). pose proof (IH (fun b' Hb' => H b' (or_intror Hb'))). lia.
Qed.
Lemma sum_bytes_ge : forall l b, In b l -> (forall b', In b' l -> 0 <= b_bytes b') -> b_bytes b <= sum_bytes l.
Proof.
induction l as [|x l IH]; intros b Hb H; [destruct Hb|]. rewrite sum_bytes_cons'.
pose proof (sum_bytes_nonneg l (fun b' Hb' => H b' (or_intror Hb'))) as Hl.
pose proof (H x (or_introl eq_refl)).
destruct Hb as [<-|Hb]; [lia|].
pose proof (IH b Hb (fun b' Hb' => H b' (or_intror Hb'))). lia.
Qed.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variables (W : world tfibsegs) (ly : alayout) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variable iw : chunk -> Z.
Variable L0 : list batch.
Hypothesis HP : mb_pre W ly regs0 mem0 iw L0.
Local Notation spr := (bv_unsigned (getr regs0 2)).
Definition inL0 (b : batch) : Prop := In (b_self b) (map b_self L0).

Lemma g_self : forall b, inL0 b ->
  kHighMemBeg <= addrb ly b /\ addrb ly b + kBatchBytes <= ASAN_CEIL /\ addrb ly b mod 8192 = 0 /\
  (addrb ly b + kBatchBytes <= spr - 16 \/ spr + 32 <= addrb ly b).
Proof.
intros b Hb. unfold inL0 in Hb. apply in_map_iff in Hb as (b0 & E & Hb0).
destruct (mb_bfacts _ _ _ _ _ _ HP b0 Hb0) as (B1 & B2 & B3 & _ & B5).
unfold addrb in *. rewrite <- E. tauto.
Qed.
Lemma g_apart : forall b b', inL0 b -> inL0 b' -> b_self b <> b_self b' ->
  addrb ly b + kBatchBytes <= addrb ly b' \/ addrb ly b' + kBatchBytes <= addrb ly b.
Proof.
intros b b' Hb Hb' Hne. destruct (g_self b Hb) as (_ & _ & M1 & _). destruct (g_self b' Hb') as (_ & _ & M2 & _).
assert (addrb ly b <> addrb ly b') by (unfold addrb; intros X; apply Hne; lia).
unfold kBatchBytes. lia.
Qed.
Lemma g_cells : forall b a, (length (b_items b) <= 1021)%nat -> bcells_of ly b a -> addrb ly b <= a < addrb ly b + kBatchBytes.
Proof. intros b a Hl Ha. unfold bcells_of, zl, kBatchBytes in *. lia. Qed.
Lemma g_nn : forall k, In k (flat_map b_items L0) -> 0 <= ck_n k.
Proof. exact (mb_nn _ _ _ _ _ _ HP). Qed.
Lemma g_bytes_lo : forall b, (forall k, In k (b_items b) -> In k (flat_map b_items L0)) -> kBatchBytes <= b_bytes b.
Proof.
intros b H. rewrite b_bytes_sumn. pose proof (sumn_nonneg (b_items b) (fun k Hk => g_nn k (H k Hk))). lia.
Qed.
End g.

Lemma hE32 : forall regs a b c d e f g h, ew (Ereg regs (DMseg_mbh.XW a b c d e f g h)) 32 = Z_to_bv 64 a.
Proof. reflexivity. Qed.
Lemma hE33 : forall regs a b c d e f g h, ew (Ereg regs (DMseg_mbh.XW a b c d e f g h)) 33 = Z_to_bv 64 b.
Proof. reflexivity. Qed.
Lemma rw_wr : forall (m : word -> option byte) a, 0xa1000 <= a < 0x600000 -> writable_at tfibsegs m a.
Proof. intros m a Ha. unfold writable_at. apply AB13.tfib_rw_window. rewrite unsigned_lit_small by lia. exact Ha. Qed.
Ltac pin_close := rewrite ?sv_off0e; cbn [sv_denot];
  match goal with H : getr ?rg ?r = _ |- getr ?rg ?r = _ => rewrite H; reflexivity end.

Section l. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variables (W : world tfibsegs) (ly : alayout) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variable iw : chunk -> Z.
Variable L0 : list batch.
Hypothesis HP : mb_pre W ly regs0 mem0 iw L0.
Local Notation spr := (bv_unsigned (getr regs0 2)).
Local Notation mr m := (mrestrict (w_H W) m).
Local Notation inL := (inL0 L0).

Lemma spr_facts : kHighMemBeg + 16 <= spr /\ spr + 32 <= kHighMemEnd /\ spr mod 16 = 0 /\ 0 <= spr < 2 ^ 64.
Proof.
destruct (mb_sp _ _ _ _ _ _ HP) as [S1 S2]. pose proof (mb_sp_al _ _ _ _ _ _ HP) as S3.
pose proof (u64_range (getr regs0 2)) as S4. tauto.
Qed.

Lemma h_FH : forall (regs : bvmap 5 word) (mem : word -> option byte) (cur nx : batch) (nnx tot : Z),
  inL cur -> inL nx -> b_self cur <> b_self nx ->
  (length (b_items cur) <= 1021)%nat -> (length (b_items nx) <= 1021)%nat ->
  kBatchBytes <= b_bytes cur <= 2 ^ 40 ->
  0 <= nnx < ASAN_CEIL -> nnx mod 8192 = 0 ->
  0 <= tot <= sum_bytes L0 -> sum_bytes L0 <= 2 ^ 40 ->
  getr regs 2 = w64 (spr - 16) -> getr regs 10 = w64 (A_QUAR + 160) -> getr regs 12 = w64 tot ->
  getr regs 14 = w64 (addrb ly cur) -> getr regs 5 = w64 (addrb ly nx) -> getr regs 15 = w64 kBatchSlots ->
  val_mem tfibsegs (mr mem) (spr - 8) 8 0x34418 ->
  val_mem tfibsegs (mr mem) (A_QUAR + 184) 8 (sum_bytes L0) ->
  bcell ly iw (mr mem) cur (addrb ly nx) -> bcell ly iw (mr mem) nx nnx ->
  DMseg_mbh.free_hyps W regs mem (addrb ly cur) (addrb ly nx) (zl (b_items cur)) (zl (b_items nx)) (b_bytes cur) nnx
    (sum_bytes L0) tot.
Proof.
intros regs mem cur nx nnx tot Ic Inx Ne Lc Ln Bc N1 N2 T1 T2 R2 R10 R12 R14 R5 R15 VRA VLB VC VN.
destruct spr_facts as (S1 & S2 & S3 & S4).
destruct (g_self W ly regs0 mem0 iw L0 HP cur Ic) as (C1 & C2 & C3 & C4).
destruct (g_self W ly regs0 mem0 iw L0 HP nx Inx) as (X1 & X2 & X3 & X4).
pose proof (g_apart W ly regs0 mem0 iw L0 HP cur nx Ic Inx Ne) as AP.
destruct VC as (VC0 & VC8 & VC16 & _). destruct VN as (VN0 & VN8 & VN16 & _).
assert (Usp : bv_unsigned (getr regs 2) = spr - 16) by (rewrite R2; unfold w64; apply unsigned_lit_small; numconst; lia).
assert (HC : 0 <= zl (b_items cur) <= 1021) by (unfold zl; lia).
assert (HN : 0 <= zl (b_items nx) <= 1021) by (unfold zl; lia).
constructor.
- rewrite Usp. numconst; lia.
- rewrite Usp. lia.
- exact (conj C1 (conj C2 C3)).
- exact (conj X1 (conj X2 X3)).
- unfold kBatchSlots. lia.
- exact Bc.
- exact (conj N1 N2).
- lia.
- rewrite restrict_mkst_fx. unfold DMseg_mbh.SS0, DMseg_mbh.SR0, DMseg_mbh.E0, w64.
  apply (entry_st_ok_full tfibsegs).
  + apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin;
      [apply regs_ok_Ereg | intros XX; discriminate | ] | intros XX; discriminate | ] | intros XX; discriminate | ]
      | intros XX; discriminate | ] | intros XX; discriminate | ].
    all: pin_close.
  + vm_compute. reflexivity.
  + unfold DMseg_mbh.REG0, DMseg_mbh.R_STK, DMseg_mbh.R_LH, DMseg_mbh.R_CUR, DMseg_mbh.R_NX.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl), Usp.
      split; [numconst; lia|]. split; [numconst; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs _ _ (spr - 16) 8 8 (SLit 0x34418) 0x34418); [reflexivity | cbn; numconst; lia | cbn; lia |].
      replace (spr - 16 + 8) with (spr - 8) by lia. exact VRA.
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      split; [numconst; lia|]. split; [numconst; lia|]. split; [intros o Ho; apply rw_wr; numconst; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs _ _ 0 (A_QUAR + 184) 8 (SOff 38%nat 0) (sum_bytes L0)); [rewrite sv_off0e; reflexivity | cbn; numconst; lia | cbn; lia |].
      rewrite Z.add_0_l. exact VLB.
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite hE32, unsigned_lit_small by (numconst; lia).
      split; [numconst; lia|]. split; [numconst; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      -- apply (chunk_ok_val tfibsegs _ _ (addrb ly cur) 8 8 (SOff 36%nat 0) (b_bytes cur)); [rewrite sv_off0e; reflexivity | cbn; numconst; lia | cbn; lia |].
         exact VC8.
      -- apply (chunk_ok_val tfibsegs _ _ (addrb ly cur) 16 8 (SOff 34%nat 0) (zl (b_items cur))); [rewrite sv_off0e; reflexivity | cbn; numconst; lia | cbn; lia |].
         exact VC16.
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite hE33, unsigned_lit_small by (numconst; lia).
      split; [numconst; lia|]. split; [numconst; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      -- apply (chunk_ok_val tfibsegs _ _ (addrb ly nx) 0 8 (SOff 37%nat 0) nnx); [rewrite sv_off0e; reflexivity | cbn; numconst; lia | cbn; lia |].
         rewrite Z.add_0_r. exact VN0.
      -- apply (chunk_ok_val tfibsegs _ _ (addrb ly nx) 16 8 (SOff 35%nat 0) (zl (b_items nx))); [rewrite sv_off0e; reflexivity | cbn; numconst; lia | cbn; lia |].
         exact VN16.
  + apply pairwise_disjoint_of_extents.
    unfold DMseg_mbh.REG0, DMseg_mbh.R_STK, DMseg_mbh.R_LH, DMseg_mbh.R_CUR, DMseg_mbh.R_NX, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl), Usp, hE32, hE33, !unsigned_lit_small by (numconst; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    numconst. splits; lia.
  + split; [|split; exact I].
    unfold DMseg_mbh.FFH. cbn [f_atoms atoms_ok]. numconst.
    split. { apply (ent_AF _ 2%nat (spr - 16));
             [rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2 | lia | lia | change (2 ^ 4) with 16; lia | lia]. }
    split. { apply (ent_AF _ 32%nat (addrb ly cur)); [reflexivity | lia | lia | change (2 ^ 13) with 8192; exact C3 | lia]. }
    split. { apply (ent_AF _ 33%nat (addrb ly nx)); [reflexivity | lia | lia | change (2 ^ 13) with 8192; exact X3 | lia]. }
    split. { apply (ent_AF _ 34%nat (zl (b_items cur))); [reflexivity | lia | lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
    split. { apply (ent_AF _ 35%nat (zl (b_items nx))); [reflexivity | lia | lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
    split. { apply (ent_AF _ 36%nat (b_bytes cur)); [reflexivity | lia | lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
    split. { apply (ent_AF _ 37%nat nnx); [reflexivity | lia | lia | change (2 ^ 13) with 8192; exact N2 | lia]. }
    split. { apply (ent_AF _ 38%nat (sum_bytes L0)); [reflexivity | lia | lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
    split; [|exact I].
    apply (ent_AF _ 39%nat tot); [reflexivity | lia | lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia].
Qed.

Lemma cE33 : forall regs a b c d, ew (Ereg regs (DMseg_mbc.XW a b c d)) 33 = Z_to_bv 64 b.
Proof. reflexivity. Qed.
Lemma cE32 : forall regs a b c d, ew (Ereg regs (DMseg_mbc.XW a b c d)) 32 = Z_to_bv 64 a.
Proof. reflexivity. Qed.
Lemma c_FH : forall (regs : bvmap 5 word) (mem : word -> option byte) (src dst endp w : Z),
  kHighMemBeg <= src -> src + 8 <= endp -> endp <= ASAN_CEIL -> src mod 8 = 0 -> endp mod 8 = 0 ->
  kHighMemBeg <= dst -> dst + 8 <= ASAN_CEIL -> dst mod 8 = 0 -> (src + 8 <= dst \/ dst + 8 <= src) -> 0 <= w < 2 ^ 64 ->
  getr regs 7 = w64 src -> getr regs 28 = w64 dst -> getr regs 29 = w64 endp ->
  val_mem tfibsegs (mr mem) src 8 w -> (forall a, dst <= a < dst + 8 -> apresent (w_H W) mem a) ->
  DMseg_mbc.free_hyps W regs mem src dst endp w.
Proof.
intros regs mem src dst endp w S1 S2 S3 S4 S5 D1 D2 D3 DJ Hw R7 R28 R29 VS PD.
constructor; [tauto | tauto | exact DJ | exact Hw |].
rewrite restrict_mkst_fx. unfold DMseg_mbc.SS0, DMseg_mbc.SR0, DMseg_mbc.E0, w64.
apply (entry_st_ok_full tfibsegs).
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin;
    [apply regs_ok_Ereg | intros XX; discriminate | ] | intros XX; discriminate | ] | intros XX; discriminate | ].
  all: pin_close.
- vm_compute. reflexivity.
- unfold DMseg_mbc.REG0, DMseg_mbc.R_SRC, DMseg_mbc.R_DST.
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite cE32, unsigned_lit_small by (numconst; lia).
    split; [numconst; lia|]. split; [numconst; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val tfibsegs _ _ src 0 8 (SOff 35%nat 0) w); [rewrite sv_off0e; reflexivity | cbn; numconst; lia | cbn; lia |].
    rewrite Z.add_0_r. exact VS.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite cE33, unsigned_lit_small by (numconst; lia).
    split; [numconst; lia|]. split; [numconst; lia|].
    split; [intros o Ho; apply apresent_writable; [numconst; lia | apply PD; lia]|].
    apply Forall_nil.
- apply pairwise_disjoint_of_extents.
  unfold DMseg_mbc.REG0, DMseg_mbc.R_SRC, DMseg_mbc.R_DST, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite cE32, cE33, !unsigned_lit_small by (numconst; lia).
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. splits; lia.
- split; [|split; exact I].
  unfold DMseg_mbc.FFC. cbn [f_atoms atoms_ok]. numconst.
  split. { apply (ent_AF _ 32%nat src); [reflexivity | lia | lia | change (2 ^ 3) with 8; exact S4 | lia]. }
  split. { apply (ent_AF _ 33%nat dst); [reflexivity | lia | lia | change (2 ^ 3) with 8; exact D3 | lia]. }
  split. { apply (ent_AF _ 34%nat endp); [reflexivity | lia | lia | change (2 ^ 3) with 8; exact S5 | lia]. }
  split; [|exact I].
  apply (ent_AF _ 35%nat w); [reflexivity | lia | lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia].
Qed.

Lemma tE32 : forall regs a b c d e f g h i j k l m n, ew (Ereg regs (DMseg_mbt.XW a b c d e f g h i j k l m n)) 32 = Z_to_bv 64 a.
Proof. reflexivity. Qed.
Lemma tE33 : forall regs a b c d e f g h i j k l m n, ew (Ereg regs (DMseg_mbt.XW a b c d e f g h i j k l m n)) 33 = Z_to_bv 64 b.
Proof. reflexivity. Qed.
Lemma t_FH : forall (regs : bvmap 5 word) (mem : word -> option byte)
  (cur nx csz nsz nnx ncn lcnt llast tcnt tfirst tlast tby tot lbytes : Z),
  getr regs 2 = w64 (spr - 16) ->
  kHighMemBeg <= cur -> cur + kBatchBytes <= ASAN_CEIL -> cur mod 8192 = 0 ->
  kHighMemBeg <= nx -> nx + kBatchBytes <= ASAN_CEIL -> nx mod 8192 = 0 ->
  (cur + 24 <= nx \/ nx + 24 <= cur) ->
  (cur + 24 <= spr - 16 \/ spr + 32 <= cur) -> (nx + 24 <= spr - 16 \/ spr + 32 <= nx) ->
  kBatchBytes <= csz <= 2 ^ 40 -> kBatchBytes <= nsz <= 2 ^ 40 ->
  0 <= nnx < ASAN_CEIL -> nnx mod 8192 = 0 -> 0 <= ncn <= kBatchSlots ->
  1 <= lcnt <= 2 ^ 40 -> 0 <= llast < ASAN_CEIL -> llast mod 8192 = 0 ->
  0 <= tcnt < 2 ^ 40 -> 0 <= tfirst < ASAN_CEIL -> 0 <= tlast < ASAN_CEIL -> tlast mod 8192 = 0 ->
  (tcnt <> 0 -> kHighMemBeg <= tlast /\ tlast + kBatchBytes <= ASAN_CEIL /\
    (tlast + 8 <= cur \/ cur + 24 <= tlast) /\ (tlast + 8 <= nx \/ nx + 24 <= tlast) /\
    (tlast + 8 <= spr - 16 \/ spr + 32 <= tlast) /\ (forall a, tlast <= a < tlast + 8 -> apresent (w_H W) mem a)) ->
  0 <= tby <= 2 ^ 40 -> 0 <= tot -> tot + kBatchBytes <= lbytes <= 2 ^ 40 ->
  getr regs 10 = w64 (A_QUAR + 160) -> getr regs 11 = w64 spr -> getr regs 12 = w64 tot -> getr regs 13 = w64 csz ->
  getr regs 14 = w64 cur -> getr regs 5 = w64 nx -> getr regs 6 = w64 ncn -> getr regs 15 = w64 kBatchSlots ->
  getr regs 16 = w64 18446744073709543424 -> getr regs 17 = w64 kBatchBytes ->
  val_mem tfibsegs (mr mem) (spr - 8) 8 0x34418 ->
  val_mem tfibsegs (mr mem) spr 8 tcnt -> val_mem tfibsegs (mr mem) (spr + 8) 8 tfirst ->
  val_mem tfibsegs (mr mem) (spr + 16) 8 tlast -> val_mem tfibsegs (mr mem) (spr + 24) 8 tby ->
  val_mem tfibsegs (mr mem) (A_QUAR + 160) 8 lcnt -> val_mem tfibsegs (mr mem) (A_QUAR + 176) 8 llast ->
  val_mem tfibsegs (mr mem) (A_QUAR + 184) 8 lbytes ->
  val_mem tfibsegs (mr mem) nx 8 nnx -> val_mem tfibsegs (mr mem) (nx + 8) 8 nsz ->
  (forall a, spr <= a < spr + 32 -> apresent (w_H W) mem a) ->
  (forall a, cur <= a < cur + 24 -> apresent (w_H W) mem a) ->
  (forall a, nx <= a < nx + 24 -> apresent (w_H W) mem a) ->
  DMseg_mbt.free_hyps W regs mem cur nx csz nsz nnx ncn lcnt llast tcnt tfirst tlast tby tot lbytes.
Proof.
intros regs mem cur nx csz nsz nnx ncn lcnt llast tcnt tfirst tlast tby tot lbytes R2 C1 C2 C3 X1 X2 X3 CX CS XS
  Z1 Z2 N1 N2 K1 L1 L2 L3 T1 T2 T3 T4 TL B1 B2 B3 R10 R11 R12 R13 R14 R5 R6 R15 R16 R17
  VRA V0 V8 V16 V24 VL0 VL16 VL24 VN0 VN8 PS PC PN.
destruct spr_facts as (S1 & S2 & S3 & S4).
assert (Usp : bv_unsigned (getr regs 2) = spr - 16) by (rewrite R2; unfold w64; apply unsigned_lit_small; numconst; lia).
constructor.
- rewrite Usp. numconst; lia.
- rewrite Usp. lia.
- tauto.
- tauto.
- tauto.
- tauto.
- exact K1.
- tauto.
- tauto.
- intros Hc. destruct (TL Hc) as (A1 & A2 & A3 & A4 & A5 & A6). rewrite Usp.
  refine (conj A1 (conj A2 (conj A3 (conj A4 (conj _ A6))))). lia.
- tauto.
- rewrite restrict_mkst_fx. unfold DMseg_mbt.SS0, DMseg_mbt.SR0, DMseg_mbt.E0, w64.
  apply (entry_st_ok_full tfibsegs).
  + apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin;
      [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin;
      [apply regs_ok_Ereg | intros XX; discriminate | ] | intros XX; discriminate | ] | intros XX; discriminate | ]
      | intros XX; discriminate | ] | intros XX; discriminate | ] | intros XX; discriminate | ]
      | intros XX; discriminate | ] | intros XX; discriminate | ] | intros XX; discriminate | ]
      | intros XX; discriminate | ].
    all: try pin_close.
    cbn [sv_denot]. rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl), Usp, R11. unfold w64. f_equal. lia.
  + vm_compute. reflexivity.
  + unfold DMseg_mbt.REG0, DMseg_mbt.R_STK, DMseg_mbt.R_LH1, DMseg_mbt.R_LH2, DMseg_mbt.R_CUR, DMseg_mbt.R_NX.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]].
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl), Usp.
      split; [numconst; lia|]. split; [numconst; lia|].
      split; [intros o Ho; apply apresent_writable; [numconst; lia | apply PS; lia]|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]].
      -- apply (chunk_ok_val tfibsegs _ _ (spr - 16) 8 8 (SLit 0x34418) 0x34418); [reflexivity | cbn; lia | cbn; lia |].
         replace (spr - 16 + 8) with (spr - 8) by lia. exact VRA.
      -- apply (chunk_ok_val tfibsegs _ _ (spr - 16) 16 8 (SOff 40%nat 0) tcnt); [rewrite sv_off0e; reflexivity | cbn; numconst; lia | cbn; lia |].
         replace (spr - 16 + 16) with spr by lia. exact V0.
      -- apply (chunk_ok_val tfibsegs _ _ (spr - 16) 24 8 (SOff 41%nat 0) tfirst); [rewrite sv_off0e; reflexivity | cbn; numconst; lia | cbn; lia |].
         replace (spr - 16 + 24) with (spr + 8) by lia. exact V8.
      -- apply (chunk_ok_val tfibsegs _ _ (spr - 16) 32 8 (SOff 42%nat 0) tlast); [rewrite sv_off0e; reflexivity | cbn; numconst; lia | cbn; lia |].
         replace (spr - 16 + 32) with (spr + 16) by lia. exact V16.
      -- apply (chunk_ok_val tfibsegs _ _ (spr - 16) 40 8 (SOff 43%nat 0) tby); [rewrite sv_off0e; reflexivity | cbn; numconst; lia | cbn; lia |].
         replace (spr - 16 + 40) with (spr + 24) by lia. exact V24.
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      split; [numconst; lia|]. split; [numconst; lia|]. split; [intros o Ho; apply rw_wr; numconst; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs _ _ 0 (A_QUAR + 160) 8 (SOff 38%nat 0) lcnt); [rewrite sv_off0e; reflexivity | cbn; numconst; lia | cbn; lia |].
      rewrite Z.add_0_l. exact VL0.
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      split; [numconst; lia|]. split; [numconst; lia|]. split; [intros o Ho; apply rw_wr; numconst; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      -- apply (chunk_ok_val tfibsegs _ _ 0 (A_QUAR + 176) 8 (SOff 39%nat 0) llast); [rewrite sv_off0e; reflexivity | cbn; numconst; lia | cbn; lia |].
         rewrite Z.add_0_l. exact VL16.
      -- apply (chunk_ok_val tfibsegs _ _ 0 (A_QUAR + 184) 8 (SOff 45%nat 0) lbytes); [rewrite sv_off0e; reflexivity | cbn; numconst; lia | cbn; lia |].
         rewrite Z.add_0_l. exact VL24.
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite tE32, unsigned_lit_small by (numconst; lia).
      split; [numconst; lia|]. split; [numconst; lia|].
      split; [intros o Ho; apply apresent_writable; [numconst; lia | apply PC; lia]|].
      apply Forall_nil.
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite tE33, unsigned_lit_small by (numconst; lia).
      split; [numconst; lia|]. split; [numconst; lia|].
      split; [intros o Ho; apply apresent_writable; [numconst; lia | apply PN; lia]|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      -- apply (chunk_ok_val tfibsegs _ _ nx 0 8 (SOff 36%nat 0) nnx); [rewrite sv_off0e; reflexivity | cbn; numconst; lia | cbn; lia |].
         rewrite Z.add_0_r. exact VN0.
      -- apply (chunk_ok_val tfibsegs _ _ nx 8 8 (SOff 35%nat 0) nsz); [rewrite sv_off0e; reflexivity | cbn; numconst; lia | cbn; lia |].
         exact VN8.
  + apply pairwise_disjoint_of_extents.
    unfold DMseg_mbt.REG0, DMseg_mbt.R_STK, DMseg_mbt.R_LH1, DMseg_mbt.R_LH2, DMseg_mbt.R_CUR, DMseg_mbt.R_NX, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl), Usp, tE32, tE33, !unsigned_lit_small by (numconst; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    numconst. splits; lia.
  + split; [|split; exact I].
    unfold DMseg_mbt.FFT. cbn [f_atoms atoms_ok]. numconst.
    split. { apply (ent_AF _ 2%nat (spr - 16));
             [rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2 | lia | lia | change (2 ^ 4) with 16; lia | lia]. }
    split. { apply (ent_AF _ 32%nat cur); [reflexivity | lia | lia | change (2 ^ 13) with 8192; exact C3 | lia]. }
    split. { apply (ent_AF _ 33%nat nx); [reflexivity | lia | lia | change (2 ^ 13) with 8192; exact X3 | lia]. }
    split. { apply (ent_AF _ 34%nat csz); [reflexivity | lia | lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
    split. { apply (ent_AF _ 35%nat nsz); [reflexivity | lia | lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
    split. { apply (ent_AF _ 36%nat nnx); [reflexivity | lia | lia | change (2 ^ 13) with 8192; exact N2 | lia]. }
    split. { apply (ent_AF _ 37%nat ncn); [reflexivity | lia | lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
    split. { apply (ent_AF _ 38%nat lcnt); [reflexivity | lia | lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
    split. { apply (ent_AF _ 39%nat llast); [reflexivity | lia | lia | change (2 ^ 13) with 8192; exact L3 | lia]. }
    split. { apply (ent_AF _ 40%nat tcnt); [reflexivity | lia | lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
    split. { apply (ent_AF _ 41%nat tfirst); [reflexivity | lia | lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
    split. { apply (ent_AF _ 42%nat tlast); [reflexivity | lia | lia | change (2 ^ 13) with 8192; exact T4 | lia]. }
    split. { apply (ent_AF _ 43%nat tby); [reflexivity | lia | lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
    split. { apply (ent_AF _ 44%nat tot); [reflexivity | lia | lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
    split; [|exact I].
    apply (ent_AF _ 45%nat lbytes); [reflexivity | lia | lia | change (2 ^ 0) with 1; apply Z.mod_1_r | lia].
Qed.

Lemma dom_keep : forall (D P : Z -> Prop) (memA memB : word -> option byte),
  (forall a, P a \/ ~ P a) -> (forall a, D a -> 0 <= a < 2 ^ 64) -> (forall a, D a -> apresent (w_H W) memA a) ->
  (forall x : word, ~ P (bv_unsigned x) -> memB x = memA x) -> (forall a, P a -> D a -> apresent (w_H W) memB a) ->
  forall a, D a -> apresent (w_H W) memB a.
Proof.
intros D P memA memB Hd HR HA HF HQ a Ha. destruct (Hd a) as [Hp|Hn]; [exact (HQ a Hp Ha)|].
exact (apresent_keep (w_H W) P memA memB a HF Hn (HR a Ha) (HA a Ha)).
Qed.
Lemma vm_pres : forall mem a (n : nat) v a', val_mem tfibsegs (mr mem) a n v ->
  a <= a' < a + Z.of_nat n -> TFIB_IMG_END <= a' < 2 ^ 64 -> apresent (w_H W) mem a'.
Proof.
intros mem a n v a' Hv Ha Hhi.
assert (E : exists b, mbyte tfibsegs (mr mem) a' = Some b).
{ exists (Z_to_bv 8 (YO0f.le_byte v n (Z.to_nat (a' - a)))). replace a' with (a + Z.of_nat (Z.to_nat (a' - a))) at 1 by lia. apply Hv. lia. }
destruct E as [b Hb]. exact (mbyte_high_apresent (w_H W) mem a' b Hhi Hb).
Qed.

Definition PRES (mem : word -> option byte) : Prop :=
  forall a, (spr - 16 <= a < spr + 32 \/ exists b, inL b /\ bobj_of ly b a) -> apresent (w_H W) mem a.
Lemma PRES_dom : forall a, (spr - 16 <= a < spr + 32 \/ exists b, inL b /\ bobj_of ly b a) ->
  kHighMemBeg <= a /\ 0 <= a < 2 ^ 64.
Proof.
intros a [Ha | (b & Hb & Ho)]; destruct spr_facts as (S1 & S2 & S3 & S4).
- numconst. lia.
- destruct (g_self W ly regs0 mem0 iw L0 HP b Hb) as (B1 & B2 & _). unfold bobj_of in Ho. numconst. lia.
Qed.
Lemma PRES_keep : forall (P : Z -> Prop) memA memB, (forall a, P a \/ ~ P a) -> PRES memA ->
  (forall x : word, ~ P (bv_unsigned x) -> memB x = memA x) ->
  (forall a, P a -> kHighMemBeg <= a -> apresent (w_H W) memB a) -> PRES memB.
Proof.
intros P memA memB Hd HA HF HQ. unfold PRES.
apply (dom_keep _ P memA memB Hd); [intros a Ha; destruct (PRES_dom a Ha) as (_ & R); exact R | exact HA | exact HF |].
intros a Hp Ha. apply HQ; [exact Hp | destruct (PRES_dom a Ha) as (R & _); exact R].
Qed.
Lemma PRES_0 : PRES mem0.
Proof.
intros a [Ha | (b & Hb & Ho)].
- exact (mb_pres _ _ _ _ _ _ HP a Ha).
- unfold inL0 in Hb. apply in_map_iff in Hb as (b0 & E & Hb0).
  apply (mb_bpres _ _ _ _ _ _ HP b0 a Hb0). unfold bobj_of, addrb in *. rewrite E. exact Ho.
Qed.

Lemma nd_sep : forall {A B : Type} (f : A -> B) l1 l2 x y, List.NoDup (map f (l1 ++ l2)) -> In x l1 -> In y l2 -> f x <> f y.
Proof.
intros A B f l1. induction l1 as [|a l1 IH]; intros l2 x y ND Hx Hy; [destruct Hx|].
cbn [app map] in ND. inversion ND as [|? ? Hn ND']; subst. destruct Hx as [<-|Hx].
- intros E. apply Hn. rewrite map_app. apply in_or_app. right. rewrite E. apply in_map. exact Hy.
- exact (IH l2 x y ND' Hx Hy).
Qed.
Lemma sum_bytes_lb : forall l, (forall b, In b l -> kBatchBytes <= b_bytes b) -> kBatchBytes * zl l <= sum_bytes l.
Proof.
induction l as [|b l IH]; intros H; [change (zl (@nil batch)) with 0; rewrite Z.mul_0_r; cbn; lia|]. rewrite sum_bytes_cons', zl_cons.
pose proof (H b (or_introl eq_refl)). pose proof (IH (fun b' Hb' => H b' (or_intror Hb'))). lia.
Qed.
Lemma lf_items : forall Lc b k, flat_map b_items Lc = flat_map b_items L0 -> In b Lc -> In k (b_items b) ->
  In k (flat_map b_items L0).
Proof. intros Lc b k E Hb Hk. rewrite <- E. apply in_flat_map. exists b. tauto. Qed.
Lemma lf_bytes : forall Lc ex : list batch, flat_map b_items Lc = flat_map b_items L0 ->
  sum_bytes Lc + kBatchBytes * zl ex = sum_bytes L0 ->
  (forall b, In b Lc -> kBatchBytes <= b_bytes b <= 2 ^ 31) /\
  kBatchBytes * zl Lc + kBatchBytes * zl ex <= sum_bytes L0 /\ sum_bytes L0 <= 2 ^ 31.
Proof.
intros Lc ex EI EB.
assert (LO : forall b, In b Lc -> kBatchBytes <= b_bytes b)
  by (intros b Hb; apply (g_bytes_lo W ly regs0 mem0 iw L0 HP); intros k Hk; exact (lf_items Lc b k EI Hb Hk)).
pose proof (mb_bytes _ _ _ _ _ _ HP) as SB. pose proof (sum_bytes_lb Lc LO) as LB. pose proof (zl_nonneg ex).
split; [|unfold kBatchBytes in *; lia].
intros b Hb. split; [exact (LO b Hb)|].
pose proof (sum_bytes_ge Lc b Hb (fun b' Hb' => Z.le_trans 0 kBatchBytes _ ltac:(unfold kBatchBytes; lia) (LO b' Hb'))).
unfold kBatchBytes in *. lia.
Qed.
Lemma fa_MB_L0 : fa ly (fst (MB L0)) 0 = fa ly L0 0.
Proof.
pose proof (mb_len _ _ _ _ _ _ HP) as HL. revert HL. case_eq L0; [intros _ HX; cbn in HX; lia|]. intros b t _ _.
unfold MB. destruct (mbcf_head (length (b :: t)) b t) as (t' & [E | (its & E)]); rewrite E; reflexivity.
Qed.

Lemma mbwin_obj : forall (Lk ex : list batch) a,
  (forall b, In b (Lk ++ ex) -> inL b /\ (length (b_items b) <= 1021)%nat) ->
  mbwin ly regs0 L0 Lk ex a ->
  spr - 16 <= a < spr + 32 \/ A_QUAR + 160 <= a < A_QUAR + 192 \/ exists b, inL b /\ bobj_of ly b a.
Proof.
intros Lk ex a HB [Ha | [Ha | (b & Hb & Hc)]]; [left; exact Ha | right; left; exact Ha |].
right; right. exists b.
apply in_app_or in Hb as [Hb | Hb].
- assert (inL b) by (apply in_map; exact Hb). split; [exact H|].
  destruct (mb_bfacts _ _ _ _ _ _ HP b Hb) as (_ & _ & _ & (_ & X) & _).
  unfold bobj_of. exact (g_cells ly b a ltac:(unfold kBatchSlots in X; lia) Hc).
- destruct (HB b Hb) as [H1 H2]. split; [exact H1|]. unfold bobj_of. exact (g_cells ly b a H2 Hc).
Qed.
Lemma obj_rng : forall a, (spr - 16 <= a < spr + 32 \/ A_QUAR + 160 <= a < A_QUAR + 192 \/ exists b, inL b /\ bobj_of ly b a) ->
  0 <= a < 2 ^ 64 /\ (A_QUAR + 160 <= a < A_QUAR + 192 \/ kHighMemBeg <= a).
Proof.
intros a H. destruct spr_facts as (S1 & S2 & S3 & S4).
destruct H as [Ha | [Ha | (b & Hb & Ho)]].
- numconst. lia.
- numconst. lia.
- destruct (g_self W ly regs0 mem0 iw L0 HP b Hb) as (B1 & B2 & _). unfold bobj_of in Ho. numconst. lia.
Qed.

Lemma MK : forall (Lk ex : list batch) (memA memB : word -> option byte) (P : Z -> Prop),
  (forall b, In b (Lk ++ ex) -> inL b /\ (length (b_items b) <= 1021)%nat) ->
  (forall a, P a \/ ~ P a) -> (forall x : word, ~ P (bv_unsigned x) -> memB x = memA x) ->
  (forall a, P a -> mbwin ly regs0 L0 Lk ex a) ->
  (forall a, P a -> kHighMemBeg <= a -> apresent (w_H W) memB a) ->
  (forall x : word, ~ mbwin ly regs0 L0 Lk ex (bv_unsigned x) -> memA x = mem0 x) ->
  (forall a, mbwin ly regs0 L0 Lk ex a -> kHighMemBeg <= a -> apresent (w_H W) memA a) ->
  (forall x : word, ~ mbwin ly regs0 L0 Lk ex (bv_unsigned x) -> memB x = mem0 x) /\
  (forall a, mbwin ly regs0 L0 Lk ex a -> kHighMemBeg <= a -> apresent (w_H W) memB a).
Proof.
intros Lk ex memA memB P HB Hd HF HPw HPp FA PA. split.
- intros x Hx. rewrite HF by (intros Hp; exact (Hx (HPw _ Hp))). exact (FA x Hx).
- intros a Ha Hh. destruct (Hd a) as [Hp | Hn]; [exact (HPp a Hp Hh)|].
  apply (apresent_keep (w_H W) P memA memB a HF Hn); [exact (proj1 (obj_rng a (mbwin_obj Lk ex a HB Ha))) | exact (PA a Ha Hh)].
Qed.

Lemma lcn_keepP : forall (P : Z -> Prop) (m m' : word -> option byte) l z,
  (forall x : word, ~ P (bv_unsigned x) -> m' x = m x) ->
  (forall b, In b l -> inL b /\ (length (b_items b) <= 1021)%nat /\ forall a, bcells_of ly b a -> ~ P a) ->
  lcn ly iw (mr m) l z -> lcn ly iw (mr m') l z.
Proof.
intros P m m' l z HF HB HL. apply (lcn_keep (w_H W) ly iw P m m' l z HF); [|exact HL].
intros b Hb. destruct (HB b Hb) as (I & S & C). destruct (g_self W ly regs0 mem0 iw L0 HP b I) as (B1 & B2 & _).
split; [exact C|]. numconst. splits; lia.
Qed.
Lemma vm_keepP : forall (P : Z -> Prop) (m m' : word -> option byte) a (n : nat) v,
  (forall x : word, ~ P (bv_unsigned x) -> m' x = m x) ->
  (forall i, 0 <= i < Z.of_nat n -> ~ P (a + i)) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  val_mem tfibsegs (mr m) a n v -> val_mem tfibsegs (mr m') a n v.
Proof.
intros P m m' a n v HF HN H1 H2 HV. apply (vm_keep (w_H W) P m m' a n v HF); [|exact HV].
intros i Hi. split; [exact (HN i Hi) | lia].
Qed.

Definition CWw (cur : batch) (j : Z) (a : Z) : Prop :=
  addrb ly cur + 24 + 8 * zl (b_items cur) <= a < addrb ly cur + 24 + 8 * (zl (b_items cur) + j).
Definition CP (regs3 : bvmap 5 word) (mem3 : word -> option byte) (cur nx : batch) (j : nat)
  (W' : world tfibsegs) (c' : config) : Prop :=
  W' = W /\ (j < length (b_items nx))%nat /\ exists regsC memC matC,
  c' = mkCfg (mkst regsC (w64 0x345c4) memC (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) matC md0) /\
  (forall r, In r DMseg_mbc.SREGS -> getr regsC r = getr regs3 r) /\
  getr regsC 7 = w64 (addrb ly nx + 24 + 8 * Z.of_nat j) /\
  getr regsC 28 = w64 (addrb ly cur + 24 + 8 * (zl (b_items cur) + Z.of_nat j)) /\
  getr regsC 29 = w64 (addrb ly nx + 24 + 8 * zl (b_items nx)) /\
  (forall x : word, ~ CWw cur (Z.of_nat j) (bv_unsigned x) -> memC x = mem3 x) /\
  (forall i k, (i < j)%nat -> nth_error (b_items nx) i = Some k ->
     val_mem tfibsegs (mr memC) (addrb ly cur + 24 + 8 * (zl (b_items cur) + Z.of_nat i)) 8 (iw k)) /\
  PRES memC.
Definition CD (regs3 : bvmap 5 word) (mem3 : word -> option byte) (cur nx : batch) (W' : world tfibsegs) (c' : config) : Prop :=
  W' = W /\ exists regsC memC matC,
  c' = mkCfg (mkst regsC (w64 0x345d8) memC (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) matC md0) /\
  (forall r, In r DMseg_mbc.SREGS -> getr regsC r = getr regs3 r) /\
  (forall x : word, ~ CWw cur (zl (b_items nx)) (bv_unsigned x) -> memC x = mem3 x) /\
  (forall i k, nth_error (b_items nx) i = Some k ->
     val_mem tfibsegs (mr memC) (addrb ly cur + 24 + 8 * (zl (b_items cur) + Z.of_nat i)) 8 (iw k)) /\
  PRES memC.

Lemma copy_loop : forall (regs3 : bvmap 5 word) (mem3 : word -> option byte) (mat3 : list word) (cur nx : batch),
  inL cur -> inL nx -> b_self cur <> b_self nx ->
  (length (b_items cur) + length (b_items nx) <= 1021)%nat -> (1 <= length (b_items nx))%nat ->
  (forall k, In k (b_items nx) -> 0 <= iw k < 2 ^ 64) ->
  getr regs3 7 = w64 (addrb ly nx + 24) -> getr regs3 28 = w64 (addrb ly cur + 24 + 8 * zl (b_items cur)) ->
  getr regs3 29 = w64 (addrb ly nx + 24 + 8 * zl (b_items nx)) ->
  (forall j k, nth_error (b_items nx) j = Some k ->
     val_mem tfibsegs (mr mem3) (addrb ly nx + 24 + 8 * Z.of_nat j) 8 (iw k)) ->
  PRES mem3 ->
  SRr tfibsegs W (mkCfg (mkst regs3 (w64 0x345c4) mem3 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat3 md0))
    (CD regs3 mem3 cur nx).
Proof.
intros regs3 mem3 mat3 cur nx Ic Inx Ne Lcn Ln1 IW R7 R28 R29 VS PR3.
destruct (g_self W ly regs0 mem0 iw L0 HP cur Ic) as (C1 & C2 & C3 & C4).
destruct (g_self W ly regs0 mem0 iw L0 HP nx Inx) as (X1 & X2 & X3 & X4).
pose proof (g_apart W ly regs0 mem0 iw L0 HP cur nx Ic Inx Ne) as AP.
assert (ZC : zl (b_items cur) = Z.of_nat (length (b_items cur))) by reflexivity.
assert (ZN : zl (b_items nx) = Z.of_nat (length (b_items nx))) by reflexivity.
assert (P0 : CP regs3 mem3 cur nx 0 W
  (mkCfg (mkst regs3 (w64 0x345c4) mem3 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat3 md0))).
{ split; [reflexivity|]. split; [lia|]. exists regs3, mem3, mat3. split; [reflexivity|].
  split; [intros r _; reflexivity|].
  split. { rewrite R7. f_equal. lia. }
  split. { rewrite R28. f_equal. lia. }
  split; [exact R29|]. split; [intros x _; reflexivity|]. split; [intros i k Hi; lia|]. exact PR3. }
refine (SRr_loop tfibsegs nat (fun j => (length (b_items nx) - j)%nat) (CP regs3 mem3 cur nx) (CD regs3 mem3 cur nx) _ 0%nat W _ P0).
clear P0. intros j W' c' (EW & Hj & regsC & memC & matC & Ec & RSc & Q7 & Q28 & Q29 & FRc & CPd & PRc). subst W' c'.
destruct (nth_error (b_items nx) j) as [k|] eqn:Ek; [|apply nth_error_None in Ek; lia].
pose proof (IW k (nth_error_In _ _ Ek)) as Kr.
assert (NUM : kHighMemBeg <= addrb ly nx + 24 + 8 * Z.of_nat j /\
  addrb ly nx + 24 + 8 * Z.of_nat j + 8 <= addrb ly nx + 24 + 8 * zl (b_items nx) /\
  addrb ly nx + 24 + 8 * zl (b_items nx) <= ASAN_CEIL /\
  (addrb ly nx + 24 + 8 * Z.of_nat j) mod 8 = 0 /\ (addrb ly nx + 24 + 8 * zl (b_items nx)) mod 8 = 0 /\
  kHighMemBeg <= addrb ly cur + 24 + 8 * (zl (b_items cur) + Z.of_nat j) /\
  addrb ly cur + 24 + 8 * (zl (b_items cur) + Z.of_nat j) + 8 <= ASAN_CEIL /\
  (addrb ly cur + 24 + 8 * (zl (b_items cur) + Z.of_nat j)) mod 8 = 0 /\
  (addrb ly nx + 24 + 8 * Z.of_nat j + 8 <= addrb ly cur + 24 + 8 * (zl (b_items cur) + Z.of_nat j) \/
   addrb ly cur + 24 + 8 * (zl (b_items cur) + Z.of_nat j) + 8 <= addrb ly nx + 24 + 8 * Z.of_nat j)).
{ rewrite ZC, ZN. unfold kBatchBytes in *. numconst. splits; lia. }
destruct NUM as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
assert (VSc : val_mem tfibsegs (mr memC) (addrb ly nx + 24 + 8 * Z.of_nat j) 8 (iw k)).
{ apply (vm_keepP (CWw cur (Z.of_nat j)) mem3 memC _ 8 (iw k) FRc); [| numconst; lia | numconst; lia | exact (VS j k Ek)].
  intros i Hi Hw. unfold CWw in Hw. rewrite ZC in Hw. unfold kBatchBytes in *. cbn in Hi. lia. }
assert (PDc : forall a, addrb ly cur + 24 + 8 * (zl (b_items cur) + Z.of_nat j) <= a <
  addrb ly cur + 24 + 8 * (zl (b_items cur) + Z.of_nat j) + 8 -> apresent (w_H W) memC a).
{ intros a Ha. apply PRc. right. exists cur. split; [exact Ic|]. unfold bobj_of. rewrite ZC in Ha. unfold kBatchBytes. lia. }
eapply SRr_bind.
{ exact (DMseg_mbc.segC W regsC memC md0 _ _ _ (iw k) matC
    (c_FH regsC memC _ _ _ (iw k) N1 N2 N3 N4 N5 N6 N7 N8 N9 Kr Q7 Q28 Q29 VSc PDc)). }
intros W2 c2 _ HC. unfold DMseg_mbc.postC in HC.
assert (HdW : forall a, DMseg_mbc.WIN (addrb ly cur + 24 + 8 * (zl (b_items cur) + Z.of_nat j)) a \/
  ~ DMseg_mbc.WIN (addrb ly cur + 24 + 8 * (zl (b_items cur) + Z.of_nat j)) a) by (intros a; unfold DMseg_mbc.WIN; lia).
destruct (addrb ly nx + 24 + 8 * Z.of_nat j + 8 =? addrb ly nx + 24 + 8 * zl (b_items nx)) eqn:Ee.
- apply Z.eqb_eq in Ee. destruct HC as (EW2 & _ & regsN & memN & matN & EcN & QS & _ & _ & _ & MQ & VW).
  apply SRr_ret. left. split; [exact EW2|]. exists regsN, memN, matN. split; [exact EcN|].
  split. { intros r Hr. rewrite (QS r Hr). exact (RSc r Hr). }
  split.
  { intros x Hx. rewrite MQ; [apply FRc; intros Hw; apply Hx; unfold CWw in *; lia|].
    intros Hw. apply Hx. unfold CWw, DMseg_mbc.WIN in *. lia. }
  split.
  { intros i k' Hk'. pose proof (nth_error_Some (b_items nx) i) as [NS _]. assert (Hi : (i < length (b_items nx))%nat) by (apply NS; rewrite Hk'; discriminate).
    destruct (Nat.eq_dec i j) as [-> | Hij].
    - rewrite Ek in Hk'. injection Hk' as <-. exact VW.
    - apply (vm_keepP (DMseg_mbc.WIN (addrb ly cur + 24 + 8 * (zl (b_items cur) + Z.of_nat j))) memC memN _ 8 (iw k') MQ);
        [| rewrite ZC; unfold kBatchBytes in *; numconst; lia | rewrite ZC; unfold kBatchBytes in *; numconst; lia |].
      + intros i0 Hi0 Hw. unfold DMseg_mbc.WIN in Hw. cbn in Hi0. lia.
      + apply CPd; [lia | exact Hk']. }
  apply (PRES_keep _ memC memN HdW PRc MQ). intros a Ha Hh. unfold DMseg_mbc.WIN in Ha.
  apply (vm_pres memN _ 8 (iw k) a VW); [cbn; lia | numconst; lia].
- apply Z.eqb_neq in Ee. destruct HC as (EW2 & _ & regsN & memN & matN & EcN & QS & Q7' & Q28' & Q29' & MQ & VW).
  apply SRr_ret. right. exists (S j). split; [lia|].
  split; [exact EW2|]. split; [rewrite ZN in Ee; lia|]. exists regsN, memN, matN. split; [exact EcN|].
  split. { intros r Hr. rewrite (QS r Hr). exact (RSc r Hr). }
  split. { rewrite Q7'. f_equal. lia. }
  split. { rewrite Q28'. f_equal. lia. }
  split; [exact Q29'|].
  split.
  { intros x Hx. rewrite MQ; [apply FRc; intros Hw; apply Hx; unfold CWw in *; lia|].
    intros Hw. apply Hx. unfold CWw, DMseg_mbc.WIN in *. lia. }
  split.
  { intros i k' Hi Hk'. destruct (Nat.eq_dec i j) as [-> | Hij].
    - rewrite Ek in Hk'. injection Hk' as <-. exact VW.
    - apply (vm_keepP (DMseg_mbc.WIN (addrb ly cur + 24 + 8 * (zl (b_items cur) + Z.of_nat j))) memC memN _ 8 (iw k') MQ);
        [| rewrite ZC; unfold kBatchBytes in *; numconst; lia | rewrite ZC; unfold kBatchBytes in *; numconst; lia |].
      + intros i0 Hi0 Hw. unfold DMseg_mbc.WIN in Hw. cbn in Hi0. lia.
      + apply CPd; [lia | exact Hk']. }
  apply (PRES_keep _ memC memN HdW PRc MQ). intros a Ha Hh. unfold DMseg_mbc.WIN in Ha.
  apply (vm_pres memN _ 8 (iw k) a VW); [cbn; lia | numconst; lia].
Qed.

Lemma la_in : forall l, l <> [] -> exists b, In b l /\ la ly l = addrb ly b.
Proof.
intros l Hl. unfold la. destruct (rev l) as [|b r] eqn:E.
- exfalso. apply Hl. apply (f_equal (@rev batch)) in E. rewrite rev_involutive in E. exact E.
- exists b. split; [|reflexivity]. apply in_rev. rewrite E. left. reflexivity.
Qed.
Lemma fa_snoc : forall l b, fa ly (l ++ [b]) 0 = if zl l =? 0 then addrb ly b else fa ly l 0.
Proof. intros [|x l] b; reflexivity. Qed.
Lemma nd_merge : forall done c n t ex, List.NoDup (map b_self (done ++ c :: n :: t ++ ex)) ->
  List.NoDup (map b_self (done ++ mergeb c n :: t ++ ex ++ [emptyb n])).
Proof.
intros done c n t ex H. eapply Permutation_NoDup; [|exact H].
rewrite !map_app. cbn [map]. rewrite !map_app. cbn [map mergeb emptyb b_self].
apply Permutation_app_head. apply perm_skip. rewrite app_assoc. apply Permutation_cons_append.
Qed.
Lemma in_merge : forall (done t : list batch) c n b, In b (done ++ mergeb c n :: t) -> b = mergeb c n \/ In b (done ++ c :: n :: t).
Proof.
intros done t c n b H. apply in_app_or in H as [H|[H|H]].
- right. apply in_or_app. left. exact H.
- left. symmetry. exact H.
- right. apply in_or_app. right. right. right. exact H.
Qed.
Lemma fm_merge : forall (done t : list batch) c n, flat_map b_items (done ++ mergeb c n :: t) = flat_map b_items (done ++ c :: n :: t).
Proof. intros done t c n. rewrite !flat_map_app. cbn [flat_map mergeb b_items]. rewrite <- !app_assoc. reflexivity. Qed.
Lemma sb_merge : forall (done t : list batch) c n, sum_bytes (done ++ mergeb c n :: t) = sum_bytes (done ++ c :: n :: t) - kBatchBytes.
Proof. intros done t c n. rewrite !sum_bytes_app', !sum_bytes_cons', b_bytes_merge. lia. Qed.
Lemma zl_merge : forall (done t : list batch) c n, zl (done ++ mergeb c n :: t) = zl (done ++ c :: n :: t) - 1.
Proof. intros done t c n. rewrite !zl_app, !zl_cons. lia. Qed.

Lemma lcn_relink : forall (P : Z -> Prop) (m m' : word -> option byte) l z z',
  (forall x : word, ~ P (bv_unsigned x) -> m' x = m x) ->
  (forall b, In b l -> inL b /\ (length (b_items b) <= 1021)%nat) ->
  (forall b a, In b l -> bcells_of ly b a -> P a -> la ly l <= a < la ly l + 8) ->
  (l <> [] -> val_mem tfibsegs (mr m') (la ly l) 8 z') ->
  List.NoDup (map b_self l) ->
  lcn ly iw (mr m) l z -> lcn ly iw (mr m') l z'.
Proof.
intros P m m' l. induction l as [|b l IH]; intros z z' HF HB HPw HV ND HL; [exact I|].
inversion ND as [|? ? Hn ND']; subst.
destruct HL as (HC & HL).
destruct (HB b (or_introl eq_refl)) as [Ib Lb].
destruct (g_self W ly regs0 mem0 iw L0 HP b Ib) as (B1 & B2 & B3 & _).
assert (KB : forall a v, bcells_of ly b a -> bcells_of ly b (a + 7) ->
  (a + 8 <= la ly (b :: l) \/ la ly (b :: l) + 8 <= a) -> val_mem tfibsegs (mr m) a 8 v -> val_mem tfibsegs (mr m') a 8 v).
{ intros a v C0 C7 Hap Hv. pose proof (g_cells ly b a Lb C0). pose proof (g_cells ly b (a + 7) Lb C7).
  apply (vm_keepP P m m' a 8 v HF); [| numconst; lia | numconst; cbn; lia | exact Hv].
  intros i Hi Hp. cbn in Hi. assert (Hc : bcells_of ly b (a + i)) by (unfold bcells_of in *; lia).
  pose proof (HPw b (a + i) (or_introl eq_refl) Hc Hp). lia. }
assert (Nb : forall j k, nth_error (b_items b) j = Some k -> (j < length (b_items b))%nat).
{ intros j k Hk. apply nth_error_Some. rewrite Hk. discriminate. }
destruct l as [|b' l'].
- cbn [lcn fa]. split; [|exact I].
  assert (LA : la ly [b] = addrb ly b) by reflexivity. rewrite LA in KB, HV.
  destruct HC as (H0 & H8 & H16 & Hs). unfold bcell.
  split; [exact (HV ltac:(discriminate))|].
  split; [apply KB; [unfold bcells_of, zl; lia | unfold bcells_of, zl; lia | lia | exact H8]|].
  split; [apply KB; [unfold bcells_of, zl; lia | unfold bcells_of, zl; lia | lia | exact H16]|].
  intros j k Hk. pose proof (Nb j k Hk).
  apply KB; [unfold bcells_of, zl; lia | unfold bcells_of, zl; lia | lia | exact (Hs j k Hk)].
- cbn [lcn] in HL |- *.
  assert (LA : la ly (b :: b' :: l') = la ly (b' :: l')) by exact (la_app_cons ly [b] b' l').
  split.
  + change (fa ly (b' :: l') z') with (fa ly (b' :: l') z).
    destruct (la_in (b' :: l') ltac:(discriminate)) as (bl & Hbl & Ela).
    destruct (HB bl (or_intror Hbl)) as [Ibl _].
    assert (Nsl : b_self b <> b_self bl) by (intros E; apply Hn; rewrite E; apply in_map; exact Hbl).
    pose proof (g_apart W ly regs0 mem0 iw L0 HP b bl Ib Ibl Nsl) as APb.
    destruct (g_self W ly regs0 mem0 iw L0 HP bl Ibl) as (L1 & L2 & L3 & _).
    rewrite LA, Ela in KB.
    destruct HC as (H0 & H8 & H16 & Hs). unfold bcell.
    split; [apply KB; [unfold bcells_of, zl; lia | unfold bcells_of, zl; lia | unfold kBatchBytes in *; lia | exact H0]|].
    split; [apply KB; [unfold bcells_of, zl; lia | unfold bcells_of, zl; lia | unfold kBatchBytes in *; lia | exact H8]|].
    split; [apply KB; [unfold bcells_of, zl; lia | unfold bcells_of, zl; lia | unfold kBatchBytes in *; lia | exact H16]|].
    intros j k Hk. pose proof (Nb j k Hk).
    apply KB; [unfold bcells_of, zl; lia | unfold bcells_of, zl; lia | unfold bcells_of, zl, kBatchBytes in *; lia | exact (Hs j k Hk)].
  + apply (IH z z' HF); [intros b0 Hb0; exact (HB b0 (or_intror Hb0)) | | | exact ND' | exact HL].
    * intros b0 a Hb0 Hc Hp. rewrite <- LA. exact (HPw b0 a (or_intror Hb0) Hc Hp).
    * intros _. rewrite <- LA. exact (HV ltac:(discriminate)).
Qed.

Definition LS : Type := (list batch * batch * batch * list batch * list batch)%type.
Definition LM (x : LS) : nat := match x with (_, _, _, t, _) => length t end.
Definition cfgH (regs : bvmap 5 word) (mem : word -> option byte) (mat : list word) : config :=
  mkCfg (mkst regs (w64 0x3458c) mem (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0).
Definition LP (x : LS) (W' : world tfibsegs) (c' : config) : Prop :=
  match x with (done, cur, nx, t, ex) =>
  mb_inv W ly regs0 mem0 md0 iw L0 done cur nx t ex W' c' /\ (exists pre, L0 = pre ++ nx :: t) /\
  (forall regs mem mat, c' = cfgH regs mem mat -> PRES mem) end.
Definition LQ (x : LS) (W' : world tfibsegs) (c' : config) : Prop :=
  mb_post W ly regs0 mem0 md0 iw L0 W' c' \/ exists x', (LM x' < LM x)%nat /\ LP x' W' c'.

Lemma cfgH_inj : forall regs mem mat regs' mem' mat', cfgH regs mem mat = cfgH regs' mem' mat' -> regs = regs' /\ mem = mem'.
Proof. intros regs mem mat regs' mem' mat' E. unfold cfgH in E. injection E as E1 E2. tauto. Qed.

Lemma MB_nomerge : forall c n t, can_merge c n = false -> MB (c :: n :: t) = (c :: fst (MB (n :: t)), snd (MB (n :: t))).
Proof. intros c n t H. rewrite MB_cons2, H. reflexivity. Qed.
Lemma MB_merge : forall c n t, can_merge c n = true ->
  MB (c :: n :: t) = (fst (MB (mergeb c n :: t)), emptyb n :: snd (MB (mergeb c n :: t))).
Proof. intros c n t H. rewrite MB_cons2, H. reflexivity. Qed.
Lemma cells_hi : forall b a, inL b -> (length (b_items b) <= 1021)%nat -> bcells_of ly b a ->
  kHighMemBeg <= a /\ a + 1 <= ASAN_CEIL /\ 0 <= a < 2 ^ 64.
Proof.
intros b a I L C. pose proof (g_cells ly b a L C). destruct (g_self W ly regs0 mem0 iw L0 HP b I) as (B1 & B2 & _).
numconst. lia.
Qed.

Definition HIDE (P : Prop) : Prop := P.
Ltac hide H := let T := type of H in change (HIDE T) in H.
Ltac inS := unfold DMseg_mbh.SREGS, DMseg_mbc.SREGS, DMseg_mbt.SREGS; cbn [In]; tauto.

Lemma step : forall x W' c', LP x W' c' -> SRr tfibsegs W' c' (LQ x).
Proof.
intros [[[[done cur] nx] t] ex] W' c' (HI & (pre & HPre) & HPR).
destruct HI as (EW & HMB & HS & HE & HND & HF & HIT & HB & regs & mem & mat & Ec & R2 & R1 & RS & R10 & R11 & R12 & R14 & R5
  & R15 & R16 & R17 & FR & PR & MV).
cbv zeta in MV. destruct MV as (VH0 & VH8 & VH16 & VH24 & VT0 & VT8 & VT16 & VT24 & VRA & VL & VX).
pose proof (HPR regs mem mat Ec) as PRm. subst W' c'.
destruct spr_facts as (S1 & S2 & S3 & S4).

assert (Icur : inL cur) by (apply HS; apply in_or_app; right; left; reflexivity).
assert (Inx : inL nx) by (apply HS; apply in_or_app; right; right; left; reflexivity).
assert (Ne : b_self cur <> b_self nx).
{ apply (nd_sep b_self (done ++ [cur]) (nx :: t ++ ex)); [rewrite <- app_assoc; exact HND | apply in_or_app; right; left; reflexivity | left; reflexivity]. }
assert (Lc : (length (b_items cur) <= 1021)%nat)
  by (rewrite Forall_forall in HF; apply HF; apply in_or_app; right; left; reflexivity).
assert (Ln : (length (b_items nx) <= 1021)%nat)
  by (rewrite Forall_forall in HF; apply HF; apply in_or_app; right; right; left; reflexivity).
assert (Ln1 : (1 <= length (b_items nx))%nat).
{ assert (In nx L0) by (rewrite HPre; apply in_or_app; right; left; reflexivity).
  destruct (mb_bfacts _ _ _ _ _ _ HP nx H) as (_ & _ & _ & (X & _) & _). exact X. }
assert (HBall : forall b, In b ((done ++ cur :: nx :: t) ++ ex) -> inL b /\ (length (b_items b) <= 1021)%nat).
{ intros b Hb. apply in_app_or in Hb as [Hb|Hb].
  - split; [exact (HS b Hb) | rewrite Forall_forall in HF; exact (HF b Hb)].
  - destruct (HE b Hb) as [I E]. split; [exact I | rewrite E; cbn; lia]. }
assert (HBc : forall b, In b ((done ++ cur :: nx :: t) ++ ex) -> forall a, bcells_of ly b a ->
  kHighMemBeg <= a /\ a + 1 <= ASAN_CEIL /\ 0 <= a < 2 ^ 64).
{ intros b Hb a Ha. destruct (HBall b Hb) as [I L]. exact (cells_hi b a I L Ha). }
destruct (lf_bytes _ ex HIT HB) as (BY & BT & SB).
assert (Bc : kBatchBytes <= b_bytes cur <= 2 ^ 40)
  by (pose proof (BY cur ltac:(apply in_or_app; right; left; reflexivity)); lia).
assert (Bn : kBatchBytes <= b_bytes nx <= 2 ^ 40)
  by (pose proof (BY nx ltac:(apply in_or_app; right; right; left; reflexivity)); lia).
pose proof (proj1 (lcn_app ly iw _ done (cur :: nx :: t) 0) VL) as (VLd & VLc).
cbn [lcn fa] in VLc. destruct VLc as (VC & VN & VLt).
assert (NX : 0 <= fa ly t 0 < ASAN_CEIL /\ fa ly t 0 mod 8192 = 0 /\ (t = [] <-> fa ly t 0 = 0)).
{ destruct t as [|n2 t2]; [cbn; split; [numconst; lia | split; [reflexivity | tauto]]|].
  assert (inL n2) by (apply HS; apply in_or_app; right; right; right; left; reflexivity).
  destruct (g_self W ly regs0 mem0 iw L0 HP n2 H) as (A1 & A2 & A3 & _). cbn [fa].
  split; [numconst; lia|]. split; [exact A3|]. split; [discriminate | numconst; lia]. }
destruct NX as (NX1 & NX2 & NX3).
assert (TOT : 0 <= kBatchBytes * zl ex <= sum_bytes L0)
  by (pose proof (zl_nonneg ex); pose proof (zl_nonneg (done ++ cur :: nx :: t)); unfold kBatchBytes in *; lia).
eapply SRr_bind.
{ exact (DMseg_mbh.segH W regs mem md0 (addrb ly cur) (addrb ly nx) (zl (b_items cur)) (zl (b_items nx)) (b_bytes cur)
    (fa ly t 0) (sum_bytes L0) (kBatchBytes * zl ex) mat
    (h_FH regs mem cur nx (fa ly t 0) (kBatchBytes * zl ex) Icur Inx Ne Lc Ln Bc NX1 NX2 TOT
       ltac:(lia) R2 R10 R12 R14 R5 R15 VRA VH24 VC VN)). }
intros W2 c2 _ HPH. unfold DMseg_mbh.postH in HPH.

assert (HdH : forall a, DMseg_mbh.WIN a \/ ~ DMseg_mbh.WIN a) by (intros a; unfold DMseg_mbh.WIN; lia).
assert (HsubH : forall a, DMseg_mbh.WIN a -> mbwin ly regs0 L0 (done ++ cur :: nx :: t) ex a)
  by (intros a Ha; right; left; unfold DMseg_mbh.WIN in Ha; lia).
assert (HlowH : forall a, DMseg_mbh.WIN a -> kHighMemBeg <= a -> False)
  by (intros a Ha Hh; unfold DMseg_mbh.WIN in Ha; numconst; lia).
destruct (1021 <? zl (b_items cur) + zl (b_items nx)) eqn:Ecm.
{ assert (CMf : can_merge cur nx = false).
  { unfold can_merge. apply Nat.leb_gt. apply Z.ltb_lt in Ecm. unfold zl in Ecm. unfold kBatchSlots. lia. }
  destruct (fa ly t 0 =? 0) eqn:Ent.
  -
    apply Z.eqb_eq in Ent. assert (t = []) by (apply NX3; exact Ent). subst t.
    destruct HPH as (EW2 & regs2 & mem2 & mat2 & Ec2 & Q2 & Q1 & QSX & MQ & VLB2).
    apply SRr_ret. left.
    assert (HMB' : MB L0 = (done ++ [cur; nx], ex)).
    { rewrite HMB, MB_nomerge by exact CMf. rewrite MB_one. cbn [fst snd]. rewrite app_nil_r. reflexivity. }
    destruct (MK _ ex mem mem2 DMseg_mbh.WIN HBall HdH MQ HsubH (fun a Ha Hh => False_ind _ (HlowH a Ha Hh)) FR PR)
      as (FR2 & PR2).
    unfold mb_post. cbv zeta. rewrite fa_MB_L0, HMB'. cbn [fst snd].
    split; [exact EW2|]. exists regs2, mem2, mat2. split; [exact Ec2|].
    split. { rewrite Q2, R2. unfold w64. rewrite unsigned_lit_small by (numconst; lia). f_equal. lia. }
    split; [exact Q1|].
    split. { intros r Hr. rewrite (QSX r Hr). exact (RS r Hr). }
    split; [exact FR2|]. split; [exact PR2|].
    assert (KH : forall a n v, (a + Z.of_nat n <= A_QUAR + 184 \/ A_QUAR + 192 <= a) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
      val_mem tfibsegs (mr mem) a n v -> val_mem tfibsegs (mr mem2) a n v).
    { intros a n v Ho H1 H2 HV. apply (vm_keepP DMseg_mbh.WIN mem mem2 a n v MQ); [|exact H1|exact H2|exact HV].
      intros i Hi. unfold DMseg_mbh.WIN. lia. }
    assert (KL : forall l, (forall b, In b l -> In b ((done ++ [cur; nx]) ++ ex)) -> lcn ly iw (mr mem) l 0 -> lcn ly iw (mr mem2) l 0).
    { intros l Hl HV. apply (lcn_keepP DMseg_mbh.WIN mem mem2 l 0 MQ); [|exact HV].
      intros b Hb. destruct (HBall b (Hl b Hb)) as [I L]. split; [exact I|]. split; [exact L|].
      intros a Ha Hw. destruct (cells_hi b a I L Ha) as (A1 & _). exact (HlowH a Hw A1). }
    split; [apply KH; [cbn; lia | numconst; lia | cbn; numconst; lia | exact VH0]|].
    split; [apply KH; [cbn; lia | numconst; lia | cbn; numconst; lia | exact VH8]|].
    split; [apply KH; [cbn; lia | numconst; lia | cbn; numconst; lia | exact VH16]|].
    split; [exact VLB2|].
    split; [apply KH; [numconst; lia | lia | cbn; numconst; lia | exact VT0]|].
    split; [apply KH; [numconst; lia | lia | cbn; numconst; lia | exact VT8]|].
    split; [apply KH; [numconst; lia | lia | cbn; numconst; lia | exact VT16]|].
    split; [apply KH; [numconst; lia | lia | cbn; numconst; lia | exact VT24]|].
    split.
    { apply (vm_keepP (mbwin ly regs0 L0 (done ++ [cur; nx]) ex) mem0 mem2 (A_QUAR + 152) 4 257 FR2);
        [| numconst; lia | cbn; numconst; lia | exact (mb_mutex _ _ _ _ _ _ HP)].
      intros i Hi Hw. destruct (obj_rng _ (mbwin_obj _ ex _ HBall Hw)) as (_ & X). cbn in Hi. numconst. lia. }
    split; [apply KL; [intros b Hb; apply in_or_app; left; exact Hb | exact VL]|].
    apply KL; [intros b Hb; apply in_or_app; right; exact Hb | exact VX].
  -
    apply Z.eqb_neq in Ent. destruct t as [|n2 t2]; [cbn in Ent; contradiction|].
    destruct HPH as (EW2 & regs2 & mem2 & mat2 & Ec2 & Q2 & QS & Q10 & Q12 & Q15 & Q14 & Q5 & MQ & VLB2).
    apply SRr_ret. right. exists (done ++ [cur], nx, n2, t2, ex). split; [cbn; lia|].
    assert (EQL : forall l : list batch, (done ++ [cur]) ++ nx :: n2 :: l = done ++ cur :: nx :: n2 :: l)
      by (intros l; rewrite <- app_assoc; reflexivity).
    destruct (MK _ ex mem mem2 DMseg_mbh.WIN HBall HdH MQ HsubH (fun a Ha Hh => False_ind _ (HlowH a Ha Hh)) FR PR)
      as (FR2 & PR2).
    unfold LP. cbv beta iota. split; [|split].
    + unfold mb_inv. rewrite !EQL.
      split; [exact EW2|].
      split. { rewrite HMB, MB_nomerge by exact CMf. cbn [fst snd]. rewrite <- app_assoc. reflexivity. }
      split; [exact HS|]. split; [exact HE|]. split; [exact HND|]. split; [exact HF|]. split; [exact HIT|]. split; [exact HB|].
      exists regs2, mem2, mat2. split; [exact Ec2|].
      split. { rewrite Q2. exact R2. }
      split. { rewrite (QS 1%bv) by inS. exact R1. }
      split. { intros r Hr. rewrite QS by (unfold SREGSX in Hr; unfold DMseg_mbh.SREGS; cbn [In] in Hr |- *; tauto). exact (RS r Hr). }
      split; [exact Q10|].
      split. { rewrite (QS 11%bv) by inS. exact R11. }
      split; [exact Q12|]. split; [exact Q14|]. split; [exact Q5|]. split; [exact Q15|].
      split. { rewrite (QS 16%bv) by inS. exact R16. }
      split. { rewrite (QS 17%bv) by inS. exact R17. }
      split; [exact FR2|]. split; [exact PR2|].
      cbv zeta.
      assert (KH : forall a n v, (a + Z.of_nat n <= A_QUAR + 184 \/ A_QUAR + 192 <= a) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
        val_mem tfibsegs (mr mem) a n v -> val_mem tfibsegs (mr mem2) a n v).
      { intros a n v Ho H1 H2 HV. apply (vm_keepP DMseg_mbh.WIN mem mem2 a n v MQ); [|exact H1|exact H2|exact HV].
        intros i Hi. unfold DMseg_mbh.WIN. lia. }
      assert (KL : forall l, (forall b, In b l -> In b ((done ++ cur :: nx :: n2 :: t2) ++ ex)) ->
        lcn ly iw (mr mem) l 0 -> lcn ly iw (mr mem2) l 0).
      { intros l Hl HV. apply (lcn_keepP DMseg_mbh.WIN mem mem2 l 0 MQ); [|exact HV].
        intros b Hb. destruct (HBall b (Hl b Hb)) as [I L]. split; [exact I|]. split; [exact L|].
        intros a Ha Hw. destruct (cells_hi b a I L Ha) as (A1 & _). exact (HlowH a Hw A1). }
      split; [apply KH; [cbn; lia | numconst; lia | cbn; numconst; lia | exact VH0]|].
      split; [apply KH; [cbn; lia | numconst; lia | cbn; numconst; lia | exact VH8]|].
      split; [apply KH; [cbn; lia | numconst; lia | cbn; numconst; lia | exact VH16]|].
      split; [exact VLB2|].
      split; [apply KH; [numconst; lia | lia | cbn; numconst; lia | exact VT0]|].
      split; [apply KH; [numconst; lia | lia | cbn; numconst; lia | exact VT8]|].
      split; [apply KH; [numconst; lia | lia | cbn; numconst; lia | exact VT16]|].
      split; [apply KH; [numconst; lia | lia | cbn; numconst; lia | exact VT24]|].
      split; [apply KH; [numconst; lia | numconst; lia | cbn; numconst; lia | exact VRA]|].
      split; [apply KL; [intros b Hb; apply in_or_app; left; exact Hb | exact VL]|].
      apply KL; [intros b Hb; apply in_or_app; right; exact Hb | exact VX].
    + exists (pre ++ [nx]). rewrite HPre, <- app_assoc. reflexivity.
    + intros regs' mem' mat' Ec'. rewrite Ec2 in Ec'. destruct (cfgH_inj regs2 mem2 mat2 regs' mem' mat' Ec') as [_ <-].
      apply (PRES_keep DMseg_mbh.WIN mem mem2 HdH PRm MQ). intros a Ha Hh. exfalso. exact (HlowH a Ha Hh). }
destruct (zl (b_items nx) =? 0) eqn:Enc.
{ exfalso. apply Z.eqb_eq in Enc. unfold zl in Enc. lia. }

assert (Lcn : (length (b_items cur) + length (b_items nx) <= 1021)%nat) by (apply Z.ltb_ge in Ecm; unfold zl in Ecm; lia).
assert (CMt : can_merge cur nx = true) by (unfold can_merge, kBatchSlots; apply Nat.leb_le; lia).
destruct HPH as (EW2 & regs3 & mem3 & mat3 & Ec3 & Q2 & QS & Q10 & Q12 & Q15 & Q14 & Q5 & Q6 & Q13 & Q7 & Q28 & Q29 & MQ3 & VLB3).
subst W2 c2.
destruct (g_self W ly regs0 mem0 iw L0 HP cur Icur) as (C1 & C2 & C3 & C4).
destruct (g_self W ly regs0 mem0 iw L0 HP nx Inx) as (X1 & X2 & X3 & X4).
pose proof (g_apart W ly regs0 mem0 iw L0 HP cur nx Icur Inx Ne) as AP.
hide C4. hide X4. hide AP.
pose proof (zl_nonneg ex) as ZEX.
assert (KH3 : forall a n v, (a + Z.of_nat n <= A_QUAR + 184 \/ A_QUAR + 192 <= a) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  val_mem tfibsegs (mr mem) a n v -> val_mem tfibsegs (mr mem3) a n v).
{ intros a n v Ho H1 H2 HV. apply (vm_keepP DMseg_mbh.WIN mem mem3 a n v MQ3); [|exact H1|exact H2|exact HV].
  intros i Hi. unfold DMseg_mbh.WIN. lia. }
assert (PR3 : PRES mem3) by (apply (PRES_keep DMseg_mbh.WIN mem mem3 HdH PRm MQ3); intros a Ha Hh; exfalso; exact (HlowH a Ha Hh)).
assert (IWn : forall k, In k (b_items nx) -> 0 <= iw k < 2 ^ 64).
{ intros k Hk. apply (mb_iw _ _ _ _ _ _ HP). apply (lf_items _ nx k HIT); [apply in_or_app; right; right; left; reflexivity | exact Hk]. }
pose proof VC as VC'. pose proof VN as VN'.
destruct VC' as (VC0 & VC8 & VC16 & VCs). destruct VN' as (VN0 & VN8 & VN16 & VNs).
assert (VS3 : forall j k, nth_error (b_items nx) j = Some k ->
  val_mem tfibsegs (mr mem3) (addrb ly nx + 24 + 8 * Z.of_nat j) 8 (iw k)).
{ intros j k Hk. assert ((j < length (b_items nx))%nat) by (apply nth_error_Some; rewrite Hk; discriminate).
  apply KH3; [numconst; lia | numconst; lia | cbn; unfold kBatchBytes in *; numconst; lia | exact (VNs j k Hk)]. }
eapply SRr_bind.
{ exact (copy_loop regs3 mem3 mat3 cur nx Icur Inx Ne Lcn Ln1 IWn Q7 Q28 Q29 VS3 PR3). }
intros W4 c4 _ (EW4 & regs4 & mem4 & mat4 & Ec4 & RS4 & FR4 & CP4 & PR4). subst W4 c4.

assert (T2 : getr regs4 2 = w64 (spr - 16)) by (rewrite (RS4 2%bv) by inS; rewrite Q2; exact R2).
assert (Usp4 : bv_unsigned (getr regs4 2) = spr - 16) by (rewrite T2; unfold w64; apply unsigned_lit_small; numconst; lia).
assert (T10 : getr regs4 10 = w64 (A_QUAR + 160)) by (rewrite (RS4 10%bv) by inS; exact Q10).
assert (T11 : getr regs4 11 = w64 spr) by (rewrite (RS4 11%bv) by inS; rewrite (QS 11%bv) by inS; exact R11).
assert (T12 : getr regs4 12 = w64 (kBatchBytes * zl ex)) by (rewrite (RS4 12%bv) by inS; exact Q12).
assert (T13 : getr regs4 13 = w64 (b_bytes cur)) by (rewrite (RS4 13%bv) by inS; exact Q13).
assert (T14 : getr regs4 14 = w64 (addrb ly cur)) by (rewrite (RS4 14%bv) by inS; exact Q14).
assert (T5 : getr regs4 5 = w64 (addrb ly nx)) by (rewrite (RS4 5%bv) by inS; exact Q5).
assert (T6 : getr regs4 6 = w64 (zl (b_items cur) + zl (b_items nx))) by (rewrite (RS4 6%bv) by inS; exact Q6).
assert (T15 : getr regs4 15 = w64 kBatchSlots) by (rewrite (RS4 15%bv) by inS; exact Q15).
assert (T16 : getr regs4 16 = w64 18446744073709543424) by (rewrite (RS4 16%bv) by inS; rewrite (QS 16%bv) by inS; exact R16).
assert (T17 : getr regs4 17 = w64 kBatchBytes) by (rewrite (RS4 17%bv) by inS; rewrite (QS 17%bv) by inS; exact R17).

assert (CWo : forall a, CWw cur (zl (b_items nx)) a -> addrb ly cur + 24 <= a < addrb ly cur + kBatchBytes).
{ intros a Ha. unfold CWw, zl in *. unfold kBatchBytes. lia. }
assert (K4 : forall a n v, (a + Z.of_nat n <= A_QUAR + 184 \/ A_QUAR + 192 <= a) ->
  (forall i, 0 <= i < Z.of_nat n -> ~ CWw cur (zl (b_items nx)) (a + i)) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  val_mem tfibsegs (mr mem) a n v -> val_mem tfibsegs (mr mem4) a n v).
{ intros a n v Ho Hc H1 H2 HV. apply (vm_keepP (CWw cur (zl (b_items nx))) mem3 mem4 a n v FR4 Hc H1 H2). exact (KH3 a n v Ho H1 H2 HV). }
assert (VRA4 : val_mem tfibsegs (mr mem4) (spr - 8) 8 0x34418).
{ apply K4; [numconst; lia | intros i Hi Hw; apply CWo in Hw; cbn in Hi; unfold HIDE, kBatchBytes in *; lia | numconst; lia | cbn; numconst; lia | exact VRA]. }
assert (VT04 : val_mem tfibsegs (mr mem4) spr 8 (zl ex)).
{ apply K4; [numconst; lia | intros i Hi Hw; apply CWo in Hw; cbn in Hi; unfold HIDE, kBatchBytes in *; lia | numconst; lia | cbn; numconst; lia | exact VT0]. }
assert (VT84 : val_mem tfibsegs (mr mem4) (spr + 8) 8 (fa ly ex 0)).
{ apply K4; [numconst; lia | intros i Hi Hw; apply CWo in Hw; cbn in Hi; unfold HIDE, kBatchBytes in *; lia | numconst; lia | cbn; numconst; lia | exact VT8]. }
assert (VT164 : val_mem tfibsegs (mr mem4) (spr + 16) 8 (la ly ex)).
{ apply K4; [numconst; lia | intros i Hi Hw; apply CWo in Hw; cbn in Hi; unfold HIDE, kBatchBytes in *; lia | numconst; lia | cbn; numconst; lia | exact VT16]. }
assert (VT244 : val_mem tfibsegs (mr mem4) (spr + 24) 8 (kBatchBytes * zl ex)).
{ apply K4; [numconst; lia | intros i Hi Hw; apply CWo in Hw; cbn in Hi; unfold HIDE, kBatchBytes in *; lia | numconst; lia | cbn; numconst; lia | exact VT24]. }
assert (VH04 : val_mem tfibsegs (mr mem4) (A_QUAR + 160) 8 (zl (done ++ cur :: nx :: t))).
{ apply K4; [cbn; lia | intros i Hi Hw; apply CWo in Hw; cbn in Hi; numconst; lia | numconst; lia | cbn; numconst; lia | exact VH0]. }
assert (VH164 : val_mem tfibsegs (mr mem4) (A_QUAR + 176) 8 (la ly (done ++ cur :: nx :: t))).
{ apply K4; [cbn; lia | intros i Hi Hw; apply CWo in Hw; cbn in Hi; numconst; lia | numconst; lia | cbn; numconst; lia | exact VH16]. }
assert (VLB4 : val_mem tfibsegs (mr mem4) (A_QUAR + 184) 8 (sum_bytes L0)).
{ apply (vm_keepP (CWw cur (zl (b_items nx))) mem3 mem4 _ 8 _ FR4); [| numconst; lia | cbn; numconst; lia | exact VLB3].
  intros i Hi Hw. apply CWo in Hw. cbn in Hi. numconst. lia. }
assert (VN04 : val_mem tfibsegs (mr mem4) (addrb ly nx) 8 (fa ly t 0)).
{ apply K4; [numconst; lia | intros i Hi Hw; apply CWo in Hw; cbn in Hi; unfold HIDE, kBatchBytes in *; lia | numconst; lia | cbn; numconst; lia | exact VN0]. }
assert (VN84 : val_mem tfibsegs (mr mem4) (addrb ly nx + 8) 8 (b_bytes nx)).
{ apply K4; [numconst; lia | intros i Hi Hw; apply CWo in Hw; cbn in Hi; unfold HIDE, kBatchBytes in *; lia | numconst; lia | cbn; numconst; lia | exact VN8]. }
assert (PS4 : forall a, spr <= a < spr + 32 -> apresent (w_H W) mem4 a) by (intros a Ha; apply PR4; left; lia).
assert (PC4 : forall a, addrb ly cur <= a < addrb ly cur + 24 -> apresent (w_H W) mem4 a).
{ intros a Ha. apply PR4. right. exists cur. split; [exact Icur|]. unfold bobj_of, kBatchBytes. lia. }
assert (PN4 : forall a, addrb ly nx <= a < addrb ly nx + 24 -> apresent (w_H W) mem4 a).
{ intros a Ha. apply PR4. right. exists nx. split; [exact Inx|]. unfold bobj_of, kBatchBytes. lia. }

assert (HND' : List.NoDup (map b_self ((done ++ cur :: nx :: t) ++ ex))) by (rewrite <- app_assoc; exact HND).
assert (DS : forall l1 l2 x y, (done ++ cur :: nx :: t) ++ ex = l1 ++ l2 -> In x l1 -> In y l2 -> b_self x <> b_self y).
{ intros l1 l2 x y E Hx Hy. apply (nd_sep b_self l1 l2); [rewrite <- E; exact HND' | exact Hx | exact Hy]. }
assert (LAc : la ly (done ++ cur :: nx :: t) = la ly (nx :: t)) by (rewrite la_app_cons; exact (la_app_cons ly [cur] nx t)).
destruct (la_in (nx :: t) ltac:(discriminate)) as (bL & HbL & ELL).
assert (IbL : inL bL) by (apply HS; apply in_or_app; right; right; exact HbL).
destruct (g_self W ly regs0 mem0 iw L0 HP bL IbL) as (LL1 & LL2 & LL3 & _).
assert (GL2 : 0 <= la ly (done ++ cur :: nx :: t) < ASAN_CEIL) by (rewrite LAc, ELL; numconst; lia).
assert (GL3 : la ly (done ++ cur :: nx :: t) mod 8192 = 0) by (rewrite LAc, ELL; exact LL3).
assert (ZLc : 2 <= zl (done ++ cur :: nx :: t)) by (rewrite zl_app, !zl_cons; pose proof (zl_nonneg done); pose proof (zl_nonneg t); lia).
assert (EXf : 0 <= fa ly ex 0 < ASAN_CEIL).
{ destruct ex as [|e0 ex0]; [cbn; numconst; lia|].
  destruct (HE e0 (or_introl eq_refl)) as [I0 _]. destruct (g_self W ly regs0 mem0 iw L0 HP e0 I0) as (E1 & E2 & _).
  cbn [fa]. numconst. lia. }
assert (EXT : zl ex <> 0 -> exists bl, In bl ex /\ la ly ex = addrb ly bl).
{ intros Hz. apply la_in. intros E. rewrite E in Hz. apply Hz. reflexivity. }
assert (EXl : 0 <= la ly ex < ASAN_CEIL /\ la ly ex mod 8192 = 0).
{ destruct (Z.eq_dec (zl ex) 0) as [Hz|Hz].
  - destruct ex as [|e0 ex0]; [cbn; numconst; lia|]. unfold zl in Hz. cbn [length] in Hz. lia.
  - destruct (EXT Hz) as (bl & Hbl & E). destruct (HE bl Hbl) as [Ibl _].
    destruct (g_self W ly regs0 mem0 iw L0 HP bl Ibl) as (E1 & E2 & E3 & _). rewrite E. split; [numconst; lia | exact E3]. }
destruct EXl as (EXl1 & EXl2).
assert (TL : zl ex <> 0 -> kHighMemBeg <= la ly ex /\ la ly ex + kBatchBytes <= ASAN_CEIL /\
    (la ly ex + 8 <= addrb ly cur \/ addrb ly cur + 24 <= la ly ex) /\ (la ly ex + 8 <= addrb ly nx \/ addrb ly nx + 24 <= la ly ex) /\
    (la ly ex + 8 <= spr - 16 \/ spr + 32 <= la ly ex) /\ (forall a, la ly ex <= a < la ly ex + 8 -> apresent (w_H W) mem4 a)).
{ intros Hz. destruct (EXT Hz) as (bl & Hbl & E). destruct (HE bl Hbl) as [Ibl Ebl].
  destruct (g_self W ly regs0 mem0 iw L0 HP bl Ibl) as (E1 & E2 & E3 & E4).
  assert (N1 : b_self cur <> b_self bl).
  { apply (DS (done ++ [cur]) (nx :: t ++ ex)); [rewrite <- !app_assoc; reflexivity | apply in_or_app; right; left; reflexivity | right; apply in_or_app; right; exact Hbl]. }
  assert (N2 : b_self nx <> b_self bl).
  { apply (DS (done ++ [cur; nx]) (t ++ ex)); [rewrite <- !app_assoc; reflexivity | apply in_or_app; right; right; left; reflexivity | apply in_or_app; right; exact Hbl]. }
  pose proof (g_apart W ly regs0 mem0 iw L0 HP cur bl Icur Ibl N1). pose proof (g_apart W ly regs0 mem0 iw L0 HP nx bl Inx Ibl N2).
  rewrite E. split; [exact E1|]. split; [exact E2|]. split; [unfold kBatchBytes in *; lia|]. split; [unfold kBatchBytes in *; lia|].
  split; [unfold kBatchBytes in *; lia|].
  intros a Ha. apply PR4. right. exists bl. split; [exact Ibl|]. unfold bobj_of, kBatchBytes. lia. }
assert (TLd : zl ex = 0 \/ (kHighMemBeg <= la ly ex /\ la ly ex + kBatchBytes <= ASAN_CEIL /\
    (la ly ex + kBatchBytes <= addrb ly cur \/ addrb ly cur + kBatchBytes <= la ly ex) /\
    (la ly ex + kBatchBytes <= addrb ly nx \/ addrb ly nx + kBatchBytes <= la ly ex) /\
    (la ly ex + 8 <= spr - 16 \/ spr + 32 <= la ly ex))).
{ destruct (Z.eq_dec (zl ex) 0) as [Hz|Hz]; [left; exact Hz|right].
  destruct (EXT Hz) as (bl & Hbl & E). destruct (HE bl Hbl) as [Ibl Ebl].
  destruct (g_self W ly regs0 mem0 iw L0 HP bl Ibl) as (E1 & E2 & E3 & E4).
  assert (N1 : b_self cur <> b_self bl).
  { apply (DS (done ++ [cur]) (nx :: t ++ ex)); [rewrite <- !app_assoc; reflexivity | apply in_or_app; right; left; reflexivity | right; apply in_or_app; right; exact Hbl]. }
  assert (N2 : b_self nx <> b_self bl).
  { apply (DS (done ++ [cur; nx]) (t ++ ex)); [rewrite <- !app_assoc; reflexivity | apply in_or_app; right; right; left; reflexivity | apply in_or_app; right; exact Hbl]. }
  pose proof (g_apart W ly regs0 mem0 iw L0 HP cur bl Icur Ibl N1). pose proof (g_apart W ly regs0 mem0 iw L0 HP nx bl Inx Ibl N2).
  rewrite E. unfold kBatchBytes in *. lia. }
hide TLd.
assert (F_CX : addrb ly cur + 24 <= addrb ly nx \/ addrb ly nx + 24 <= addrb ly cur)
  by (unfold HIDE in AP; clear - AP; unfold kBatchBytes in *; lia).
assert (F_CS : addrb ly cur + 24 <= spr - 16 \/ spr + 32 <= addrb ly cur)
  by (unfold HIDE in C4; clear - C4; unfold kBatchBytes in *; lia).
assert (F_XS : addrb ly nx + 24 <= spr - 16 \/ spr + 32 <= addrb ly nx)
  by (unfold HIDE in X4; clear - X4; unfold kBatchBytes in *; lia).
assert (F_K1 : 0 <= zl (b_items cur) + zl (b_items nx) <= kBatchSlots) by (clear - Lcn; unfold zl, kBatchSlots; lia).
assert (F_L1 : 1 <= zl (done ++ cur :: nx :: t) <= 2 ^ 40) by (clear - ZLc BT SB ZEX; unfold kBatchBytes in *; lia).
assert (F_T1 : 0 <= zl ex < 2 ^ 40) by (clear - ZLc BT SB ZEX; unfold kBatchBytes in *; lia).
assert (F_B1 : 0 <= kBatchBytes * zl ex <= 2 ^ 40) by (clear - ZLc BT SB ZEX; unfold kBatchBytes in *; lia).
assert (F_B2 : 0 <= kBatchBytes * zl ex) by (clear - ZEX; unfold kBatchBytes; lia).
assert (F_B3 : kBatchBytes * zl ex + kBatchBytes <= sum_bytes L0 <= 2 ^ 40) by (clear - ZLc BT SB ZEX; unfold kBatchBytes in *; lia).
assert (FT : DMseg_mbt.free_hyps W regs4 mem4 (addrb ly cur) (addrb ly nx) (b_bytes cur) (b_bytes nx) (fa ly t 0)
    (zl (b_items cur) + zl (b_items nx)) (zl (done ++ cur :: nx :: t)) (la ly (done ++ cur :: nx :: t)) (zl ex) (fa ly ex 0) (la ly ex)
    (kBatchBytes * zl ex) (kBatchBytes * zl ex) (sum_bytes L0)).
{ apply t_FH; assumption. }
eapply SRr_bind; [exact (DMseg_mbt.segT W regs4 mem4 md0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat4 FT)|].
intros W5 c5 _ HT. unfold DMseg_mbt.postT in HT.

pose (WALL := fun a => DMseg_mbh.WIN a \/ CWw cur (zl (b_items nx)) a \/
  DMseg_mbt.WIN regs4 (addrb ly cur) (addrb ly nx) (zl ex) (la ly ex) a).
assert (AW : forall b a, In b ((done ++ cur :: nx :: t) ++ ex) -> b_self b <> b_self cur -> b_self b <> b_self nx ->
  (zl ex <> 0 -> addrb ly b <> la ly ex) -> bcells_of ly b a -> ~ WALL a).
{ intros b a Hb N1 N2 N3 Hc HW. destruct (HBall b Hb) as [Ib Lb]. pose proof (g_cells ly b a Lb Hc) as GC.
  destruct (g_self W ly regs0 mem0 iw L0 HP b Ib) as (B1 & B2 & B3 & B4).
  pose proof (g_apart W ly regs0 mem0 iw L0 HP b cur Ib Icur N1) as A1.
  pose proof (g_apart W ly regs0 mem0 iw L0 HP b nx Ib Inx N2) as A2.
  assert (A3 : zl ex = 0 \/ la ly ex + 8 <= addrb ly b \/ addrb ly b + 8192 <= la ly ex).
  { destruct (Z.eq_dec (zl ex) 0) as [Hz|Hz]; [left; exact Hz|right]. specialize (N3 Hz). lia. }
  unfold WALL, DMseg_mbh.WIN, CWw, DMseg_mbt.WIN, DMseg_mbt.WINF, DMseg_mbt.WINA in HW. rewrite Usp4 in HW.
  clear - HW GC B1 B2 B4 A1 A2 A3 Lcn. unfold zl, kBatchBytes in *. numconst. lia. }
assert (InT : forall b, In b t -> In b ((done ++ cur :: nx :: t) ++ ex))
  by (intros b Hb; apply in_or_app; left; apply in_or_app; right; right; right; exact Hb).
assert (DD : forall b, In b done -> b_self b <> b_self cur /\ b_self b <> b_self nx /\ (zl ex <> 0 -> addrb ly b <> la ly ex)).
{ intros b Hb. split; [|split].
  - apply (DS done (cur :: nx :: t ++ ex)); [rewrite <- app_assoc; reflexivity | exact Hb | left; reflexivity].
  - apply (DS done (cur :: nx :: t ++ ex)); [rewrite <- app_assoc; reflexivity | exact Hb | right; left; reflexivity].
  - intros Hz. destruct (EXT Hz) as (bl & Hbl & E). rewrite E. unfold addrb. intros X.
    apply (DS done (cur :: nx :: t ++ ex) b bl); [rewrite <- app_assoc; reflexivity | exact Hb | right; right; apply in_or_app; right; exact Hbl | lia]. }
assert (DT : forall b, In b t -> b_self b <> b_self cur /\ b_self b <> b_self nx /\ (zl ex <> 0 -> addrb ly b <> la ly ex)).
{ intros b Hb. split; [|split].
  - intros X. apply (DS (done ++ [cur]) (nx :: t ++ ex) cur b); [rewrite <- !app_assoc; reflexivity | apply in_or_app; right; left; reflexivity | right; apply in_or_app; left; exact Hb | symmetry; exact X].
  - intros X. apply (DS (done ++ [cur; nx]) (t ++ ex) nx b); [rewrite <- !app_assoc; reflexivity | apply in_or_app; right; right; left; reflexivity | apply in_or_app; left; exact Hb | symmetry; exact X].
  - intros Hz. destruct (EXT Hz) as (bl & Hbl & E). rewrite E. unfold addrb. intros X.
    apply (DS (done ++ cur :: nx :: t) ex b bl); [reflexivity | apply in_or_app; right; right; right; exact Hb | exact Hbl | lia]. }
assert (HBnew : forall b, In b ((done ++ mergeb cur nx :: t) ++ ex ++ [emptyb nx]) -> inL b /\ (length (b_items b) <= 1021)%nat).
{ intros b Hb. apply in_app_or in Hb as [Hb|Hb].
  - destruct (in_merge done t cur nx b Hb) as [-> | H].
    + split; [exact Icur | cbn [mergeb b_items]; rewrite length_app; exact Lcn].
    + exact (HBall b (in_or_app _ _ _ (or_introl H))).
  - apply in_app_or in Hb as [Hb | [<- | []]].
    + exact (HBall b (in_or_app _ _ _ (or_intror Hb))).
    + split; [exact Inx | cbn; lia]. }
assert (SubO : forall a, mbwin ly regs0 L0 (done ++ cur :: nx :: t) ex a ->
  mbwin ly regs0 L0 (done ++ mergeb cur nx :: t) (ex ++ [emptyb nx]) a).
{ intros a [H|[H|(b & Hb & Hc)]]; [left; exact H | right; left; exact H|]. right; right.
  apply in_app_or in Hb as [Hb|Hb]; [exists b; split; [apply in_or_app; left; exact Hb | exact Hc]|].
  apply in_app_or in Hb as [Hb|Hb].
  - apply in_app_or in Hb as [Hb|[<-|[<-|Hb]]].
    + exists b. split; [apply in_or_app; right; apply in_or_app; left; apply in_or_app; left; exact Hb | exact Hc].
    + exists (mergeb cur nx). split; [apply in_or_app; right; apply in_or_app; left; apply in_or_app; right; left; reflexivity|].
      unfold bcells_of in Hc |- *. change (addrb ly (mergeb cur nx)) with (addrb ly cur).
      change (b_items (mergeb cur nx)) with (b_items cur ++ b_items nx). rewrite zl_app. pose proof (zl_nonneg (b_items nx)). lia.
    + exists nx. split; [apply in_or_app; left; rewrite HPre; apply in_or_app; right; left; reflexivity | exact Hc].
    + exists b. split; [apply in_or_app; right; apply in_or_app; left; apply in_or_app; right; right; exact Hb | exact Hc].
  - exists b. split; [apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb | exact Hc]. }
assert (SubW : forall a, WALL a -> mbwin ly regs0 L0 (done ++ mergeb cur nx :: t) (ex ++ [emptyb nx]) a).
{ intros a HW. unfold WALL, DMseg_mbh.WIN, DMseg_mbt.WIN, DMseg_mbt.WINF, DMseg_mbt.WINA in HW. rewrite Usp4 in HW.
  destruct HW as [HW | [HW | [[HW | [HW | [HW | [HW | HW]]]] | HW]]].
  - right. left. lia.
  - right. right. exists (mergeb cur nx). split; [apply in_or_app; right; apply in_or_app; left; apply in_or_app; right; left; reflexivity|].
    unfold CWw in HW. unfold bcells_of. change (addrb ly (mergeb cur nx)) with (addrb ly cur).
    change (b_items (mergeb cur nx)) with (b_items cur ++ b_items nx). rewrite zl_app. pose proof (zl_nonneg (b_items cur)). lia.
  - left. lia.
  - right. left. lia.
  - right. left. lia.
  - right. right. exists (mergeb cur nx). split; [apply in_or_app; right; apply in_or_app; left; apply in_or_app; right; left; reflexivity|].
    unfold bcells_of. change (addrb ly (mergeb cur nx)) with (addrb ly cur).
    change (b_items (mergeb cur nx)) with (b_items cur ++ b_items nx). pose proof (zl_nonneg (b_items cur ++ b_items nx)). lia.
  - right. right. exists (emptyb nx). split; [apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; left; reflexivity|].
    unfold bcells_of. change (addrb ly (emptyb nx)) with (addrb ly nx). change (zl (b_items (emptyb nx))) with 0. lia.
  - destruct HW as (Hz & HW). destruct (EXT Hz) as (bl & Hbl & E). destruct (HE bl Hbl) as [_ Ebl].
    right. right. exists bl. split; [apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hbl|].
    unfold bcells_of. rewrite Ebl. change (zl (@nil chunk)) with 0. rewrite E in HW. lia. }
assert (TAIL : forall mem5 lb,
  (forall x : word, ~ DMseg_mbt.WIN regs4 (addrb ly cur) (addrb ly nx) (zl ex) (la ly ex) (bv_unsigned x) -> mem5 x = mem4 x) ->
  (forall a, DMseg_mbt.WIN regs4 (addrb ly cur) (addrb ly nx) (zl ex) (la ly ex) a -> kHighMemBeg <= a -> apresent (w_H W) mem5 a) ->
  DMseg_mbt.tail_cells regs4 (addrb ly cur) (addrb ly nx) (b_bytes cur) (b_bytes nx) (fa ly t 0) (zl (b_items cur) + zl (b_items nx))
    (zl (done ++ cur :: nx :: t)) (la ly (done ++ cur :: nx :: t)) (zl ex) (fa ly ex 0) (la ly ex) (kBatchBytes * zl ex) (mr mem5) lb ->
  (forall x : word, ~ mbwin ly regs0 L0 (done ++ mergeb cur nx :: t) (ex ++ [emptyb nx]) (bv_unsigned x) -> mem5 x = mem0 x) /\
  (forall a, mbwin ly regs0 L0 (done ++ mergeb cur nx :: t) (ex ++ [emptyb nx]) a -> kHighMemBeg <= a -> apresent (w_H W) mem5 a) /\
  PRES mem5 /\
  val_mem tfibsegs (mr mem5) (A_QUAR + 160) 8 (zl (done ++ mergeb cur nx :: t)) /\
  val_mem tfibsegs (mr mem5) (A_QUAR + 168) 8 (fa ly L0 0) /\
  val_mem tfibsegs (mr mem5) (A_QUAR + 176) 8 (la ly (done ++ mergeb cur nx :: t)) /\
  val_mem tfibsegs (mr mem5) (A_QUAR + 184) 8 lb /\
  val_mem tfibsegs (mr mem5) spr 8 (zl (ex ++ [emptyb nx])) /\ val_mem tfibsegs (mr mem5) (spr + 8) 8 (fa ly (ex ++ [emptyb nx]) 0) /\
  val_mem tfibsegs (mr mem5) (spr + 16) 8 (la ly (ex ++ [emptyb nx])) /\
  val_mem tfibsegs (mr mem5) (spr + 24) 8 (kBatchBytes * zl (ex ++ [emptyb nx])) /\
  val_mem tfibsegs (mr mem5) (spr - 8) 8 0x34418 /\
  lcn ly iw (mr mem5) (done ++ mergeb cur nx :: t) 0 /\ lcn ly iw (mr mem5) (ex ++ [emptyb nx]) 0 /\
  val_mem tfibsegs (mr mem5) (A_QUAR + 152) 4 257).
{ intros mem5 lb MQ5 PW5 TC.
  unfold DMseg_mbt.tail_cells in TC. rewrite Usp4 in TC.
  destruct TC as (TC1 & TC2 & TC3 & TC4 & TC5 & TC6 & TC7 & TC8 & TC9 & TC10 & TC11 & TC12 & TC13 & TC14).
  assert (FR5 : forall x : word, ~ WALL (bv_unsigned x) -> mem5 x = mem x).
  { intros x Hx. rewrite MQ5 by (intros Hw; apply Hx; right; right; exact Hw).
    rewrite FR4 by (intros Hw; apply Hx; right; left; exact Hw). apply MQ3. intros Hw; apply Hx; left; exact Hw. }
  assert (K5 : forall a n v, (forall i, 0 <= i < Z.of_nat n -> ~ WALL (a + i)) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
    val_mem tfibsegs (mr mem) a n v -> val_mem tfibsegs (mr mem5) a n v).
  { intros a n v Hw H1 H2 HV. exact (vm_keepP WALL mem mem5 a n v FR5 Hw H1 H2 HV). }
  assert (K45 : forall a n v, (forall i, 0 <= i < Z.of_nat n -> ~ DMseg_mbt.WIN regs4 (addrb ly cur) (addrb ly nx) (zl ex) (la ly ex) (a + i)) ->
    0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> val_mem tfibsegs (mr mem4) a n v -> val_mem tfibsegs (mr mem5) a n v).
  { intros a n v Hw H1 H2 HV. exact (vm_keepP _ mem4 mem5 a n v MQ5 Hw H1 H2 HV). }
  assert (HdT : forall a, DMseg_mbt.WIN regs4 (addrb ly cur) (addrb ly nx) (zl ex) (la ly ex) a \/
    ~ DMseg_mbt.WIN regs4 (addrb ly cur) (addrb ly nx) (zl ex) (la ly ex) a).
  { intros a. unfold DMseg_mbt.WIN, DMseg_mbt.WINF, DMseg_mbt.WINA. lia. }
  assert (PR5 : PRES mem5) by exact (PRES_keep _ mem4 mem5 HdT PR4 MQ5 PW5).

  assert (FAR : forall a, (A_QUAR + 152 <= a < A_QUAR + 160 \/ A_QUAR + 168 <= a < A_QUAR + 176 \/ spr - 8 <= a < spr) -> ~ WALL a).
  { intros a Ha HW. unfold WALL, DMseg_mbh.WIN, CWw, DMseg_mbt.WIN, DMseg_mbt.WINF, DMseg_mbt.WINA in HW. rewrite Usp4 in HW.
    clear - Ha HW C1 X1 C4 X4 TLd S1 S2 S4 Lcn. unfold HIDE, zl, kBatchBytes in *. numconst. lia. }
  split.
  { intros x Hx. rewrite FR5 by (intros Hw; apply Hx; apply SubW; exact Hw). apply FR. intros Hw; apply Hx; apply SubO; exact Hw. }
  split.
  { intros a Ha Hh. apply PR5. destruct (mbwin_obj _ _ a HBnew Ha) as [H|[H|H]]; [left; lia | exfalso; numconst; lia | right; exact H]. }
  split; [exact PR5|].
  split. { rewrite zl_merge. exact TC7. }
  split. { apply K5; [intros i Hi; apply FAR; cbn in Hi; lia | numconst; lia | cbn; numconst; lia | exact VH8]. }
  split.
  { assert (ELLn : DMseg_mbt.LLn (addrb ly cur) (addrb ly nx) (la ly (done ++ cur :: nx :: t)) = la ly (done ++ mergeb cur nx :: t)).
    { unfold DMseg_mbt.LLn. rewrite LAc. destruct t as [|n2 t2].
      - change (la ly [nx]) with (addrb ly nx). rewrite Z.eqb_refl. rewrite la_snoc. reflexivity.
      - rewrite la_cons2, la_app_cons, la_cons2.
        destruct (la_in (n2 :: t2) ltac:(discriminate)) as (b & Hb & E). rewrite E.
        destruct (DT b Hb) as (_ & N2 & _). destruct (Z.eqb_spec (addrb ly b) (addrb ly nx)) as [X|_]; [|reflexivity].
        exfalso. apply N2. unfold addrb in X. lia. }
    rewrite <- ELLn. exact TC8. }
  split; [exact TC9|].
  split. { replace (spr - 16 + 16) with spr in TC10 by lia. replace (zl (ex ++ [emptyb nx])) with (zl ex + 1) by (rewrite zl_app; reflexivity). exact TC10. }
  split. { replace (spr - 16 + 24) with (spr + 8) in TC11 by lia. rewrite fa_snoc. exact TC11. }
  split. { replace (spr - 16 + 32) with (spr + 16) in TC12 by lia. rewrite la_snoc. exact TC12. }
  split. { replace (spr - 16 + 40) with (spr + 24) in TC13 by lia.
    replace (kBatchBytes * zl (ex ++ [emptyb nx])) with (kBatchBytes * zl ex + 8192) by (rewrite zl_app; change (zl [emptyb nx]) with 1; unfold kBatchBytes; lia). exact TC13. }
  split. { apply K5; [intros i Hi; apply FAR; cbn in Hi; lia | numconst; lia | cbn; numconst; lia | exact VRA]. }
  split.
  { apply lcn_app. split.
    - apply (lcn_keepP WALL mem mem5 done _ FR5); [|exact VLd].
      intros b Hb. destruct (HBall b (in_or_app _ _ _ (or_introl (in_or_app _ _ _ (or_introl Hb))))) as [I L].
      destruct (DD b Hb) as (N1 & N2 & N3). split; [exact I|]. split; [exact L|].
      intros a Ha. exact (AW b a (in_or_app _ _ _ (or_introl (in_or_app _ _ _ (or_introl Hb)))) N1 N2 N3 Ha).
    - cbn [lcn]. split.
      + unfold bcell. change (addrb ly (mergeb cur nx)) with (addrb ly cur). rewrite b_bytes_merge.
        change (b_items (mergeb cur nx)) with (b_items cur ++ b_items nx).
        split; [exact TC1|]. split; [exact TC2|]. split; [rewrite zl_app; exact TC3|].
        intros j k Hk. destruct (Nat.lt_ge_cases j (length (b_items cur))) as [Hj|Hj].
        * rewrite nth_error_app1 in Hk by exact Hj.
          apply K5; [| numconst; lia | cbn; unfold kBatchBytes in *; numconst; lia | exact (VCs j k Hk)].
          intros i Hi HW. cbn in Hi. unfold WALL, DMseg_mbh.WIN, CWw, DMseg_mbt.WIN, DMseg_mbt.WINF, DMseg_mbt.WINA in HW.
          rewrite Usp4 in HW. pose proof (zl_nonneg (b_items nx)) as ZN0.
          clear - Hi HW Hj Lc C1 C2 C4 X1 AP TLd S1 S2 S4 ZN0. unfold HIDE, zl, kBatchBytes in *. numconst. lia.
        * rewrite nth_error_app2 in Hk by exact Hj. pose proof (CP4 (j - length (b_items cur))%nat k Hk) as V4.
          assert ((j - length (b_items cur) < length (b_items nx))%nat) by (apply nth_error_Some; rewrite Hk; discriminate).
          replace (addrb ly cur + 24 + 8 * (zl (b_items cur) + Z.of_nat (j - length (b_items cur))))
            with (addrb ly cur + 24 + 8 * Z.of_nat j) in V4 by (unfold zl; rewrite Nat2Z.inj_sub by exact Hj; lia).
          apply K45; [| numconst; lia | cbn; unfold kBatchBytes in *; numconst; lia | exact V4].
          intros i Hi HW. cbn in Hi. unfold DMseg_mbt.WIN, DMseg_mbt.WINF, DMseg_mbt.WINA in HW.
          rewrite Usp4 in HW. clear - Hi HW Hj H Lcn C1 C2 C4 X1 AP TLd S1 S2 S4. unfold HIDE, zl, kBatchBytes in *. numconst. lia.
      + apply (lcn_keepP WALL mem mem5 t 0 FR5); [|exact VLt].
        intros b Hb. destruct (HBall b (InT b Hb)) as [I L].
        destruct (DT b Hb) as (N1 & N2 & N3). split; [exact I|]. split; [exact L|].
        intros a Ha. exact (AW b a (InT b Hb) N1 N2 N3 Ha). }
  split.
  { apply lcn_app. split.
    - apply (lcn_relink WALL mem mem5 ex 0 (addrb ly nx) FR5).
      + intros b Hb. exact (HBall b (in_or_app _ _ _ (or_intror Hb))).
      + intros b a Hb Hc HW. destruct (HBall b (in_or_app _ _ _ (or_intror Hb))) as [Ib Lb]. pose proof (g_cells ly b a Lb Hc) as GC.
        destruct (g_self W ly regs0 mem0 iw L0 HP b Ib) as (B1 & B2 & B3 & B4).
        assert (N1 : b_self cur <> b_self b).
        { apply (DS (done ++ [cur]) (nx :: t ++ ex)); [rewrite <- !app_assoc; reflexivity | apply in_or_app; right; left; reflexivity | right; apply in_or_app; right; exact Hb]. }
        assert (N2 : b_self nx <> b_self b).
        { apply (DS (done ++ [cur; nx]) (t ++ ex)); [rewrite <- !app_assoc; reflexivity | apply in_or_app; right; right; left; reflexivity | apply in_or_app; right; exact Hb]. }
        pose proof (g_apart W ly regs0 mem0 iw L0 HP cur b Icur Ib N1) as A1.
        pose proof (g_apart W ly regs0 mem0 iw L0 HP nx b Inx Ib N2) as A2.
        unfold WALL, DMseg_mbh.WIN, CWw, DMseg_mbt.WIN, DMseg_mbt.WINF, DMseg_mbt.WINA in HW. rewrite Usp4 in HW.
        clear - HW GC B1 B2 B4 A1 A2 Lcn. unfold zl, kBatchBytes in *. numconst. lia.
      + intros Hne. assert (Hz : zl ex <> 0) by (destruct ex; [contradiction | unfold zl; cbn [length]; lia]). exact (TC14 Hz).
      + rewrite map_app in HND'. exact (NoDup_app_remove_l _ _ HND').
      + exact VX.
    - cbn [lcn]. split; [|exact I]. unfold bcell. change (addrb ly (emptyb nx)) with (addrb ly nx). rewrite b_bytes_empty.
      change (b_items (emptyb nx)) with (@nil chunk).
      split; [exact TC4|]. split; [exact TC5|]. split; [exact TC6|]. intros j k Hk. destruct j; discriminate Hk. }
  apply (vm_keepP (mbwin ly regs0 L0 (done ++ mergeb cur nx :: t) (ex ++ [emptyb nx])) mem0 mem5 (A_QUAR + 152) 4 257);
    [| | numconst; lia | cbn; numconst; lia | exact (mb_mutex _ _ _ _ _ _ HP)].
  - intros x Hx. rewrite FR5 by (intros Hw; apply Hx; apply SubW; exact Hw). apply FR. intros Hw; apply Hx; apply SubO; exact Hw.
  - intros i Hi Hw. destruct (obj_rng _ (mbwin_obj _ _ _ HBnew Hw)) as (_ & X). cbn in Hi. numconst. lia. }
destruct (fa ly t 0 =? 0) eqn:Ent.
-
  apply Z.eqb_eq in Ent. assert (t = []) by (apply NX3; exact Ent). subst t.
  destruct HT as (EW5 & _ & regs5 & mem5 & mat5 & Ec5 & U2 & U1 & USX & MQ5 & PW5 & TC).
  destruct (TAIL mem5 _ MQ5 PW5 TC) as (F5 & P5 & PR5 & W160 & W168 & W176 & W184 & W0 & W8 & W16 & W24 & WRA & WL & WX & WMX).
  apply SRr_ret. left.
  assert (HMB' : MB L0 = (done ++ [mergeb cur nx], ex ++ [emptyb nx])).
  { rewrite HMB, MB_merge by exact CMt. rewrite MB_one. reflexivity. }
  unfold mb_post. cbv zeta. rewrite fa_MB_L0, HMB'. cbn [fst snd].
  split; [exact EW5|]. exists regs5, mem5, mat5. split; [exact Ec5|].
  split. { rewrite U2, Usp4. unfold w64. f_equal. lia. }
  split; [exact U1|].
  split.
  { intros r Hr. rewrite (USX r Hr).
    rewrite (RS4 r) by (unfold SREGSX in Hr; unfold DMseg_mbc.SREGS; cbn [In] in Hr |- *; tauto).
    rewrite (QS r) by (unfold SREGSX in Hr; unfold DMseg_mbh.SREGS; cbn [In] in Hr |- *; tauto). exact (RS r Hr). }
  split; [exact F5|]. split; [exact P5|].
  split; [exact W160|]. split; [exact W168|]. split; [exact W176|].
  split. { replace (sum_bytes L0 - kBatchBytes * zl (ex ++ [emptyb nx])) with (sum_bytes L0 - (kBatchBytes * zl ex + 8192))
             by (rewrite zl_app; change (zl [emptyb nx]) with 1; unfold kBatchBytes; lia). exact W184. }
  split; [exact W0|]. split; [exact W8|]. split; [exact W16|]. split; [exact W24|].
  split; [exact WMX|]. split; [exact WL|]. exact WX.
-
  apply Z.eqb_neq in Ent. destruct t as [|n2 t2]; [cbn in Ent; contradiction|].
  destruct HT as (EW5 & _ & regs5 & mem5 & mat5 & Ec5 & U2 & US & U10 & U11 & U12 & U15 & U16 & U17 & U14 & U5 & MQ5 & PW5 & TC).
  destruct (TAIL mem5 _ MQ5 PW5 TC) as (F5 & P5 & PR5 & W160 & W168 & W176 & W184 & W0 & W8 & W16 & W24 & WRA & WL & WX & _).
  apply SRr_ret. right. exists (done, mergeb cur nx, n2, t2, ex ++ [emptyb nx]). split; [cbn; lia|].
  unfold LP. cbv beta iota. split; [|split].
  + unfold mb_inv.
    split; [exact EW5|].
    split. { rewrite HMB, MB_merge by exact CMt. cbn [fst snd]. rewrite <- app_assoc. reflexivity. }
    split. { intros b Hb. destruct (in_merge done (n2 :: t2) cur nx b Hb) as [-> | H]; [exact Icur | exact (HS b H)]. }
    split. { intros b Hb. apply in_app_or in Hb as [Hb | [<- | []]]; [exact (HE b Hb) | split; [exact Inx | reflexivity]]. }
    split; [exact (nd_merge done cur nx (n2 :: t2) ex HND)|].
    split.
    { rewrite Forall_forall in HF |- *. intros b Hb. destruct (in_merge done (n2 :: t2) cur nx b Hb) as [-> | H];
        [cbn [mergeb b_items]; rewrite length_app; unfold kBatchSlots; lia | exact (HF b H)]. }
    split; [rewrite fm_merge; exact HIT|].
    split. { rewrite sb_merge, zl_app. change (zl [emptyb nx]) with 1. unfold kBatchBytes in *. lia. }
    exists regs5, mem5, mat5. split; [exact Ec5|].
    split. { rewrite U2. exact T2. }
    split. { rewrite (US 1%bv) by inS. rewrite (RS4 1%bv) by inS. rewrite (QS 1%bv) by inS. exact R1. }
    split.
    { intros r Hr.
      rewrite (US r) by (unfold SREGSX in Hr; unfold DMseg_mbt.SREGS; cbn [In] in Hr |- *; tauto).
      rewrite (RS4 r) by (unfold SREGSX in Hr; unfold DMseg_mbc.SREGS; cbn [In] in Hr |- *; tauto).
      rewrite (QS r) by (unfold SREGSX in Hr; unfold DMseg_mbh.SREGS; cbn [In] in Hr |- *; tauto). exact (RS r Hr). }
    split; [exact U10|].
    split. { rewrite U11, Usp4. unfold w64. f_equal. lia. }
    split. { rewrite U12. unfold w64. f_equal. rewrite zl_app. change (zl [emptyb nx]) with 1. unfold kBatchBytes. lia. }
    split; [exact U14|]. split; [exact U5|]. split; [exact U15|]. split; [exact U16|]. split; [exact U17|].
    split; [exact F5|]. split; [exact P5|].
    cbv zeta.
    split; [exact W160|]. split; [exact W168|]. split; [exact W176|]. split; [exact W184|].
    split; [exact W0|]. split; [exact W8|]. split; [exact W16|]. split; [exact W24|].
    split; [exact WRA|]. split; [exact WL|]. exact WX.
  + exists (pre ++ [nx]). rewrite HPre, <- app_assoc. reflexivity.
  + intros regs' mem' mat' Ec'. rewrite Ec5 in Ec'. destruct (cfgH_inj regs5 mem5 mat5 regs' mem' mat' Ec') as [_ <-]. exact PR5.
Qed.

Theorem loop : forall x W' c', LP x W' c' -> SRr tfibsegs W' c' (mb_post W ly regs0 mem0 md0 iw L0).
Proof.
apply (SRr_loop tfibsegs LS LM LP). exact step.
Qed.

Lemma l_main : forall mat0 : list word,
  SRr tfibsegs W (mkCfg (mkst regs0 (w64 0x34554) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0))
    (mb_post W ly regs0 mem0 md0 iw L0).
Proof.
intros mat0. pose proof (mb_len _ _ _ _ _ _ HP) as HLen.
assert (E : exists b1 b2 t, L0 = b1 :: b2 :: t).
{ clear - HLen. destruct L0 as [|b1 [|b2 t]]; [cbn in HLen; lia | cbn in HLen; lia |]. exists b1, b2, t. reflexivity. }
destruct E as (b1 & b2 & t & EL).
eapply SRr_bind; [eapply DMseg_mbe.segE; eapply ent_FH; [exact HP | exact EL]|].
intros W' c' _ HM. apply (loop ([], b1, b2, t, [])). unfold LP. cbv beta iota.
split; [eapply ent_conv; [exact HP | exact EL | exact HM]|]. split; [exists [b1]; exact EL|].
intros regs' mem' mat' Ec'.
destruct HM as (EW & regs1 & mem1 & mat1 & Ec & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MQ & PR1 & _).
rewrite Ec in Ec'. destruct (cfgH_inj regs1 mem1 mat1 regs' mem' mat' Ec') as [_ <-].
apply (PRES_keep (DMseg_mbe.WIN regs0) mem0 mem1); [| exact PRES_0 | exact MQ | exact PR1].
intros a. unfold DMseg_mbe.WIN. lia.
Qed.
End l.

Theorem mb_ok {fx : YK11.FPState} {rc : YM05.RunCeil} : forall W ly regs0 mem0 md0 mat0 iw L0,
  mb_ok_t W ly regs0 mem0 md0 mat0 iw L0.
Proof.
intros W ly regs0 mem0 md0 mat0 iw L0 HP. exact (l_main W ly regs0 mem0 md0 iw L0 HP mat0).
Qed.
