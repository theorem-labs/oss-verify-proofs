(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v; 64 of its 422 lines of code are new or changed and 670 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require RegisterBridge Regs6ss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import tx_put_c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac br_lits := unfold_cond; rewrite ?unsigned_lit by lia.

Lemma bv_signed_lit : forall z, (0 <= z < 2 ^ 63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. unfold bv_signed. rewrite unsigned_lit by lia. apply bv_swrap_small.
  change (bv_half_modulus 64) with (2 ^ 63)%Z. lia.
Qed.

Lemma bytes_at_munch : forall W m m' a bs,
  bytes_at rsegs m a bs -> munch W m m' -> (bs = [] \/ disjoint_from W a (Z.of_nat (length bs))) ->
  bytes_at rsegs m' a bs.
Proof.
  intros W m m' a bs H MU [E|D].
  - subst bs. pose proof (bytes_at_bound _ _ _ _ H) as HB. cbn [length Z.of_nat] in HB. apply bytes_at_nil. lia.
  - eapply bytes_at_transport; eassumption.
Qed.

Lemma find_segment_some : forall segs a k seg, find_segment segs a k = Some seg ->
  In seg segs /\ (Z.of_N (seg_base seg) <= a /\ a + k <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z.
Proof.
  induction segs as [|sg segs IH]; intros a k seg H; cbn in H; [discriminate|].
  match type of H with context [if ?c then _ else _] => destruct c eqn:E end.
  - inversion H; subst. apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1, E2.
    split; [left; reflexivity | lia].
  - destruct (IH _ _ _ H) as (H1 & H2). split; [right; exact H1 | exact H2].
Qed.

Lemma rsegs_low : forall seg, In seg rsegs -> (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= 2 ^ 40)%Z.
Proof.
  intros seg H.
  assert (E : forallb (fun sg => Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? 2 ^ 40)%Z rsegs = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in E. specialize (E seg H). apply Z.leb_le in E. exact E.
Qed.

Lemma reserve_cover : forall seg a,
  (Z.of_N (seg_base seg) <= a < Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z ->
  (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= 2 ^ 40)%Z ->
  (bv_unsigned (fst (segment_reservation seg)) <= a <
   bv_unsigned (fst (segment_reservation seg)) + bv_unsigned (snd (segment_reservation seg)))%Z.
Proof.
  intros seg a Ha Hs. unfold segment_reservation. cbn [fst snd].
  unfold page_round_down_Z, page_round_up_Z, page_size.
  set (b := Z.of_N (seg_base seg)) in *. set (z := Z.of_N (seg_size seg)) in *.
  assert (Hb : (0 <= b)%Z) by (subst b; lia). assert (Hz : (0 <= z)%Z) by (subst z; lia).
  assert (L1 : (0 <= b / 4096 * 4096 <= b)%Z) by (Z.div_mod_to_equations; lia).
  assert (L2 : (b + z <= (b + z + 4096 - 1) / 4096 * 4096 <= b + z + 4095)%Z)
    by (Z.div_mod_to_equations; lia).
  rewrite !unsigned_lit by lia. lia.
Qed.

Lemma pairwise_in : forall {T : Type} (R : T -> T -> Prop) (l : list T) x y,
  pairwise R l -> In x l -> In y l -> x <> y -> R x y \/ R y x.
Proof.
  intros T R l. induction l as [|h l IH]; intros x y Hp Hx Hy Hne; cbn in *; [contradiction|].
  destruct Hp as [H1 H2].
  destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - contradiction.
  - left. apply H1. exact Hy.
  - right. apply H1. exact Hx.
  - apply IH; assumption.
Qed.

Lemma pairwise_mid : forall {T : Type} (R : T -> T -> Prop) l1 x l2 y,
  pairwise R (l1 ++ x :: l2) -> In y (l1 ++ l2) -> R y x \/ R x y.
Proof.
  intros T R l1. induction l1 as [|h l1 IH]; cbn; intros x l2 y Hp Hy.
  - destruct Hp as [H1 _]. right. apply H1. exact Hy.
  - destruct Hp as [H1 H2]. destruct Hy as [<-|Hy].
    + left. apply H1. apply in_or_app. right. left. reflexivity.
    + eapply IH; eassumption.
Qed.

Lemma ivl_disj : forall s n lo hi, (lo < hi)%Z ->
  (forall i, (0 <= i < n)%Z -> ~ (lo <= s + i < hi)%Z) -> (n = 0 \/ s + n <= lo \/ hi <= s)%Z \/ (n < 0)%Z.
Proof.
  intros s n lo hi Hle H.
  destruct (Z_lt_ge_dec n 0); [right; lia|]. left.
  destruct (Z.eq_dec n 0); [left; exact e|]. right.
  destruct (Z_le_gt_dec (s + n) lo); [left; lia|].
  destruct (Z_le_gt_dec hi s); [right; lia|].
  exfalso. destruct (Z_le_gt_dec s lo).
  - apply (H (lo - s)%Z); lia.
  - apply (H 0%Z); lia.
Qed.

Lemma outside_dec : forall W x, {outside W x} + {~ outside W x}.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn; [left; exact I|].
  destruct (IH x) as [H|H].
  - destruct (Z_le_gt_dec lo x); destruct (Z_lt_ge_dec x hi).
    + right. intros [H1 _]. lia.
    + left. split; [lia | exact H].
    + left. split; [lia | exact H].
    + left. split; [lia | exact H].
  - right. intros [_ H2]. exact (H H2).
Qed.

Lemma vm_id : forall md, md = with_vmmaps (m_vmmaps md) md.
Proof. intros [fd v io fs pr lim tm]. destruct v. reflexivity. Qed.

Lemma with_vmmaps_twice : forall vm1 vm2 md, with_vmmaps vm2 (with_vmmaps vm1 md) = with_vmmaps vm2 md.
Proof. intros vm1 vm2 [fd [h lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma layout_le_trans : forall A A1 L L1 L2,
  layout_le A L L1 -> layout_le A1 L1 L2 -> (length (st_regions A) <= length (st_regions A1))%nat ->
  layout_le A L L2.
Proof.
  intros A A1 L L1 L2 (C1 & S1 & B1 & R1) (C2 & S2 & B2 & R2) HL.
  split; [congruence|]. split; [congruence|]. split; [congruence|].
  intros r Hr. rewrite (R2 r ltac:(lia)). apply R1. exact Hr.
Qed.

Lemma in_other : forall (bl : list (Z * Z)) bl1 bl2 (b0 cap0 : Z) a k,
  In (a, k) bl -> a <> b0 ->
  ((cap0 = 0 /\ bl = bl1 ++ bl2) \/ (cap0 <> 0 /\ bl = bl1 ++ (b0, cap0) :: bl2))%Z -> In (a, k) (bl1 ++ bl2).
Proof.
  intros bl bl1 bl2 b0 cap0 a k Hin Hne [[_ E]|[_ E]]; subst bl; [exact Hin|].
  apply in_app_or in Hin. apply in_or_app. destruct Hin as [H|[H|H]]; [left; exact H | | right; exact H].
  inversion H. congruence.
Qed.

Lemma eqv_final `{fx : FPState} : forall R F pc fc m ro ms',
  Regs6ss.ms_eqv (MS R F pc fc None m ro) ms' -> F = fp_regs -> fc = fp_csr ->
  ms' = YK11.mkst (ms_regs ms') pc m ro /\
  (forall r : reg, is_x0 r = false -> reg_get (ms_regs ms') r = reg_get R r).
Proof.
  intros R F pc fc m ro [r' fr pcv svc rv fcs mm rom] (HR & HF & HP & HS & HV & HC & HM & HRo) EF EC.
  cbn in *. subst. split; [reflexivity|]. intros r Hr. symmetry. apply HR. exact Hr.
Qed.

Ltac getr_val HR :=
  lazymatch goal with
  | |- context [YK11.getr ?X ?k] =>
      change (YK11.getr X k) with (reg_get X k); rewrite HR by reflexivity
  end.

Ltac regs_pres HR :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; unfold callee_saved in Hr;
  assert (Hc : (r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)%Z) by lia;
  repeat destruct Hc as [Hc|Hc]; subst r;
  lazymatch goal with |- YK11.getr ?X ?k = _ => change (YK11.getr X k) with (reg_get X k) end;
  rewrite HR by reflexivity; simp_regs; reflexivity.

Ltac gval HR :=
  lazymatch goal with |- YK11.getr ?X ?k = _ => change (YK11.getr X k) with (reg_get X k) end;
  rewrite HR by reflexivity; simp_regs; reflexivity.

Section KB.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRB : errno_addr B + 4 <= YM05.alloc_ceiling.
Local Open Scope Z_scope.

Lemma find_img : forall a seg, (0 <= a)%Z -> find_segment rsegs a 1 = Some seg -> in_img B a.
Proof.
  intros a seg Ha F. destruct (find_segment_some _ _ _ _ F) as (Hin & H1 & H2). pose proof (rsegs_low _ Hin).
  split. { rewrite SEGS. intros E. rewrite E in Hin. destruct Hin. }
  exists (segment_reservation seg). split.
  - rewrite SEGS. unfold segments_reserved. apply in_map. exact Hin.
  - apply reserve_cover; lia.
Qed.

Lemma present_of_writable : forall m a, (0 <= a < 2 ^ 64)%Z ->
  (YM05.alloc_ceiling <= a \/ ~ in_img B a)%Z -> writable_at (ms_segs B) m a -> present m a.
Proof.
  intros m a Ha Hc W. unfold writable_at, wview in W. unfold present.
  destruct (m (Z_to_bv 64 a)) as [x|] eqn:E; [exists x; reflexivity|]. exfalso.
  rewrite SEGS in W. rewrite unsigned_lit in W by lia.
  destruct (find_segment rsegs a 1) as [seg|] eqn:F; [|apply W; reflexivity].
  destruct Hc as [Hc|Hc].
  - destruct (find_segment_some _ _ _ _ F) as (Hin & _ & H2). pose proof (rsegs_low _ Hin).
    pose proof YM05.alloc_ceiling_value. lia.
  - apply Hc. eapply find_img; [lia | exact F].
Qed.

Lemma writable_of_present : forall m a, present m a -> writable_at (ms_segs B) m a.
Proof. intros m a [x Hx]. unfold writable_at, wview. rewrite Hx. discriminate. Qed.

Lemma rw_of_present : forall m lo k, (0 <= lo)%Z -> (lo + k <= 2 ^ 64)%Z -> (0 <= k)%Z ->
  (forall i, (0 <= i < k)%Z -> present m (lo + i)) -> exists junk, rw_cells rsegs m lo [CB (Z.to_nat k) junk].
Proof.
  intros m lo k Hlo Hhi Hk HP.
  assert (ST : stk rsegs m lo (lo + k)).
  { split; [lia|]. split; [lia|]. intros a Ha. destruct (HP (a - lo)%Z) as [x Hx]; [lia|].
    replace (lo + (a - lo))%Z with a in Hx by lia. unfold wa. split.
    - unfold wview. rewrite Hx. discriminate.
    - exists x. unfold mrd. rewrite Hx. reflexivity. }
  destruct (stk_carve rsegs m lo (lo + k) (Z.to_nat k) ST ltac:(lia)) as [_ [junk H]].
  exists junk. replace (lo + k - Z.of_nat (Z.to_nat k))%Z with lo in H by lia. exact H.
Qed.

Lemma rw_cells_CB1 : forall m a bs, rw_cells rsegs m a [CB 1 bs] -> exists z, rw_cells rsegs m a [C1 z].
Proof.
  intros m a bs [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as [Hl _].
  destruct bs as [|z [|]]; cbn in Hl; try lia. exists z.
  split; [split; [cbn; tauto | exact Hb] | exact Hw].
Qed.

Lemma mbytes_bytes_at : forall m a bs, (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  mbytes B m a bs -> bytes_at rsegs m a bs.
Proof.
  intros m a bs Ha Hl H. unfold mbytes in H. rewrite SEGS in H. split; [lia|]. split; [lia|].
  intros i Hi. specialize (H (Z.of_nat i) ltac:(lia)). rewrite Nat2Z.id in H. exact H.
Qed.

Lemma bytes_at_mbytes : forall m a bs, bytes_at rsegs m a bs -> mbytes B m a bs.
Proof.
  intros m a bs (Ha & Hl & H). unfold mbytes. rewrite SEGS. intros i Hi.
  specialize (H (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in H by lia. exact H.
Qed.

Lemma rw_rec : forall m t b len cap, (0 <= t)%Z -> (t + 24 <= 2 ^ 64)%Z -> text_rec B m t b len cap ->
  (forall i, (0 <= i < 24)%Z -> writable_at (ms_segs B) m (t + i)) ->
  rw_cells rsegs m t [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 cap)].
Proof.
  intros m t b len cap Ht Ht1 [R _] W. split.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    apply mbytes_bytes_at; [lia | rewrite !length_app, !length_le8; cbn; lia | exact R].
  - cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi. rewrite SEGS in W. apply W. lia.
Qed.

Lemma rec_of_rw : forall m t b len cap,
  rw_cells rsegs m t [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 cap)] ->
  (t + 28 <= 2 ^ 64)%Z -> mbytes B m (t + 24) (le4 (Z_to_bv 64 0)) ->
  text_rec B m t b len cap /\ (forall i, (0 <= i < 24)%Z -> writable_at (ms_segs B) m (t + i)).
Proof.
  intros m t b len cap [[_ Hb] (_ & _ & Hw)] T28 FL. split.
  - split; [|split; [exact T28 | exact FL]].
    apply bytes_at_mbytes. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
  - intros i Hi. rewrite SEGS. apply Hw. cbn. lia.
Qed.

Lemma rw_cells_same : forall m m' A cs, rw_cells rsegs m A cs ->
  (forall a, (A <= a < A + Z.of_nat (cells_size cs))%Z ->
     mbyte rsegs m' a = mbyte rsegs m a /\ (writable_at rsegs m a -> writable_at rsegs m' a)) ->
  rw_cells rsegs m' A cs.
Proof.
  intros m m' A cs [[Hwf (Ha & Hl & Hb)] (_ & _ & Hw)] H.
  pose proof (cells_bytes_length cs Hwf) as CL.
  split; [split; [exact Hwf|]|].
  - split; [lia|]. split; [lia|]. intros i Hi.
    destruct (H (A + Z.of_nat i)%Z) as [E _]; [lia|].
    change (mrd rsegs m' (wa (A + Z.of_nat i))) with (mbyte rsegs m' (A + Z.of_nat i)).
    rewrite E. apply Hb. exact Hi.
  - split; [lia|]. split; [lia|]. intros i Hi.
    destruct (H (A + i)%Z) as [_ W]; [lia|]. apply W. apply Hw. exact Hi.
Qed.

Lemma ro_mbyte : forall m a, mem_inv rsegs m -> ro_addr rsegs (Z_to_bv 64 a) = true ->
  mbyte rsegs m a = YK11.seg_rom rsegs (Z_to_bv 64 a).
Proof.
  intros m a MI R. unfold mbyte. destruct (m (Z_to_bv 64 a)) eqn:E; [|reflexivity].
  pose proof (MI _ _ E). congruence.
Qed.

Lemma present_not_ro : forall m a, mem_inv rsegs m -> present m a -> ro_addr rsegs (Z_to_bv 64 a) = false.
Proof. intros m a MI [x Hx]. exact (MI _ _ Hx). Qed.

Lemma in_blocks : forall L A a k, In (a, k) (blocks L A) -> exists p, In (p, k) (user_blocks A) /\ ptr_addr L p = a.
Proof.
  intros L A a k H. unfold blocks in H. apply in_map_iff in H. destruct H as ([p k'] & E & Hin).
  cbn in E. inversion E; subst. exists p. split; [exact Hin | reflexivity].
Qed.

Lemma user_in_blocks : forall L A p k, In (p, k) (user_blocks A) -> In (ptr_addr L p, k) (blocks L A).
Proof. intros L A p k H. unfold blocks. apply in_map_iff. exists (p, k). split; [reflexivity | exact H]. Qed.

Lemma block_facts : forall L A mem md a k i, aa_MR API L A mem md -> In (a, k) (blocks L A) -> (0 <= i < k)%Z ->
  present mem (a + i) /\ (4096 <= a)%Z /\ (a + k <= YM05.alloc_ceiling)%Z /\ ~ owned B L A (a + i).
Proof.
  intros L A mem md a k i MR H Hi. destruct (in_blocks _ _ _ _ H) as (p & Hp & <-).
  exact (mr_blocks _ _ (aa_laws API) _ _ _ _ _ _ _ MR Hp Hi).
Qed.

Lemma block_range : forall L A mem md a k, aa_MR API L A mem md -> In (a, k) (blocks L A) ->
  (4096 <= a)%Z /\ (a + k <= YM05.alloc_ceiling)%Z.
Proof.
  intros L A mem md a k MR H. destruct (in_blocks _ _ _ _ H) as (p & Hp & <-).
  exact (mr_blocks_range _ _ (aa_laws API) _ _ _ _ _ _ MR Hp).
Qed.

Lemma mr_store : forall L A m m' md W, aa_MR API L A m md -> munch W m m' -> wmono rsegs m m' ->
  (forall a, ~ outside W a -> (0 <= a < 2 ^ 64)%Z /\ (YM05.alloc_ceiling <= a \/ ~ in_img B a)%Z) ->
  (forall a, owned B L A a -> outside W a) ->
  aa_MR API L A m' md.
Proof.
  intros L A m m' md W MR MU WM HW HO. pose proof (aa_laws API) as LAWS. pose proof YM05.alloc_ceiling_value as ACV.
  destruct (mr_model _ _ LAWS _ _ _ _ MR) as (Hh & Hl & Hm).
  eapply (mr_frame _ _ LAWS); try eassumption; try reflexivity.
  - intros a Ho. pose proof (mr_owned_low _ _ LAWS _ _ _ _ _ MR Ho). unfold mbyte.
    rewrite (MU (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit by lia. apply HO. exact Ho.
  - intros a Ho [x Hx]. pose proof (mr_owned_low _ _ LAWS _ _ _ _ _ MR Ho). exists x.
    rewrite (MU (Z_to_bv 64 a)); [exact Hx|]. rewrite unsigned_lit by lia. apply HO. exact Ho.
  - intros p k i Hin Hi. destruct (mr_blocks _ _ LAWS _ _ _ _ _ _ _ MR Hin Hi) as (Hp & H4 & Hc & _).
    destruct (outside_dec W (ptr_addr L p + i)) as [Ho|Ho].
    + destruct Hp as [x Hx]. exists x. rewrite (MU (Z_to_bv 64 _)); [exact Hx|]. rewrite unsigned_lit by lia. exact Ho.
    + destruct (HW _ Ho) as [Hr Hc'].
      apply present_of_writable; [exact Hr | exact Hc' |].
      pose proof (writable_of_present _ _ Hp) as Wp. unfold writable_at in *. rewrite SEGS in *. apply WM. exact Wp.
Qed.

Lemma in_img_range : forall a, in_img B a -> (0 <= a < 2 ^ 40)%Z.
Proof.
  intros a [_ (r & Hr & H1)]. rewrite SEGS in Hr.
  assert (E : forallb (fun r => bv_unsigned (fst r) + bv_unsigned (snd r) <=? 2 ^ 40)%Z (segments_reserved rsegs) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in E. specialize (E r Hr). apply Z.leb_le in E.
  pose proof (bv_unsigned_in_range _ (fst r)). lia.
Qed.

Lemma munch_byte : forall W m m' a, munch W m m' -> (0 <= a < 2 ^ 64)%Z -> outside W a ->
  mbyte (ms_segs B) m' a = mbyte (ms_segs B) m a /\ (writable_at (ms_segs B) m a <-> writable_at (ms_segs B) m' a).
Proof.
  intros W m m' a MU Ha Ho.
  assert (E : m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) by (apply MU; rewrite unsigned_lit by lia; exact Ho).
  unfold mbyte, writable_at, wview. rewrite E. tauto.
Qed.

Lemma mbytes_app : forall m a x y, mbytes B m a (x ++ y) <-> mbytes B m a x /\ mbytes B m (a + Z.of_nat (length x)) y.
Proof.
  intros m a x y. unfold mbytes. rewrite length_app. split.
  - intros H. split.
    + intros i Hi. rewrite H by lia. rewrite nth_error_app1 by lia. reflexivity.
    + intros i Hi. replace (a + Z.of_nat (length x) + i)%Z with (a + (Z.of_nat (length x) + i))%Z by lia.
      rewrite H by lia. rewrite nth_error_app2 by lia. f_equal. lia.
  - intros [H1 H2] i Hi. destruct (Z_lt_ge_dec i (Z.of_nat (length x))).
    + rewrite H1 by lia. rewrite nth_error_app1 by lia. reflexivity.
    + replace (a + i)%Z with (a + Z.of_nat (length x) + (i - Z.of_nat (length x)))%Z by lia.
      rewrite H2 by lia. rewrite nth_error_app2 by lia. f_equal. lia.
Qed.

Lemma mbytes_same : forall m m' a bs,
  mbytes B m a bs -> (forall i, (0 <= i < Z.of_nat (length bs))%Z -> mbyte (ms_segs B) m' (a + i) = mbyte (ms_segs B) m (a + i)) ->
  mbytes B m' a bs.
Proof. intros m m' a bs H E i Hi. rewrite E by exact Hi. apply H. exact Hi. Qed.

Lemma ret_ok_pc : forall k, YK0s.ret_ok k -> ret_pc k = k.
Proof.
  intros k H. unfold YK0s.ret_ok in H.
  assert (E : (bv_unsigned k mod 2 = 0)%Z).
  { rewrite <- H. unfold YK14.v_jalr. rewrite Z_to_bv_unsigned. unfold bv_wrap. unfold YK11.jalr_tgtZ.
    set (x := Z.land (bv_unsigned k + 0) (-2)).
    assert (X : (x mod 2 = 0)%Z).
    { replace 2%Z with (2 ^ 1)%Z by reflexivity. rewrite <- Z.land_ones by lia. subst x.
      rewrite <- Z.land_assoc. change (Z.land (-2) (Z.ones 1)) with 0%Z. apply Z.land_0_r. }
    change (bv_modulus 64) with (2 * 2 ^ 63)%Z. rewrite (Z.mod_eq x (2 * 2 ^ 63)) by lia.
    replace (x - 2 * 2 ^ 63 * (x / (2 * 2 ^ 63)))%Z with (x + (- (2 ^ 63 * (x / (2 * 2 ^ 63)))) * 2)%Z by ring.
    rewrite Z_mod_plus_full. exact X. }
  rewrite <- (Z_to_bv_bv_unsigned k). apply ret_pc_even; [| exact E].
  pose proof (bv_unsigned_in_range 64 k) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.

Lemma sr_evt : forall regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] ->
  evt rsegs Q (MS (mkR (YK11.getr regs 1) (YK11.getr regs 2) (YK11.getr regs 3) (YK11.getr regs 4) (YK11.getr regs 5) (YK11.getr regs 6) (YK11.getr regs 7)
          (YK11.getr regs 8) (YK11.getr regs 9) (YK11.getr regs 10) (YK11.getr regs 11) (YK11.getr regs 12) (YK11.getr regs 13) (YK11.getr regs 14)
          (YK11.getr regs 15) (YK11.getr regs 16) (YK11.getr regs 17) (YK11.getr regs 18) (YK11.getr regs 19) (YK11.getr regs 20) (YK11.getr regs 21)
          (YK11.getr regs 22) (YK11.getr regs 23) (YK11.getr regs 24) (YK11.getr regs 25) (YK11.getr regs 26) (YK11.getr regs 27) (YK11.getr regs 28)
          (YK11.getr regs 29) (YK11.getr regs 30) (YK11.getr regs 31)) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall ms', (exists can, Q can /\ Regs6ss.ms_eqv can ms') -> SR (ms_segs B) (mkCfg ms' md) P) ->
  SR (ms_segs B) (mkCfg (YK11.mkst regs pc mem (YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros regs pc mem md Q P Hh Hl HE K. rewrite SEGS in K |- *.
  apply (evt_SR_canon rsegs _ Q md P); [exact HE | exact Hh | exact Hl | exact K].
Qed.

Lemma ro_false : forall a, (0 <= a < 2 ^ 64)%Z -> (YM05.alloc_ceiling <= a \/ ~ in_img B a)%Z ->
  ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha Hc. unfold ro_addr. rewrite unsigned_lit by lia. pose proof YM05.alloc_ceiling_value.
  destruct (find_segment rsegs a 1) as [seg|] eqn:F; [|reflexivity]. exfalso.
  destruct Hc as [Hc|Hc].
  - destruct (find_segment_some _ _ _ _ F) as (Hin & _ & H2). pose proof (rsegs_low _ Hin). lia.
  - apply Hc. eapply find_img; [lia | exact F].
Qed.

Lemma ro_img : forall a, (0 <= a < 2 ^ 64)%Z -> ro_addr rsegs (Z_to_bv 64 a) = true -> in_img B a.
Proof.
  intros a Ha H. unfold ro_addr in H. rewrite unsigned_lit in H by lia.
  destruct (find_segment rsegs a 1) as [seg|] eqn:F; [|discriminate H].
  eapply find_img; [lia | exact F].
Qed.

Lemma rw_cells_norm : forall m A cs, ro_agree rsegs m -> rw_cells rsegs m A cs ->
  (forall i, (0 <= i < Z.of_nat (cells_size cs))%Z -> ro_addr rsegs (wa (A + i)) = false) ->
  rw_cells rsegs (normalize rsegs m) A cs.
Proof.
  intros m A cs RA [[Hwf Hb] Hw] Hro. split; [split; [exact Hwf | apply bytes_at_normalize; assumption] |].
  apply (wr_at_norm rsegs m (normalize rsegs m)); [apply mem_rel_normalize; exact RA | exact Hw | exact Hro].
Qed.

Lemma rw_cells_rel : forall m m0 A cs, mem_rel rsegs m m0 -> rw_cells rsegs m0 A cs -> rw_cells rsegs m A cs.
Proof.
  intros m m0 A cs HR [[Hwf Hb] Hw]. split; [split; [exact Hwf|] |].
  - apply (proj2 (bytes_at_rel rsegs m m0 A _ HR)). exact Hb.
  - apply (wr_at_rel rsegs m m0 A _ HR). exact Hw.
Qed.

Lemma final_n : forall R F pc fc m0 ro can ms',
  ms_rel rsegs can (MS R F pc fc None m0 ro) -> Regs6ss.ms_eqv can ms' -> F = fp_regs -> fc = fp_csr ->
  ms' = YK11.mkst (ms_regs ms') pc (ms_mem ms') ro /\
  (forall r : reg, is_x0 r = false -> reg_get (ms_regs ms') r = reg_get R r) /\
  mem_rel rsegs (ms_mem ms') m0 /\ ms_mem ms' = ms_mem can.
Proof.
  intros R F pc fc m0 ro [r1 f1 p1 v1 s1 c1 m1 o1] [r2 f2 p2 v2 s2 c2 m2 o2]
    (HR & HF & HP & HS & HV & HC & HO & HM) (ER & EF & EP & ES & EV & EC & EM & EO) E1 E2.
  cbn in *. subst. split; [reflexivity|]. split; [|split; [exact HM | reflexivity]].
  intros r Hr. symmetry. apply ER. exact Hr.
Qed.

Lemma wmono_writable : forall m m' a, wmono rsegs m m' -> writable_at (ms_segs B) m a -> writable_at (ms_segs B) m' a.
Proof. intros m m' a WM H. unfold writable_at in *. rewrite SEGS in *. apply WM. exact H. Qed.

Lemma ro_agree_mbyte : forall m a, ro_agree rsegs m -> ro_addr rsegs (Z_to_bv 64 a) = true ->
  mbyte rsegs m a = YK11.seg_rom rsegs (Z_to_bv 64 a).
Proof. intros m a RA H. exact (RA _ H). Qed.

Lemma sr_evt_n : forall regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] -> ro_agree rsegs mem ->
  evt rsegs Q (MS (mkR (YK11.getr regs 1) (YK11.getr regs 2) (YK11.getr regs 3) (YK11.getr regs 4) (YK11.getr regs 5)
          (YK11.getr regs 6) (YK11.getr regs 7) (YK11.getr regs 8) (YK11.getr regs 9) (YK11.getr regs 10)
          (YK11.getr regs 11) (YK11.getr regs 12) (YK11.getr regs 13) (YK11.getr regs 14) (YK11.getr regs 15)
          (YK11.getr regs 16) (YK11.getr regs 17) (YK11.getr regs 18) (YK11.getr regs 19) (YK11.getr regs 20)
          (YK11.getr regs 21) (YK11.getr regs 22) (YK11.getr regs 23) (YK11.getr regs 24) (YK11.getr regs 25)
          (YK11.getr regs 26) (YK11.getr regs 27) (YK11.getr regs 28) (YK11.getr regs 29) (YK11.getr regs 30)
          (YK11.getr regs 31)) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms', (exists can s0, Q s0 /\ ms_rel rsegs can s0 /\ ro_same rsegs mem (ms_mem can) /\ Regs6ss.ms_eqv can ms') ->
     SR (ms_segs B) (mkCfg ms' md) P) ->
  SR (ms_segs B) (mkCfg (YK11.mkst regs pc mem (YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros regs pc mem md Q P Hh Hl RA HE K.
  apply (sr_evt regs pc mem md (fun s => exists s0, Q s0 /\ ms_rel rsegs s s0 /\ ro_same rsegs mem (ms_mem s)) P Hh Hl).
  - apply evt_normalize; [vm_compute; reflexivity | exact RA | exact HE].
  - intros ms' (can & (s0 & HQ & HR & HO) & EQV). apply K. exists can, s0. auto.
Qed.

Lemma call_post_k_mono : forall stk L A regs mem md (E1 E2 : Z -> Prop) L' A' regs' mem' md',
  call_post_k B (aa_MR API) stk L A regs mem md E1 L' A' regs' mem' md' -> (forall a, E1 a -> E2 a) ->
  call_post_k B (aa_MR API) stk L A regs mem md E2 L' A' regs' mem' md'.
Proof.
  intros stk L A regs mem md E1 E2 L' A' regs' mem' md'
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10) HE.
  repeat (split; [eassumption|]). split; [|split; [exact H9 | exact H10]].
  intros a Ha Ho1 Ho2 Hs He. apply H8; auto.
Qed.

Lemma blocks_kept_mono : forall L A mem mem' (g1 g2 : Z -> Prop),
  blocks_kept B L A mem mem' g1 -> (forall a, g1 a -> g2 a) -> blocks_kept B L A mem mem' g2.
Proof.
  unfold blocks_kept. intros L A mem mem' g1 g2 H G a k i Hin Hg Hi.
  apply (H a k i Hin); [intros Hx; apply Hg; apply G; exact Hx | exact Hi].
Qed.

End KB.
