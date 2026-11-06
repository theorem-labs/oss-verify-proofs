(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mret_bind : forall {A B} (x : B) (k : B -> M A) s, (y <- mret x ;; k y) s = k x s.
Proof. reflexivity. Qed.

Lemma tsafe_tbind_assoc : forall {A B C} (t : itree A) (f : A -> M B) (g : B -> M C) P,
  tsafe (tbind t (fun x s => tbind (f x s) g)) P <-> tsafe (tbind (tbind t f) g) P.
Proof.
  intros A B C t f g P. induction t; cbn; try tauto.
  split; intros [H1 H2]; split; try tauto; intros a Ha; apply (H a); apply H2; exact Ha.
Qed.

(* [comment removed for export] *)
Lemma ts_assoc : forall {R B C} (m0 : M B) (f : B -> M C) (g : C -> M R) s P,
  tsafe ((x <- m0 ;; y <- f x ;; g y) s) P -> tsafe ((y <- (x <- m0 ;; f x) ;; g y) s) P.
Proof. intros R B C m0 f g s P H. unfold mbind in *. apply (proj1 (tsafe_tbind_assoc _ _ _ _)). exact H. Qed.

Lemma ts_assoc_inv : forall {R B C} (m0 : M B) (f : B -> M C) (g : C -> M R) s P,
  tsafe ((y <- (x <- m0 ;; f x) ;; g y) s) P -> tsafe ((x <- m0 ;; y <- f x ;; g y) s) P.
Proof. intros R B C m0 f g s P H. unfold mbind in *. apply (proj2 (tsafe_tbind_assoc _ _ _ _)). exact H. Qed.

(* [comment removed for export] *)
Lemma st_zone_spec : forall a n, st_zone a n = true <->
  (bv_unsigned a + n <= IMG_LO \/ IMG_HI <= bv_unsigned a \/
   (ERRNO <= bv_unsigned a /\ bv_unsigned a + n <= ERRNO + 4) \/
   (CTX <= bv_unsigned a /\ bv_unsigned a + n <= CTX_END)).
Proof.
  intros a n. unfold st_zone, ERRNO, CTX, CTX_END, CTX_SIZE.
  rewrite !Bool.orb_true_iff, !Bool.andb_true_iff, !Z.leb_le.
  pose proof (mlo_ctx (ML:=ML)). unfold LOCKA. lia.
Qed.

Lemma upd_lo : forall s m h, ms_lo (upd s m h) = ms_lo s. Proof. reflexivity. Qed.
Lemma upd_hi : forall s m h, ms_hi (upd s m h) = ms_hi s. Proof. reflexivity. Qed.
Lemma upd_mem : forall s m h, ms_mem (upd s m h) = m. Proof. reflexivity. Qed.
Lemma upd_vm : forall s m h, ms_vm (upd s m h) = h. Proof. reflexivity. Qed.
Lemma le_val_u : forall bs, (length bs <= 8)%nat -> bytes_le_to_Z bs = bv_unsigned (le_val bs).
Proof.
  intros bs Hlen. unfold le_val. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
  pose proof (bytes_le_to_Z_bound bs). pose proof (bytes_le_to_Z_nonneg bs). change (bv_modulus 64) with (2^64).
  assert (2 ^ (8 * Z.of_nat (length bs)) <= 2^64) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u_lit : forall z, 0 <= z < 2^64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply Z_to_bv_small_unsigned; lia. Qed.

Lemma at_lit : forall a d, at_ (Z_to_bv 64 a) d = Z_to_bv 64 (a + d).
Proof.
  intros a d. unfold at_. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap. rewrite ?Zmod_mod. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma u_add1_lit : forall a, (Z_to_bv 64 a + 1)%bv = Z_to_bv 64 (a + 1).
Proof.
  intros a. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  change (bv_unsigned (1 : word)) with 1%Z. rewrite bv_wrap64_mod. unfold bv_wrap.
  rewrite ?Zmod_mod. apply Zplus_mod_idemp_l.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mbyte_overlay : forall m x (b : byte), 0 <= x < 2^64 ->
  m (Z_to_bv 64 x) = Some b -> mbyte m x = Some (bv_unsigned b).
Proof. intros m x b Hx Hm. unfold mbyte. cbn [rdn]. rewrite Hm. reflexivity. Qed.

Lemma mbyte_some_rdn1 : forall m x b, mbyte m x = Some b ->
  exists bb : byte, rdn ml_segs m (Z_to_bv 64 x) 1 = Some [bb] /\ bv_unsigned bb = b.
Proof.
  intros m x b H. unfold mbyte in H.
  destruct (rdn ml_segs m (Z_to_bv 64 x) 1) as [[|bb [|]]|] eqn:E; try discriminate.
  exists bb. split; [reflexivity | congruence].
Qed.

(* [comment removed for export] *)
Lemma rdn1_eq : forall m (a : word),
  rdn ml_segs m a 1 = match (match m a with Some b => Some b | None => seg_rom ml_segs a end) with
                    | Some b => Some [b] | None => None end.
Proof. intros m a. cbn [rdn]. destruct (match m a with Some b => Some b | None => seg_rom ml_segs a end); reflexivity. Qed.

Lemma rdn_S_split : forall m (a : word) n,
  rdn ml_segs m a (S n) =
  match rdn ml_segs m a 1 with
  | Some [b] => match rdn ml_segs m (a + 1)%bv n with Some rest => Some (b :: rest) | None => None end
  | _ => None
  end.
Proof.
  intros m a n. cbn [rdn].
  destruct (match m a with Some b => Some b | None => seg_rom ml_segs a end); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rdn_of_mbytes : forall m n a (f : Z -> Z),
  0 <= a -> a + Z.of_nat n <= 2^64 ->
  (forall k, 0 <= k < Z.of_nat n -> mbyte m (a + k) = Some (f k)) ->
  exists bs, rdn ml_segs m (Z_to_bv 64 a) n = Some bs /\ length bs = n /\
             forall k, (k < n)%nat -> bv_unsigned (nth k bs (Z_to_bv 8 0)) = f (Z.of_nat k).
Proof.
  intros m n. induction n as [|n IH]; intros a f Ha Hn Hf.
  - exists []. split; [reflexivity | split; [reflexivity | intros k Hk; lia]].
  - destruct (mbyte_some_rdn1 m a (f 0) (ltac:(replace a with (a + 0) by lia; apply Hf; lia))) as (bb & Hbb & Hu).
    destruct (IH (a + 1) (fun k => f (k + 1))) as (bs & Hbs & Hlen & Hnth); [lia | lia | |].
    { intros k Hk. replace (a + 1 + k) with (a + (k + 1)) by lia. apply Hf. lia. }
    exists (bb :: bs). split; [| split; [cbn; lia |]].
    + rewrite rdn_S_split, Hbb. rewrite u_add1_lit. rewrite Hbs. reflexivity.
    + intros k Hk. destruct k as [|k]; [exact Hu|]. cbn [nth]. rewrite Hnth by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma byte_of_range : forall v k, 0 <= byte_of v k < 256.
Proof. intros v k. unfold byte_of. apply Z.mod_pos_bound. lia. Qed.



Lemma lor_shiftl_8 : forall lo hi, 0 <= lo < 256 -> 0 <= hi ->
  Z.lor lo (Z.shiftl hi 8) = lo + 256 * hi.
Proof.
  intros lo hi Hlo Hhi. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite <- Z.lxor_lor.
  - rewrite <- Z.add_nocarry_lxor. + lia.
    + apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.testbit_0_l.
      destruct (Z.lt_ge_cases i 8) as [H8|H8].
      * rewrite (Z.mul_pow2_bits_low hi 8 i) by lia. apply andb_false_r.
      * rewrite (Z.bits_above_log2 lo i); [reflexivity | lia |].
        destruct (Z.eq_dec lo 0) as [->|Hnz]; [cbn; lia|].
        apply Z.lt_le_trans with 8; [apply Z.log2_lt_pow2; lia | lia].
  - apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.testbit_0_l.
    destruct (Z.lt_ge_cases i 8) as [H8|H8].
    + rewrite (Z.mul_pow2_bits_low hi 8 i) by lia. apply andb_false_r.
    + rewrite (Z.bits_above_log2 lo i); [reflexivity | lia |].
      destruct (Z.eq_dec lo 0) as [->|Hnz]; [cbn; lia|].
      apply Z.lt_le_trans with 8; [apply Z.log2_lt_pow2; lia | lia].
Qed.

Lemma bytes_le_to_Z_of_bytes : forall bs (v : Z), 0 <= v ->
  (forall k, (k < length bs)%nat -> bv_unsigned (nth k bs (Z_to_bv 8 0)) = byte_of v (Z.of_nat k)) ->
  bytes_le_to_Z bs = v mod 2 ^ (8 * Z.of_nat (length bs)).
Proof.
  induction bs as [|b bs IH]; intros v Hv Hk.
  - cbn. rewrite Z.pow_0_r, Z.mod_1_r. reflexivity.
  - cbn [bytes_le_to_Z length].
    rewrite (IH (v / 256)); [| apply Z.div_pos; lia |].
    2:{ intros k Hkk. pose proof (Hk (S k) ltac:(cbn; lia)) as E. cbn [nth] in E. rewrite E.
        unfold byte_of. rewrite Z.div_div by lia.
        replace (8 * Z.of_nat (S k)) with (8 + 8 * Z.of_nat k) by lia.
        rewrite Z.pow_add_r by lia. reflexivity. }
    pose proof (Hk O ltac:(cbn; lia)) as E0. cbn [nth] in E0. rewrite E0.
    unfold byte_of. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r.
    rewrite lor_shiftl_8; [| apply Z.mod_pos_bound; lia | apply Z.mod_pos_bound; lia].
    replace (8 * Z.of_nat (S (length bs))) with (8 + 8 * Z.of_nat (length bs)) by lia.
    rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
    rewrite Z.rem_mul_r by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithRep.
  Variable A : astate.
  Variable m : word -> option byte.
  Hypothesis HR : Rep A m.

  (* [comment removed for export] *)
  Lemma rep_read : forall a (n : nat) v,
    has A (FCT a (Z.of_nat n) v) ->
    0 <= a -> a + Z.of_nat n <= 2^64 -> 0 <= v ->
    exists bs, rdn ml_segs m (Z_to_bv 64 a) n = Some bs /\ length bs = n /\
               bytes_le_to_Z bs = v mod 2 ^ (8 * Z.of_nat n).
  Proof.
    intros a n v Hf Ha Hn Hv.
    destruct (rdn_of_mbytes m n a (fun k => byte_of v k) Ha Hn) as (bs & Hbs & Hlen & Hnth).
    { intros k Hk. apply (rep_facts A m HR). exists (FCT a (Z.of_nat n) v). split; [exact Hf|].
      unfold fbyte. cbn [f_a f_n f_v]. split; [lia|]. f_equal. lia. }
    exists bs. split; [exact Hbs | split; [exact Hlen |]].
    rewrite <- Hlen. apply bytes_le_to_Z_of_bytes; [exact Hv |].
    intros k Hk. rewrite Hnth by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma rep_read_dom : forall a (n : nat),
    (forall k, 0 <= k < Z.of_nat n -> dom A (a + k)) ->
    0 <= a -> a + Z.of_nat n <= 2^64 ->
    exists bs, rdn ml_segs m (Z_to_bv 64 a) n = Some bs /\ length bs = n.
  Proof.
    intros a n Hd Ha Hn.
    assert (Hf : forall k, 0 <= k < Z.of_nat n -> exists b, mbyte m (a + k) = Some b).
    { intros k Hk. destruct (m (Z_to_bv 64 (a + k))) as [bb|] eqn:E.
      - exists (bv_unsigned bb). apply mbyte_overlay; [lia | exact E].
      - exfalso. exact (rep_dom A m HR (a + k) (Hd k Hk) E). }
    (* [comment removed for export] *)
    revert a Hd Ha Hn Hf. induction n as [|n IH]; intros a Hd Ha Hn Hf.
    - exists []. split; reflexivity.
    - destruct (Hf 0 ltac:(lia)) as (b0 & Hb0). rewrite Z.add_0_r in Hb0.
      destruct (mbyte_some_rdn1 m a b0 Hb0) as (bb & Hbb & _).
      destruct (IH (a + 1)) as (bs & Hbs & Hlen); [ | lia | lia | | ].
      { intros k Hk. replace (a + 1 + k) with (a + (k + 1)) by lia. apply Hd. lia. }
      { intros k Hk. replace (a + 1 + k) with (a + (k + 1)) by lia. apply Hf. lia. }
      exists (bb :: bs). split; [| cbn; lia].
      rewrite rdn_S_split, Hbb, u_add1_lit. rewrite Hbs. reflexivity.
  Qed.
End WithRep.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nth_Z_to_le_bytes : forall n z k, 0 <= z -> (k < n)%nat ->
  bv_unsigned (nth k (Z_to_le_bytes n z) (Z_to_bv 8 0)) = byte_of z (Z.of_nat k).
Proof.
  induction n as [|n IH]; intros z k Hz Hk; [lia|].
  cbn [Z_to_le_bytes]. destruct k as [|k].
  - cbn [nth]. rewrite Z_to_bv_unsigned. unfold byte_of. cbn [Z.mul Z.of_nat].
    rewrite Z.pow_0_r, Z.div_1_r. reflexivity.
  - cbn [nth]. rewrite IH; [| apply Z.shiftr_nonneg; lia | lia].
    unfold byte_of. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_div by lia.
    change (2 ^ 8) with 256.
    replace (8 * Z.of_nat (S k)) with (8 + 8 * Z.of_nat k) by lia. rewrite Z.pow_add_r by lia.
    reflexivity.
Qed.

Lemma wbytes_at_in : forall bs m (a : word) (x : word),
  bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
  bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs) ->
  wbytes m a bs x = Some (nth (Z.to_nat (bv_unsigned x - bv_unsigned a)) bs (Z_to_bv 8 0)).
Proof.
  induction bs as [|b bs IH]; intros m a x Hnw Hx; cbn [length] in *; [lia|].
  cbn [wbytes].
  destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq | Hne].
  - assert (x = a) by (apply bv_eq; exact Heq). subst x. rewrite Z.sub_diag. cbn [Z.to_nat nth].
    destruct bs as [|b' bs'].
    + cbn [wbytes]. rewrite bv_eqb_refl. reflexivity.
    + rewrite wbytes_below.
      * rewrite bv_eqb_refl. reflexivity.
      * rewrite u_add1 by (cbn [length] in Hnw; lia). cbn [length] in *. lia.
      * rewrite u_add1 by (cbn [length] in Hnw; lia). lia.
  - assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
    rewrite (IH _ (a + 1)%bv x) by (rewrite Hu1; lia).
    rewrite Hu1. replace (Z.to_nat (bv_unsigned x - bv_unsigned a)) with (S (Z.to_nat (bv_unsigned x - (bv_unsigned a + 1)))) by lia.
    reflexivity.
Qed.

Lemma mbyte_wbytes_in : forall m a bs x,
  0 <= a -> a + Z.of_nat (length bs) <= 2^64 -> a <= x < a + Z.of_nat (length bs) ->
  mbyte (wbytes m (Z_to_bv 64 a) bs) x = Some (bv_unsigned (nth (Z.to_nat (x - a)) bs (Z_to_bv 8 0))).
Proof.
  intros m a bs x Ha Hnw Hx. unfold mbyte. rewrite rdn1_eq.
  rewrite (wbytes_at_in bs m (Z_to_bv 64 a) (Z_to_bv 64 x)) by (rewrite !u_lit by lia; lia).
  rewrite !u_lit by lia. reflexivity.
Qed.

Lemma mbyte_wbytes_out : forall m a bs x,
  0 <= a < 2^64 -> a + Z.of_nat (length bs) <= 2^64 -> 0 <= x < 2^64 -> (x < a \/ a + Z.of_nat (length bs) <= x) ->
  mbyte (wbytes m (Z_to_bv 64 a) bs) x = mbyte m x.
Proof.
  intros m a bs x Ha Hnw Hx Hout. unfold mbyte.
  rewrite rdn_wbytes_out; [reflexivity | | |]; rewrite ?u_lit by lia; cbn [Z.of_nat Pos.of_succ_nat]; lia.
Qed.

(* [comment removed for export] *)
Lemma rep_write : forall A A' m a bs,
  Rep A m -> 0 <= a < 2^64 -> a + Z.of_nat (length bs) <= 2^64 ->
  (forall x b, facts A' x b ->
     (a <= x < a + Z.of_nat (length bs) /\ b = bv_unsigned (nth (Z.to_nat (x - a)) bs (Z_to_bv 8 0))) \/
     ((x < a \/ a + Z.of_nat (length bs) <= x) /\ facts A x b)) ->
  (forall x, dom A' x -> dom A x) ->
  (forall x b, facts A x b -> 0 <= x < 2^64) ->
  Rep A' (wbytes m (Z_to_bv 64 a) bs).
Proof.
  intros A A' m a bs HR Ha Hnw Hf Hd Hrange. constructor.
  - intros x b Hxb. destruct (Hf x b Hxb) as [[Hin ->] | [Hout Hold]].
    + apply mbyte_wbytes_in; lia.
    + rewrite mbyte_wbytes_out; [| lia | lia | | exact Hout].
      * apply (rep_facts A m HR). exact Hold.
      * destruct (Hf x b Hxb) as [[? _]|[_ H2]]; [lia|]. exact (Hrange x b H2).
  - intros x Hx E. apply (rep_dom A m HR x (Hd x Hx)).
    pose proof (u64_range (Z_to_bv 64 x)) as Hxr.
    destruct (Z_lt_le_dec (bv_unsigned (Z_to_bv 64 x)) (bv_unsigned (Z_to_bv 64 a))) as [Hl|Hl].
    + rewrite <- (wbytes_below bs m (Z_to_bv 64 a) (Z_to_bv 64 x)); [exact E | rewrite u_lit by lia; lia | exact Hl].
    + destruct (Z_lt_le_dec (bv_unsigned (Z_to_bv 64 x)) (bv_unsigned (Z_to_bv 64 a) + Z.of_nat (length bs))) as [Hi|Hi].
      * exfalso. rewrite (wbytes_at_in bs m (Z_to_bv 64 a) (Z_to_bv 64 x)) in E; [discriminate | rewrite u_lit by lia; lia | lia].
      * rewrite <- (wbytes_above bs m (Z_to_bv 64 a) (Z_to_bv 64 x)); [exact E | exact Hi].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mbyte_zfill_in : forall m (a n : Z) x,
  0 <= a < 2^64 -> 0 <= n < 2^64 -> a + n <= 2^64 -> a <= x < a + n ->
  mbyte (zfill (Z_to_bv 64 a) (Z_to_bv 64 n) m) x = Some 0.
Proof.
  intros m a n x Ha Hn Han Hx. unfold mbyte. rewrite rdn1_eq. unfold zfill, zmem.
  rewrite !u_lit by lia.
  replace ((a <=? x) && (x <? a + n))%Z with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  reflexivity.
Qed.

Lemma mbyte_zfill_out : forall m (a n : Z) x,
  0 <= a < 2^64 -> 0 <= n < 2^64 -> a + n <= 2^64 -> 0 <= x < 2^64 -> (x < a \/ a + n <= x) ->
  mbyte (zfill (Z_to_bv 64 a) (Z_to_bv 64 n) m) x = mbyte m x.
Proof.
  intros m a n x Ha Hn Han Hx Hout. unfold mbyte. rewrite !rdn1_eq. unfold zfill, zmem.
  rewrite !u_lit by lia.
  replace ((a <=? x) && (x <? a + n))%Z with false; [reflexivity|].
  symmetry. destruct Hout; [apply andb_false_intro1; apply Z.leb_gt; lia | apply andb_false_intro2; apply Z.ltb_ge; lia].
Qed.

Lemma zfill_some : forall m (a n : Z) x,
  0 <= a < 2^64 -> 0 <= n < 2^64 -> a + n <= 2^64 -> 0 <= x < 2^64 ->
  m (Z_to_bv 64 x) <> None -> zfill (Z_to_bv 64 a) (Z_to_bv 64 n) m (Z_to_bv 64 x) <> None.
Proof.
  intros m a n x Ha Hn Han Hx Hm. unfold zfill, zmem. rewrite !u_lit by lia.
  destruct ((a <=? x) && (x <? a + n))%Z; [discriminate | exact Hm].
Qed.

Lemma zfill_some_in : forall m (a n : Z) x,
  0 <= a < 2^64 -> 0 <= n < 2^64 -> a + n <= 2^64 -> a <= x < a + n ->
  zfill (Z_to_bv 64 a) (Z_to_bv 64 n) m (Z_to_bv 64 x) <> None.
Proof.
  intros m a n x Ha Hn Han Hx. unfold zfill, zmem. rewrite !u_lit by lia.
  replace ((a <=? x) && (x <? a + n))%Z with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  discriminate.
Qed.

(* [comment removed for export] *)
Lemma rep_zfill : forall A A' m a n,
  Rep A m -> 0 <= a < 2^64 -> 0 <= n < 2^64 -> a + n <= 2^64 ->
  (forall x b, facts A' x b -> (a <= x < a + n /\ b = 0) \/ ((x < a \/ a + n <= x) /\ facts A x b)) ->
  (forall x, dom A' x -> dom A x \/ a <= x < a + n) ->
  (forall x b, facts A x b -> 0 <= x < 2^64) ->
  (forall x, dom A x -> 0 <= x < 2^64) ->
  Rep A' (zfill (Z_to_bv 64 a) (Z_to_bv 64 n) m).
Proof.
  intros A A' m a n HR Ha Hn Han Hf Hd Hr Hdr. constructor.
  - intros x b Hxb. destruct (Hf x b Hxb) as [[Hin ->] | [Hout Hold]].
    + apply mbyte_zfill_in; lia.
    + rewrite mbyte_zfill_out; [apply (rep_facts A m HR); exact Hold | lia | lia | lia | exact (Hr x b Hold) | exact Hout].
  - intros x Hx. destruct (Hd x Hx) as [Hold | Hin].
    + apply zfill_some; [lia | lia | lia | exact (Hdr x Hold) | exact (rep_dom A m HR x Hold)].
    + apply zfill_some_in; lia.
Qed.

(* [comment removed for export] *)
Lemma rep_unfill : forall A A' m a n,
  Rep A m -> 0 <= a < 2^64 -> 0 <= n < 2^64 -> a + n <= 2^64 ->
  (forall x b, facts A' x b -> (x < a \/ a + n <= x) /\ facts A x b) ->
  (forall x, dom A' x -> (x < a \/ a + n <= x) /\ dom A x) ->
  (forall x b, facts A x b -> 0 <= x < 2^64) ->
  (forall x, dom A x -> 0 <= x < 2^64) ->
  Rep A' (unfill (Z_to_bv 64 a) (Z_to_bv 64 n) m).
Proof.
  intros A A' m a n HR Ha Hn Han Hf Hd Hr Hdr. constructor.
  - intros x b Hxb. destruct (Hf x b Hxb) as [Hout Hold].
    pose proof (Hr x b Hold) as Hx.
    unfold mbyte. rewrite rdn1_eq. unfold unfill. rewrite !u_lit by lia.
    replace ((a <=? x) && (x <? a + n))%Z with false.
    2:{ symmetry. destruct Hout; [apply andb_false_intro1; apply Z.leb_gt; lia | apply andb_false_intro2; apply Z.ltb_ge; lia]. }
    pose proof (rep_facts A m HR x b Hold) as E. unfold mbyte in E. rewrite rdn1_eq in E. exact E.
  - intros x Hx. destruct (Hd x Hx) as [Hout Hold]. pose proof (Hdr x Hold) as Hxr.
    unfold unfill. rewrite !u_lit by lia.
    replace ((a <=? x) && (x <? a + n))%Z with false.
    2:{ symmetry. destruct Hout; [apply andb_false_intro1; apply Z.leb_gt; lia | apply andb_false_intro2; apply Z.ltb_ge; lia]. }
    exact (rep_dom A m HR x Hold).
Qed.

(* [comment removed for export] *)
Lemma rep_restate : forall A A' m,
  Rep A m ->
  (forall x b, facts A' x b -> facts A x b \/ mbyte m x = Some b) ->
  (forall x, dom A' x -> dom A x \/ m (Z_to_bv 64 x) <> None) ->
  Rep A' m.
Proof.
  intros A A' m HR Hf Hd. constructor.
  - intros x b Hxb. destruct (Hf x b Hxb) as [H|H]; [apply (rep_facts A m HR); exact H | exact H].
  - intros x Hx. destruct (Hd x Hx) as [H|H]; [apply (rep_dom A m HR); exact H | exact H].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Steps.
  Context {R : Type}.
  Implicit Types (P : R -> mstate -> Prop) (s : mstate).

  Lemma ts_ret : forall (v : R) s P, P v s -> tsafe (mret v s) P.
  Proof. intros v s P H. exact H. Qed.

  Lemma ts_bind_ret : forall {B} (x : B) (k : B -> M R) s P,
    tsafe (k x s) P -> tsafe ((y <- mret x ;; k y) s) P.
  Proof. intros B x k s P H. exact H. Qed.

  Lemma ts_assert : forall b (k : unit -> M R) s P,
    b = true -> tsafe (k tt s) P -> tsafe ((x <- massert b ;; k x) s) P.
  Proof. intros b k s P -> H. exact H. Qed.

  Lemma ts_rd : forall n a bs (k : list byte -> M R) s P,
    acc_ok s (Z_to_bv 64 a) (Z.of_nat n) = true ->
    rdn ml_segs (ms_mem s) (Z_to_bv 64 a) n = Some bs ->
    tsafe (k bs s) P -> tsafe ((x <- m_rd n (Z_to_bv 64 a) ;; k x) s) P.
  Proof. intros n a bs k s P Hacc Hrd H. unfold mbind, m_rd. rewrite Hacc, Hrd. exact H. Qed.

  Lemma ts_ld : forall a bs (k : word -> M R) s P,
    acc_ok s (Z_to_bv 64 a) 8 = true ->
    rdn ml_segs (ms_mem s) (Z_to_bv 64 a) 8 = Some bs ->
    tsafe (k (le_val bs) s) P -> tsafe ((x <- m_ld (Z_to_bv 64 a) ;; k x) s) P.
  Proof. intros a bs k s P Hacc Hrd H. unfold mbind, m_ld, m_rd, mbind, mret. change (Z.of_nat 8) with 8%Z. rewrite Hacc, Hrd. exact H. Qed.

  Lemma ts_lwu : forall a bs (k : word -> M R) s P,
    acc_ok s (Z_to_bv 64 a) 4 = true ->
    rdn ml_segs (ms_mem s) (Z_to_bv 64 a) 4 = Some bs ->
    tsafe (k (le_val bs) s) P -> tsafe ((x <- m_lwu (Z_to_bv 64 a) ;; k x) s) P.
  Proof. intros a bs k s P Hacc Hrd H. unfold mbind, m_lwu, m_rd, mbind, mret. change (Z.of_nat 4) with 4%Z. rewrite Hacc, Hrd. exact H. Qed.

  Lemma ts_lw : forall a bs (k : word -> M R) s P,
    acc_ok s (Z_to_bv 64 a) 4 = true ->
    rdn ml_segs (ms_mem s) (Z_to_bv 64 a) 4 = Some bs ->
    tsafe (k (v_lw (le_val bs)) s) P -> tsafe ((x <- m_lw (Z_to_bv 64 a) ;; k x) s) P.
  Proof. intros a bs k s P Hacc Hrd H. unfold mbind, m_lw, m_rd, mbind, mret. change (Z.of_nat 4) with 4%Z. rewrite Hacc, Hrd. exact H. Qed.

  Lemma ts_lhu : forall a bs (k : word -> M R) s P,
    acc_ok s (Z_to_bv 64 a) 2 = true ->
    rdn ml_segs (ms_mem s) (Z_to_bv 64 a) 2 = Some bs ->
    tsafe (k (le_val bs) s) P -> tsafe ((x <- m_lhu (Z_to_bv 64 a) ;; k x) s) P.
  Proof. intros a bs k s P Hacc Hrd H. unfold mbind, m_lhu, m_rd, mbind, mret. change (Z.of_nat 2) with 2%Z. rewrite Hacc, Hrd. exact H. Qed.

  Lemma ts_lbu : forall a (b : byte) (k : word -> M R) s P,
    acc_ok s (Z_to_bv 64 a) 1 = true ->
    rdn ml_segs (ms_mem s) (Z_to_bv 64 a) 1 = Some [b] ->
    tsafe (k (Z_to_bv 64 (bv_unsigned b)) s) P -> tsafe ((x <- m_lbu (Z_to_bv 64 a) ;; k x) s) P.
  Proof. intros a b k s P Hacc Hrd H. unfold mbind, m_lbu, m_rd, mbind, mret. change (Z.of_nat 1) with 1%Z. rewrite Hacc, Hrd. exact H. Qed.

  Lemma ts_st : forall n a v (k : unit -> M R) s P,
    acc_ok s (Z_to_bv 64 a) (Z.of_nat n) = true ->
    st_zone (Z_to_bv 64 a) (Z.of_nat n) = true ->
    store_ok ml_segs (ms_mem s) (Z_to_bv 64 a) n = true ->
    tsafe (k tt (upd s (wbytes (ms_mem s) (Z_to_bv 64 a) (word_to_le_bytes n v)) (ms_vm s))) P ->
    tsafe ((x <- m_st n (Z_to_bv 64 a) v ;; k x) s) P.
  Proof. intros n a v k s P Hacc Hz Hso H. unfold mbind, m_st. rewrite Hacc, Hz, Hso. exact H. Qed.
End Steps.

(* [comment removed for export] *)
Lemma acc_ok_below : forall s a n,
  0 <= a -> 0 <= n -> a + n <= ms_lo s -> ms_lo s < 2^64 -> acc_ok s (Z_to_bv 64 a) n = true.
Proof.
  intros s a n Ha Hn Hle Hlo. unfold acc_ok. rewrite u_lit by lia.
  apply Bool.orb_true_iff. left. apply Z.leb_le. lia.
Qed.

Lemma acc_ok_above : forall s a n,
  0 <= a -> 0 < n -> ms_hi s <= a -> a + n <= 2^64 -> acc_ok s (Z_to_bv 64 a) n = true.
Proof.
  intros s a n Ha Hn Hhi Hnw. unfold acc_ok. rewrite u_lit by lia.
  apply Bool.orb_true_iff. right. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ctx_block_rw : RW_LO <= LOCKA /\ CTX_END <= IMG_HI.
Proof. pose proof layout_nums. lia. Qed.

Lemma img_hi_small : IMG_HI <= 2^32.
Proof. pose proof (mlo_hull (ML:=ML)). lia. Qed.

Lemma store_ok_rwseg : forall m x (n : nat),
  RW_LO <= x -> x + Z.of_nat n <= IMG_HI -> store_ok ml_segs m (Z_to_bv 64 x) n = true.
Proof.
  intros m x n Hlo Hhi. pose proof img_hi_small. pose proof (mlo_hull (ML:=ML)).
  apply store_ok_of_all; [rewrite u_lit by lia; lia|].
  intros y Hy. rewrite u_lit in Hy by lia. apply mlo_wview_rw. lia.
Qed.

Lemma store_ok_ctx : forall m x (n : nat),
  LOCKA <= x -> x + Z.of_nat n <= CTX_END -> store_ok ml_segs m (Z_to_bv 64 x) n = true.
Proof. intros m x n Hlo Hhi. pose proof ctx_block_rw. apply store_ok_rwseg; lia. Qed.

Lemma store_ok_dom : forall A m x (n : nat),
  Rep A m -> (forall k, 0 <= k < Z.of_nat n -> dom A (x + k)) ->
  0 <= x < 2^64 -> x + Z.of_nat n <= 2^64 ->
  store_ok ml_segs m (Z_to_bv 64 x) n = true.
Proof.
  intros A m x n HR Hd Hx Hnw.
  apply store_ok_of_all; [rewrite u_lit by lia; lia|].
  intros y Hy. rewrite u_lit in Hy by lia. unfold wview.
  pose proof (rep_dom A m HR (bv_unsigned y) ltac:(replace (bv_unsigned y) with (x + (bv_unsigned y - x)) by lia; apply Hd; lia)) as Hm.
  rewrite Z_to_bv_bv_unsigned in Hm. destruct (m y); [discriminate | exfalso; apply Hm; reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mbyte_ctx_image : forall m x, LOCKA <= x < CTX_END -> m (Z_to_bv 64 x) = None -> mbyte m x = Some 0.
Proof.
  intros m x Hx Hm. pose proof layout_nums.
  unfold mbyte. rewrite rdn1_eq, Hm.
  rewrite (mlo_ctx_zero (Z_to_bv 64 x)); [reflexivity|].
  rewrite u_lit by lia. unfold CTX_END, LOCKA in Hx.
  pose proof (mlo_ctx (ML:=ML)). pose proof (mlo_order_ctx (ML:=ML)). unfold CTX_SIZE in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rep_write_clear : forall A m a bs,
  Rep A m -> 0 <= a < 2^64 -> a + Z.of_nat (length bs) <= 2^64 ->
  (forall f, has A f -> f_a f + f_n f <= a \/ a + Z.of_nat (length bs) <= f_a f) ->
  (forall x b, facts A x b -> 0 <= x < 2^64) ->
  Rep A (wbytes m (Z_to_bv 64 a) bs).
Proof.
  intros A m a bs HR Ha Hnw Hclear Hr.
  apply (rep_write A A m a bs HR Ha Hnw); [| intros x Hx; exact Hx | exact Hr].
  intros x b (f & Hf & [Hx ->]). right. split; [| exists f; split; [exact Hf | split; [exact Hx | reflexivity]]].
  destruct (Hclear f Hf); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wbytes_other_Z : forall m a bs (x : word),
  0 <= a < 2^64 -> a + Z.of_nat (length bs) <= 2^64 ->
  (bv_unsigned x < a \/ a + Z.of_nat (length bs) <= bv_unsigned x) ->
  wbytes m (Z_to_bv 64 a) bs x = m x.
Proof.
  intros m a bs x Ha Hnw [Hl | Hh].
  - apply wbytes_below; rewrite u_lit by lia; lia.
  - apply wbytes_above; rewrite u_lit by lia; lia.
Qed.

Lemma mbyte_store_in : forall m a (n : nat) (v : word) k,
  0 <= a -> a + Z.of_nat n <= 2^64 -> 0 <= k < Z.of_nat n ->
  mbyte (wbytes m (Z_to_bv 64 a) (word_to_le_bytes n v)) (a + k) = Some (byte_of (bv_unsigned v) k).
Proof.
  intros m a n v k Ha Hnw Hk.
  rewrite mbyte_wbytes_in; [| lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia].
  f_equal. replace (a + k - a) with k by lia. unfold word_to_le_bytes.
  rewrite nth_Z_to_le_bytes; [| apply u64_range | lia]. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma mbyte_store_out : forall m a (n : nat) (v : word) x,
  0 <= a < 2^64 -> a + Z.of_nat n <= 2^64 -> 0 <= x < 2^64 -> (x < a \/ a + Z.of_nat n <= x) ->
  mbyte (wbytes m (Z_to_bv 64 a) (word_to_le_bytes n v)) x = mbyte m x.
Proof.
  intros m a n v x Ha Hnw Hx Hout.
  apply mbyte_wbytes_out; rewrite ?length_N_to_le_bytes; lia.
Qed.

Lemma byte_of_0 : forall v, byte_of v 0 = v mod 256.
Proof. intros v. unfold byte_of. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r. reflexivity. Qed.

Lemma byte_of_1 : forall v, byte_of v 1 = (v / 256) mod 256.
Proof. intros v. unfold byte_of. reflexivity. Qed.

Lemma mbyte_ext : forall m1 m2 x, m1 (Z_to_bv 64 x) = m2 (Z_to_bv 64 x) -> mbyte m1 x = mbyte m2 x.
Proof. intros m1 m2 x H. unfold mbyte. rewrite !rdn1_eq, H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma lor_low_high : forall lo hi n, 0 <= n -> 0 <= lo < 2^n -> 0 <= hi ->
  Z.lor lo (hi * 2^n) = lo + hi * 2^n.
Proof.
  intros lo hi n Hn Hlo Hhi.
  assert (Hd : Z.land lo (hi * 2^n) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i n) as [Hl|Hl].
    - rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    - destruct (Z.eq_dec lo 0) as [->|Hnz]; [rewrite Z.bits_0; reflexivity|].
      rewrite (Z.bits_above_log2 lo i); [reflexivity | lia |].
      apply Z.lt_le_trans with n; [apply Z.log2_lt_pow2; lia | lia]. }
  rewrite <- Z.lxor_lor by exact Hd. symmetry. rewrite <- Z.add_nocarry_lxor by exact Hd. reflexivity.
Qed.

End WithLayout.

(* [comment removed for export] *)
Ltac reassoc :=
  lazymatch goal with
  | |- tsafe (mbind (mbind ?m ?f) ?g ?s) ?P => apply (ts_assoc m f g s P)
  end.
