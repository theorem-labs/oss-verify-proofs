(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module ZStores.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Local Open Scope Z_scope.

Definition zeros (n : nat) : list byte := repeat (Z_to_bv 8 0) n.

Fixpoint zstores (m : word -> option byte) (d : word) (ws : list (Z * nat)) : word -> option byte :=
  match ws with
  | [] => m
  | (o, n) :: ws' => zstores (wbytes m (Z_to_bv 64 (bv_unsigned d + o)) (zeros n)) d ws'
  end.

Definition covers_off (i : Z) (on : Z * nat) : bool :=
  (fst on <=? i) && (i <? fst on + Z.of_nat (snd on)).

Definition ws_inb (ws : list (Z * nat)) (N : Z) : bool :=
  forallb (fun on => (0 <=? fst on) && (fst on + Z.of_nat (snd on) <=? N)) ws.

Fixpoint iota_Z (i : Z) (k : nat) : list Z :=
  match k with O => [] | S k' => i :: iota_Z (i + 1) k' end.

Definition ws_cover (ws : list (Z * nat)) (N : nat) : bool :=
  forallb (fun i => existsb (covers_off i) ws) (iota_Z 0 N).

Lemma forallb_In : forall {A} (f : A -> bool) l x, forallb f l = true -> In x l -> f x = true.
Proof.
  induction l as [|y l IH]; intros x H Hin; [contradiction|].
  cbn in H. apply andb_true_iff in H as [Hy Hl].
  destruct Hin as [<-|Hin]; [exact Hy | apply IH; assumption].
Qed.

Lemma iota_Z_In : forall k i z, i <= z < i + Z.of_nat k -> In z (iota_Z i k).
Proof.
  induction k as [|k IH]; intros i z Hz; [lia|].
  cbn. destruct (Z.eq_dec i z); [left; assumption | right]. apply IH. lia.
Qed.

Lemma existsb_false_forall : forall {A} (f : A -> bool) l,
  existsb f l = false -> forall x, In x l -> f x = false.
Proof.
  induction l as [|y l IH]; intros H x Hin; [contradiction|].
  cbn in H. apply orb_false_iff in H as [Hy Hl].
  destruct Hin as [<-|Hin]; [exact Hy | apply IH; assumption].
Qed.

Lemma existsb_true_exists : forall {A} (f : A -> bool) l,
  existsb f l = true -> exists x, In x l /\ f x = true.
Proof.
  induction l as [|y l IH]; intros H; [discriminate|].
  cbn in H. apply orb_true_iff in H as [Hy|Hl].
  - exists y. split; [left; reflexivity | exact Hy].
  - destruct (IH Hl) as [x [Hin Hx]]. exists x. split; [right; exact Hin | exact Hx].
Qed.

Lemma length_zeros : forall n, length (zeros n) = n.
Proof. intro n. apply repeat_length. Qed.

Lemma nth_zeros : forall n k, nth k (zeros n) (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof. intros n k. unfold zeros. apply nth_repeat. Qed.

Lemma rdn_wbytes_zeros_in : forall segs m (d a : word) (N n : nat),
  bv_unsigned d + Z.of_nat N < 2^64 ->
  bv_unsigned d <= bv_unsigned a ->
  bv_unsigned a + Z.of_nat n <= bv_unsigned d + Z.of_nat N ->
  rdn segs (wbytes m d (zeros N)) a n = Some (zeros n).
Proof.
  intros segs m d a N n Hnw Hlo Hhi. unfold zeros at 2. apply rdn_const; [lia|].
  intros x Hx. rewrite wbytes_inside by (rewrite length_zeros; lia).
  f_equal. apply nth_zeros.
Qed.


Section Cover.
  Variable d : word.
  Variable N : Z.
  Hypothesis Hnw : bv_unsigned d + N < 2^64.

  Lemma zstores_miss : forall ws m (x : word),
    ws_inb ws N = true ->
    (forall on, In on ws -> covers_off (bv_unsigned x - bv_unsigned d) on = false) ->
    zstores m d ws x = m x.
  Proof.
    induction ws as [|[o n] ws IH]; intros m x Hinb Hno; [reflexivity|].
    cbn [zstores]. cbn [ws_inb forallb fst snd] in Hinb.
    apply andb_true_iff in Hinb as [Hon Hinb]. apply andb_true_iff in Hon as [Ho Hn].
    apply Z.leb_le in Ho. apply Z.leb_le in Hn.
    rewrite IH; [| exact Hinb | intros on Hin; apply Hno; right; exact Hin].
    pose proof (Hno (o, n) (or_introl eq_refl)) as Hc. cbn [covers_off fst snd] in Hc.
    pose proof (u64_range x). pose proof (u64_range d).
    apply wbytes_outside.
    - rewrite length_zeros. rewrite u_Z2bv by lia. lia.
    - rewrite length_zeros. rewrite u_Z2bv by lia.
      apply andb_false_iff in Hc as [Hc|Hc]; [apply Z.leb_gt in Hc | apply Z.ltb_ge in Hc];
        cbn [fst snd] in Hc; lia.
  Qed.

  Lemma zstores_hit : forall ws m (x : word),
    ws_inb ws N = true ->
    (exists on, In on ws /\ covers_off (bv_unsigned x - bv_unsigned d) on = true) ->
    zstores m d ws x = Some (Z_to_bv 8 0).
  Proof.
    induction ws as [|[o n] ws IH]; intros m x Hinb Hex.
    { destruct Hex as [on [[] _]]. }
    cbn [zstores]. cbn [ws_inb forallb fst snd] in Hinb.
    apply andb_true_iff in Hinb as [Hon Hinb]. apply andb_true_iff in Hon as [Ho Hn].
    apply Z.leb_le in Ho. apply Z.leb_le in Hn.
    destruct (existsb (covers_off (bv_unsigned x - bv_unsigned d)) ws) eqn:E.
    - apply IH; [exact Hinb|]. apply existsb_true_exists. exact E.
    - rewrite zstores_miss; [| exact Hinb | apply existsb_false_forall; exact E].
      destruct Hex as [on [[<-|Hin] Hc]].
      2:{ rewrite (existsb_false_forall _ _ E on Hin) in Hc. discriminate. }
      cbn [covers_off fst snd] in Hc. apply andb_true_iff in Hc as [Hc1 Hc2].
      apply Z.leb_le in Hc1. apply Z.ltb_lt in Hc2. cbn [fst snd] in Hc1, Hc2.
      pose proof (u64_range x). pose proof (u64_range d).
      rewrite wbytes_inside by (rewrite length_zeros, u_Z2bv by lia; lia).
      f_equal. apply nth_zeros.
  Qed.

  Lemma zstores_cover : forall ws m (n : nat),
    Z.of_nat n = N ->
    ws_inb ws N = true ->
    ws_cover ws n = true ->
    zstores m d ws = wbytes m d (zeros n).
  Proof.
    intros ws m n HnN Hinb Hcov. apply functional_extensionality. intro x.
    pose proof (u64_range x). pose proof (u64_range d).
    destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned d)) as [Hlt|Hge].
    { rewrite wbytes_outside by (rewrite length_zeros; lia).
      apply zstores_miss; [exact Hinb|]. intros [o k] Hin.
      pose proof (forallb_In _ _ _ Hinb Hin) as Hb. cbn [fst snd] in Hb.
      apply andb_true_iff in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1.
      cbn [covers_off fst snd]. apply andb_false_iff. left. apply Z.leb_gt. cbn [fst snd]. lia. }
    destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned d + N)) as [Hin|Hout].
    - rewrite wbytes_inside by (rewrite length_zeros; lia). rewrite nth_zeros.
      apply zstores_hit; [exact Hinb|].
      pose proof (forallb_In _ _ _ Hcov (iota_Z_In n 0 (bv_unsigned x - bv_unsigned d) ltac:(lia))) as He.
      apply existsb_true_exists in He. exact He.
    - rewrite wbytes_outside by (rewrite length_zeros; lia).
      apply zstores_miss; [exact Hinb|]. intros [o k] Hin'.
      pose proof (forallb_In _ _ _ Hinb Hin') as Hb. cbn [fst snd] in Hb.
      apply andb_true_iff in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb2.
      cbn [covers_off fst snd]. apply andb_false_iff. right. apply Z.ltb_ge. cbn [fst snd]. lia.
  Qed.
End Cover.
End ZStores.
Require LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module StartupAux.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma getr_empty : forall r : reg, getr bvmap_empty r = Z_to_bv 64 0.
Proof.
  intro r. unfold getr. destruct (bv_eqb r 0); [reflexivity|].
  unfold reg_get, bvmap_get, bvmap_empty.
  destruct (bv_key r); cbn [tget]; apply bv_eq; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Open Scope Z_scope.

Lemma land_align_mask : forall a k, 0 <= a < 2^64 -> 0 <= k <= 64 -> a mod 2^k = 0 ->
  Z.land a (2^64 - 2^k) = a.
Proof.
  intros a k Ha Hk Hmod.
  replace (2^64 - 2^k) with (Z.ldiff (Z.ones 64) (Z.ones k)).
  2:{ rewrite Z.ldiff_land, <- Z.sub_land_same_l, Z.land_ones by lia.
      rewrite Z.ones_mod_pow2 by lia. rewrite !Z.ones_equiv. lia. }
  rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia.
  rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  pose proof (Z.div_mod a (2^k) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma v_andi_m16_aligned : forall x : word,
  bv_unsigned x mod 16 = 0 -> v_andi x (-16) = x.
Proof.
  intros x Hm. unfold v_andi. apply bv_eq. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 (-16)) with (2^64 - 2^4).
  pose proof (u64_range x).
  rewrite land_align_mask by (first [lia | exact Hm]).
  apply bv_wrap_small. unfold bv_modulus. lia.
Qed.


(* [comment removed for export] *)
Lemma land_low_zero : forall a k, 0 <= a -> 0 <= k -> a mod 2^k = 0 -> Z.land a (Z.ones k) = 0.
Proof. intros a k Ha Hk Hm. rewrite Z.land_ones by lia. exact Hm. Qed.

Lemma v_andi_3_aligned : forall x : word,
  bv_unsigned x mod 4 = 0 -> v_andi x 3 = Z_to_bv 64 0.
Proof.
  intros x Hm. unfold v_andi. f_equal.
  change (bv_wrap 64 3) with (Z.ones 2). apply land_low_zero; [apply u64_range | lia | exact Hm].
Qed.

Lemma land_4_aligned8 : forall a, 0 <= a -> a mod 8 = 0 -> Z.land a 4 = 0.
Proof.
  intros a Ha Hm.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.bits_0.
  change 4 with (2^2). rewrite Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec 2 i); [|apply andb_false_r].
  subst i.
  replace a with ((a / 8) * 2^3) by lia.
  rewrite Z.mul_pow2_bits by lia. change (2 - 3) with (-1).
  rewrite Z.testbit_neg_r by lia. reflexivity.
Qed.

Lemma v_andi_4_aligned8 : forall x : word,
  bv_unsigned x mod 8 = 0 -> v_andi x 4 = Z_to_bv 64 0.
Proof.
  intros x Hm. unfold v_andi. f_equal.
  change (bv_wrap 64 4) with 4. apply land_4_aligned8; [apply u64_range | exact Hm].
Qed.


Lemma mod4_mod_pow2 : forall t k, 2 <= k -> (t mod 2^k) mod 4 = t mod 4.
Proof.
  intros t k Hk. apply Z.mod_mod_divide.
  exists (2^(k-2)). change 4 with (2^2). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma negw_and3_aligned : forall x : word,
  bv_unsigned x mod 4 = 0 -> v_andi (v_subw (Z_to_bv 64 0) x) 3 = Z_to_bv 64 0.
Proof.
  intros x Hm. unfold v_andi, v_subw. f_equal.
  change (bv_wrap 64 3) with (Z.ones 2). rewrite Z.land_ones by lia.
  rewrite Z_to_bv_unsigned. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  unfold bv_swrap. rewrite bv_wrap64_mod.
  change (bv_half_modulus 32) with (2^31).
  unfold bv_wrap. change (bv_modulus 32) with (2^32). change (2^2) with 4.
  rewrite mod4_mod_pow2 by lia.
  rewrite <- Zminus_mod_idemp_l.
  rewrite mod4_mod_pow2 by lia.
  replace ((0 - bv_unsigned x + 2^31) mod 4) with 0.
  2:{ replace (0 - bv_unsigned x + 2^31) with (2^31 - bv_unsigned x) by lia.
      rewrite <- Zminus_mod_idemp_r, Hm. reflexivity. }
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma firstn_Z_to_le_bytes : forall k n z, (k <= n)%nat ->
  firstn k (Z_to_le_bytes n z) = Z_to_le_bytes k z.
Proof.
  induction k as [|k IH]; intros n z Hk; [reflexivity|].
  destruct n as [|n]; [lia|]. cbn [Z_to_le_bytes firstn]. rewrite IH by lia. reflexivity.
Qed.

Lemma firstn_word_to_le_bytes : forall k n (v : word), (k <= n)%nat ->
  firstn k (word_to_le_bytes n v) = word_to_le_bytes k v.
Proof. intros. unfold word_to_le_bytes. apply firstn_Z_to_le_bytes. assumption. Qed.

(* [comment removed for export] *)
Lemma rdn_low_bytes : forall segs m (a v : word) k, (k <= 8)%nat ->
  rdn segs m a 8 = Some (word_to_le_bytes 8 v) ->
  rdn segs m a k = Some (word_to_le_bytes k v).
Proof.
  intros segs m a v k Hk H.
  rewrite (rdn_firstn segs m 8 a _ k H Hk). f_equal. apply firstn_word_to_le_bytes. exact Hk.
Qed.

Lemma bytes_le_to_Z_4_small : forall v : word, bv_unsigned v < 2^32 ->
  bytes_le_to_Z (word_to_le_bytes 4 v) = bv_unsigned v.
Proof.
  intros v Hv. rewrite bytes_le_N. change (2 ^ (8 * Z.of_nat 4)) with (2^32).
  apply Z.mod_small. pose proof (u64_range v). lia.
Qed.

Lemma v_lw_small : forall v : word, bv_unsigned v < 2^31 -> v_lw v = v.
Proof.
  intros v Hv. unfold v_lw. apply bv_eq. rewrite Z_to_bv_unsigned.
  pose proof (u64_range v).
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31); lia).
  apply bv_wrap_small. unfold bv_modulus. lia.
Qed.





Lemma Z_to_bv_u_eq : forall (a : word) (z : Z), z = bv_unsigned a -> Z_to_bv 64 z = a.
Proof. intros a z ->. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma Z_to_bv_u_eq_sym : forall (a : word) (z : Z), z = bv_unsigned a -> a = Z_to_bv 64 z.
Proof. intros a z H. symmetry. apply Z_to_bv_u_eq. exact H. Qed.
End StartupAux.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module StartupTac.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Export OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit StartupAux ZStores.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac pin :=
  repeat match goal with
         | H : getr ?rs ?r = _ |- context [getr ?rs ?r] => rewrite !H
         end.

(* [comment removed for export] *)
Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with
             | context [Z_to_bv 64 _] => fail
             | _ => rewrite (u_Z2bv z) by lia
             end
         end.

(* [comment removed for export] *)
Ltac zlit :=
  repeat match goal with
         | |- context [Z_to_bv 64 ?z] =>
             lazymatch z with
             | Z0 => fail | Zpos _ => fail | Zneg _ => fail
             | _ => check_closed_term z; let z' := eval vm_compute in z in change z with z'
             end
         end.

(* [comment removed for export] *)
Ltac region_side :=
  unfold win_lo; rewrite ?stack_max_size_val, ?length_N_to_le_bytes, ?length_zeros, ?repeat_length;
  cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul]; imm_norm; unorm; lia.

(* [comment removed for export] *)
Ltac addr_norm :=
  gres; pin; imm_norm; rewrite ?v_addi_0; unfold v_addi, v_add; unorm; zlit.

(* [comment removed for export] *)
Ltac vclose_fin :=
  first [ reflexivity | f_equal; lia | apply at_self | symmetry; apply at_self
        | apply Z_to_bv_u_eq; lia | apply Z_to_bv_u_eq_sym; lia | bveq ].
Ltac vclose :=
  gres; pin; imm_norm;
  first [ reflexivity
        | unfold v_addi, v_add; unorm; zlit; vclose_fin
        | rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l; first [ reflexivity | vclose_fin ]
        | rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l; unfold v_addi, v_add; unorm; zlit; vclose_fin ].

(* [comment removed for export] *)
Ltac sn F D := stepn F D; pin.
Ltac sv F D v := stepiv F D v vclose.

(* [comment removed for export] *)
Ltac blit :=
  repeat match goal with
         | |- context [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 ?z))] =>
             lazymatch z with
             | Z0 => change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 0)
             | Zpos _ => let z' := eval vm_compute in (z mod 256)%Z in
                         change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 z')
             end
         end.

(* [comment removed for export] *)
Ltac push_store :=
  blit;
  first [ rewrite wbytes_cmem_win by region_side
        | rewrite wbytes_cmem_data by region_side
        | idtac ].

(* [comment removed for export] *)
Ltac stw F D aa vv oktac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Store SZ8 _ _ _, _) =>
        eapply step_sd_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | vclose | vclose | oktac ]
    | decode_any _ = Some (Store SZ4 _ _ _, _) =>
        eapply step_sw_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | vclose | vclose | oktac ]
    | decode_any _ = Some (Store SZ2 _ _ _, _) =>
        eapply step_sh_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | vclose | vclose | oktac ]
    | decode_any _ = Some (Store SZ1 _ _ _, _) =>
        eapply MmapSim.step_sb_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | vclose | vclose | reflexivity | oktac ]
    end
  | step_simpl; push_store ].

(* [comment removed for export] *)
Ltac ok_sub Hok :=
  store_ok_peel; eapply store_ok_sub; [ | exact Hok | | ];
  rewrite ?length_N_to_le_bytes, ?length_zeros; unorm; lia.

(* [comment removed for export] *)
Ltac ok_win HJ :=
  apply store_ok_cmem_win; [ repeat apply wfJ_wbytes; exact HJ | region_side | region_side ].

(* [comment removed for export] *)
Ltac ok_data :=
  apply store_ok_cmem_data;
  lazymatch goal with |- ?g => check_closed_term g; vm_compute; reflexivity end.

(* [comment removed for export] *)
Ltac ld_step F D bsv vv rdtac valtac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Load SZ8 _ _ _ _, _) => eapply step_ld with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ4 true _ _ _, _) => eapply step_lw with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ4 false _ _ _, _) => eapply step_lwu with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ2 true _ _ _, _) => eapply step_lh with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ2 false _ _ _, _) => eapply step_lhu with (bs := bsv) (v := vv)
    end;
    [ exact F | reflexivity | exact D | addr_norm; rdtac | valtac ]
  | step_simpl ]; vnorm; pin.

(* [comment removed for export] *)
Ltac lb_step F D bb rdtac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Load SZ1 false _ _ _, _) => eapply step_lbu with (b := bb)
    | decode_any _ = Some (Load SZ1 true _ _ _, _) => eapply step_lb with (b := bb)
    end;
    [ exact F | reflexivity | exact D | addr_norm; rdtac ]
  | step_simpl ]; vnorm; pin.

(* [comment removed for export] *)
Ltac peel := repeat (rewrite rdn_wbytes_out by region_side).

(* [comment removed for export] *)
Ltac rd_img L := addr_norm; rewrite rdn_cmem_data by region_side; peel; exact L.

(* [comment removed for export] *)
Ltac rd_hit8 :=
  addr_norm; peel;
  lazymatch goal with |- rdn _ (wbytes _ ?a' _) ?a _ = _ =>
    first [ constr_eq a a' | replace a with a' by (first [f_equal; lia | bveq]) ] end;
  apply rdn_wbytes_hit8; unorm; lia.

(* [comment removed for export] *)
Ltac in_list := cbn [In]; repeat first [ left; reflexivity | right ].
Ltac solve_regs_agree :=
  repeat (apply regs_agree_upd; [ in_list | ]); apply regs_agree_refl.

(* [comment removed for export] *)
Ltac incl_list :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn [In] in Hr;
  repeat (destruct Hr as [<-|Hr]; [in_list|]); destruct Hr.
Ltac regs_agree_weaken Hag :=
  eapply regs_agree_mono; [| exact Hag]; incl_list.

Ltac notin_list :=
  cbn [In]; intros HH; repeat (destruct HH as [HH|HH]; [apply bv_eq in HH; cbv in HH; discriminate HH|]); exact HH.

(* [comment removed for export] *)
Ltac carry Hag H r T :=
  pose proof (Hag r ltac:(notin_list)) as T;
  repeat first [ rewrite getr_same in T by reg_neq_tac | rewrite getr_other in T by reg_neq_tac ];
  rewrite ?H in T.

(* [comment removed for export] *)
Ltac ra_chain :=
  first [ apply regs_agree_refl
        | apply regs_agree_upd; [ in_list | ]; ra_chain
        | match goal with
          | Hag : regs_agree _ _ ?r |- regs_agree _ _ ?r =>
              eapply regs_agree_trans; [ | regs_agree_weaken Hag ]; ra_chain
          end ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition bwd (segs : list Segment) (G : machine_state -> Prop) : Prop :=
  forall st st', msteps segs st st' -> G st' -> G st.


(* [comment removed for export] *)
Ltac gsteps HG := eapply HG.
End StartupTac.
Module PuPeel.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac ZStores StartupTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Open Scope Z_scope.

Definition pp_out_lit (za n zb nb : Z) : bool :=
  (0 <=? za) && (za <? 2^64) && (za + n <=? 2^64) && (0 <=? zb) && (zb <? 2^64) && (zb + nb <=? 2^64) && ((za + n <=? zb) || (zb + nb <=? za)).

(* [comment removed for export] *)
Definition pp_out_off (lo hi oa n ob nb : Z) : bool :=
  (0 <=? lo + oa) && (hi + oa <? 2^64) && (hi + oa + n <=? 2^64) && (0 <=? lo + ob) && (hi + ob <? 2^64) && (hi + ob + nb <=? 2^64) && ((oa + n <=? ob) || (ob + nb <=? oa)).

Section PP.
Context {fx : FPState}.

Lemma pp_rdn_lit : forall segs bs m (zb za : Z) n nb,
  length bs = nb -> pp_out_lit za (Z.of_nat n) zb (Z.of_nat nb) = true ->
  rdn segs (wbytes m (Z_to_bv 64 zb) bs) (Z_to_bv 64 za) n = rdn segs m (Z_to_bv 64 za) n.
Proof.
  intros segs bs m zb za n nb L H. subst nb. unfold pp_out_lit in H.
  repeat rewrite andb_true_iff in H. rewrite orb_true_iff in H. rewrite ?Z.leb_le, ?Z.ltb_lt in H.
  destruct H as ((((((H1 & H1') & H2) & H3) & H3') & H4) & H5).
  assert (E1 : bv_unsigned (Z_to_bv 64 za) = za) by (apply u_Z2bv; lia).
  assert (E2 : bv_unsigned (Z_to_bv 64 zb) = zb) by (apply u_Z2bv; lia).
  apply rdn_wbytes_out; rewrite ?E1, ?E2; rewrite ?Z.leb_le in H5; lia.
Qed.

Lemma pp_rdn_off : forall segs bs m (za zb s lo hi oa ob : Z) n nb,
  za = (s + oa)%Z -> zb = (s + ob)%Z ->
  (lo <= s)%Z -> (s <= hi)%Z -> length bs = nb -> pp_out_off lo hi oa (Z.of_nat n) ob (Z.of_nat nb) = true ->
  rdn segs (wbytes m (Z_to_bv 64 zb) bs) (Z_to_bv 64 za) n = rdn segs m (Z_to_bv 64 za) n.
Proof.
  intros segs bs m za zb s lo hi oa ob n nb -> -> Hl Hh L H. subst nb. unfold pp_out_off in H.
  repeat rewrite andb_true_iff in H. rewrite orb_true_iff in H. rewrite ?Z.leb_le, ?Z.ltb_lt in H.
  destruct H as ((((((H1 & H1') & H2) & H3) & H3') & H4) & H5).
  assert (E1 : bv_unsigned (Z_to_bv 64 (s + oa)) = s + oa) by (apply u_Z2bv; lia).
  assert (E2 : bv_unsigned (Z_to_bv 64 (s + ob)) = s + ob) by (apply u_Z2bv; lia).
  apply rdn_wbytes_out; rewrite ?E1, ?E2; rewrite ?Z.leb_le in H5; lia.
Qed.
End PP.

(* [comment removed for export] *)
Ltac pp_blen bs :=
  lazymatch bs with
  | word_to_le_bytes ?k _ => k
  | zeros ?k => k
  | repeat _ ?k => k
  | nil => O
  | cons _ ?t => let r := pp_blen t in constr:(S r)
  end.
Ltac pp_len_eq :=
  first [ reflexivity | apply length_N_to_le_bytes | apply length_zeros | apply repeat_length ].

Ltac pp_is_lit z := lazymatch z with Z0 => idtac | Zpos ?p => is_pos_lit p | Zneg ?p => is_pos_lit p end.
Ltac pp_is_nat_lit n := lazymatch n with O => idtac | S ?m => pp_is_nat_lit m end.

(* [comment removed for export] *)
Ltac pp_split z :=
  lazymatch z with
  | (?x - ?k)%Z =>
      let _ := match goal with _ => pp_is_lit k end in
      let r := pp_split x in
      lazymatch r with pair ?s ?o => let o' := eval cbv in (o - k)%Z in constr:(pair s o') end
  | (?x + ?k)%Z =>
      let _ := match goal with _ => pp_is_lit k end in
      let r := pp_split x in
      lazymatch r with pair ?s ?o => let o' := eval cbv in (o + k)%Z in constr:(pair s o') end
  | _ => constr:(pair z 0%Z)
  end.

(* [comment removed for export] *)
Ltac pp_lo s := match goal with H : (?lo <= s)%Z |- _ => let _ := match goal with _ => pp_is_lit lo end in constr:(pair lo H) end.
Ltac pp_hi s := match goal with H : (s <= ?hi)%Z |- _ => let _ := match goal with _ => pp_is_lit hi end in constr:(pair hi H) end.

Ltac pp_peel1 :=
  lazymatch goal with
  | |- context [rdn ?segs (wbytes ?m (Z_to_bv 64 ?zb) ?bs) (Z_to_bv 64 ?za) ?n] =>
      let nb := pp_blen bs in
      let _ := match goal with _ => pp_is_nat_lit nb; pp_is_nat_lit n end in
      first
        [ pp_is_lit za; pp_is_lit zb;
          rewrite (pp_rdn_lit segs bs m zb za n nb ltac:(pp_len_eq) (@eq_refl bool true))
        | let A := pp_split za in let B := pp_split zb in
          lazymatch A with
          | pair ?s ?oa =>
              lazymatch B with
              | pair ?s' ?ob =>
                  constr_eq s s';
                  let L := pp_lo s in let Hh := pp_hi s in
                  lazymatch L with
                  | pair ?lo ?Hl =>
                      lazymatch Hh with
                      | pair ?hi ?Hu =>
                          let C := constr:(pp_out_off lo hi oa (Z.of_nat n) ob (Z.of_nat nb)) in
                          let c := eval vm_compute in C in
                          lazymatch c with
                          | true =>
                              let Ea := fresh "ppEa" in let Eb := fresh "ppEb" in
                              assert (Ea : za = (s + oa)%Z) by (clear; lia);
                              assert (Eb : zb = (s + ob)%Z) by (clear; lia);
                              rewrite (pp_rdn_off segs bs m za zb s lo hi oa ob n nb Ea Eb Hl Hu ltac:(pp_len_eq) (@eq_refl bool true));
                              clear Ea Eb
                          end
                      end
                  end
              end
          end ]
  end.

(* [comment removed for export] *)
Ltac pp_stop :=
  lazymatch goal with
  | |- context [rdn ?segs (wbytes ?m (Z_to_bv 64 ?zb) ?bs) (Z_to_bv 64 ?za) ?n] =>
      let nb := pp_blen bs in
      let _ := match goal with _ => pp_is_nat_lit nb; pp_is_nat_lit n end in
      let A := pp_split za in let B := pp_split zb in
      lazymatch A with
      | pair ?s ?oa =>
          lazymatch B with
          | pair ?s' ?ob =>
              constr_eq s s';
              let c := eval vm_compute in ((oa + Z.of_nat n <=? ob) || (ob + Z.of_nat nb <=? oa))%Z in
              lazymatch c with false => idtac end
          end
      end
  end.

Section PPA.
Context {fx : FPState}.
Lemma pp_rdn_addr : forall segs m (a a' : word) n r, a = a' -> rdn segs m a' n = r -> rdn segs m a n = r.
Proof. intros segs m a a' n r -> H. exact H. Qed.
End PPA.
(* [comment removed for export] *)
Ltac addr_norm_orig := gres; pin; imm_norm; rewrite ?v_addi_0; unfold v_addi, v_add; unorm; zlit.   (* [comment removed for export] *)
Ltac addr_norm_fast :=
  lazymatch goal with
  | |- rdn ?segs ?M ?A ?n = ?r =>
      refine (pp_rdn_addr segs M A _ n r _ _); [ addr_norm_orig; reflexivity | ]
  | |- _ => addr_norm_orig
  end.

Ltac peel_fast := repeat (tryif pp_stop then fail else first [ pp_peel1 | rewrite rdn_wbytes_out by region_side ]).
End PuPeel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Export StartupTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import PropExec.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint code_at (segs : list Segment) (base : word) (off : Z) (ws : list (bv 32)) : Prop :=
  match ws with
  | [] => True
  | w :: ws' => fetch_word segs (at_ base off) = Some w /\ code_at segs base (off + 4)%Z ws'
  end.

(* [comment removed for export] *)
Ltac code_at_vm :=
  cbn [code_at Z.add Pos.add Pos.succ];
  repeat split;
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Ltac zlit_at :=
  repeat match goal with
  | |- context [at_ ?b (?x + ?y)%Z] =>
      is_Z_lit x; is_Z_lit y;
      let z := eval cbv in (x + y)%Z in change (at_ b (x + y)%Z) with (at_ b z)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.

(* [comment removed for export] *)
Ltac fold_at_vars :=
  repeat match goal with
         | |- context [v_addi ?b ?e] => is_var b; change (v_addi b e) with (at_ b e)
         end.

(* [comment removed for export] *)
Ltac vn :=
  gres; rwH; imm_norm; unfold btgt;
  rewrite ?at_addi; rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l;
  fold_at_vars; rewrite ?at_addi; zlit_at; vals_lit.
Ltac pcn := vn.

(* [comment removed for export] *)
Ltac an F D :=
  lazymatch type of D with
  | decode_any _ = Some (Jal _ _, _) => stepj F D; vn
  | _ => stepi F D; vn
  end.

(* [comment removed for export] *)
Ltac av F D v tac := stepiv F D v ltac:(gres; rwH; imm_norm; tac); vn.

(* [comment removed for export] *)
Ltac ab_tk F D tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_tk
    | decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_tk
    | decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_tk
    | decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_tk
    | decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_tk
    | decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_tk
    end;
    [ exact F | reflexivity | exact D | gres; rwH; imm_norm; tac ]
  | step_simpl; vn ].

Ltac ab_ft F D tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_ft
    | decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_ft
    | decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_ft
    | decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_ft
    | decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_ft
    | decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_ft
    end;
    [ exact F | reflexivity | exact D | gres; rwH; imm_norm; tac ]
  | step_simpl; vn ].

(* [comment removed for export] *)
Ltac aret F D k :=
  stepjr F D k ltac:(gres; rwH; reflexivity);
  imm_norm;
  try lazymatch goal with
      | Hk : ret_ok k |- _ => rewrite (Hk : v_jalr k 0 = k)
      end.

(* [comment removed for export] *)
Ltac condz :=
  rwH; unfold at_, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
  first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; unorm; lia.

(* [comment removed for export] *)
Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try reflexivity; try (f_equal; lia).




(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record cpyH (segs : list Segment) (mem0 : word -> option byte) (dst src : word) (n : Z) (bs : list byte) : Prop := CPYH {
  cHn : (0 <= n)%Z;
  cHlen : length bs = Z.to_nat n;
  cHsrc : rdn segs mem0 src (length bs) = Some bs;
  cHdst : store_ok segs mem0 dst (length bs) = true;
  cHdisj : (bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst)%Z;
  cHnws : (bv_unsigned src + n < 2 ^ 64)%Z;
  cHnwd : (bv_unsigned dst + n < 2 ^ 64)%Z }.

Section MEMK.
  Variable segs : list Segment.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Hypothesis HOK : cpyH segs mem0 dst src n bs.

  Let Hn := cHn _ _ _ _ _ _ HOK.
  Let Hlen := cHlen _ _ _ _ _ _ HOK.
  Let Hsrc := cHsrc _ _ _ _ _ _ HOK.
  Let Hdst := cHdst _ _ _ _ _ _ HOK.
  Let Hdisj := cHdisj _ _ _ _ _ _ HOK.
  Let Hnws := cHnws _ _ _ _ _ _ HOK.
  Let Hnwd := cHnwd _ _ _ _ _ _ HOK.










End MEMK.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MSETK.
  Variable segs : list Segment.
  Variable mem0 : word -> option byte.
  Variable s : word.
  Variable n : Z.
  Variable b : byte.
  Hypothesis Hn : (0 <= n)%Z.
  Hypothesis Hnw : (bv_unsigned s + n < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok segs mem0 s (Z.to_nat n) = true.





End MSETK.





(* [comment removed for export] *)
Definition M8 : Z := 72340172838076673.





(* [comment removed for export] *)
Lemma step_or_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_OR rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_or (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_or segs regs pc mem rom w rd rs1 rs2 Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

(* [comment removed for export] *)
Ltac av_or F D vv tac :=
  chain_step;
  [ reflexivity
  | eapply step_or_at with (v := vv); [ exact F | reflexivity | exact D | reflexivity | gres; rwH; imm_norm; tac ]
  | step_simpl ]; vn.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
