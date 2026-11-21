(** * KeyTie — the builder-to-declarative canonical-code tie, layer 1


    The keystone value classes need: the builder's ledger position
    ([ItGTblCover.Pos] over [it_mass]) read as the DECLARATIVE canonical
    code value ([Huff.nc] + [Huff.code_offset]).  Both sides fold the
    same length histogram; this file proves the pure-arithmetic half:

      Z.of_nat (nc L len) = 2 * it_mass (len-1) 1 (cntL L)   (1 <= len <= 15)

    where [cntL L j = count of codes of length j].  No builder objects
    here — layer 2 ties [cntL] to the build's [cnt0]/[s_count] and layer
    3 does rank = [code_offset] over the sorted work list. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Huff Inftrees ItGTblRev ItGTblGeom.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** The length histogram of a declarative lens list, as the zarr shape
    [it_mass] consumes.  Clipped to the 1..15 window [it_mass 15 1]
    reads; lengths outside it carry no mass. *)
Definition cntL (L : list nat) : zarr :=
  fun j =>
    if (1 <=? j) && (j <=? 15) then Z.of_nat (count_len L (Z.to_nat j))
    else 0.

Lemma cntL_nonneg : forall L j, 0 <= cntL L j.
Proof.
  intros L j. unfold cntL.
  destruct ((1 <=? j) && (j <=? 15)); lia.
Qed.

Lemma cntL_in_window : forall L (b : nat),
  (1 <= b <= 15)%nat ->
  cntL L (Z.of_nat b) = Z.of_nat (count_len L b).
Proof.
  intros L b Hb. unfold cntL.
  destruct (Z.leb_spec 1 (Z.of_nat b)); [|lia].
  destruct (Z.leb_spec (Z.of_nat b) 15); [|lia].
  cbn. rewrite Nat2Z.id. reflexivity.
Qed.

(** [bl_count] agrees with [count_len] off zero (Huff.v: [bl_count 0 = 0]). *)
Lemma bl_count_pos : forall L b, (1 <= b)%nat -> bl_count L b = count_len L b.
Proof.
  intros L b Hb. destruct b; [lia | reflexivity].
Qed.

(** [it_mass]'s length-step doubles the accumulated weight — the exact
    shape of [nc]'s recursion. *)
Lemma it_mass_S_shift : forall n len cnt,
  it_mass (S n) len cnt = 2 * it_mass n len cnt + cnt (len + Z.of_nat n).
Proof.
  induction n as [|n IH]; intros len cnt.
  - cbn [it_mass]. change (Z.of_nat 0) with 0.
    rewrite Z.pow_0_r, !Z.add_0_r. lia.
  - change (it_mass (S (S n)) len cnt)
      with (cnt len * 2 ^ Z.of_nat (S n) + it_mass (S n) (len + 1) cnt).
    rewrite IH.
    change (it_mass (S n) len cnt)
      with (cnt len * 2 ^ Z.of_nat n + it_mass n (len + 1) cnt).
    replace (len + 1 + Z.of_nat n) with (len + Z.of_nat (S n)) by lia.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    lia.
Qed.

(** The core identity: the canonical next-code base of length [len] is
    twice the histogram mass of the strictly shorter lengths. *)
Lemma nc_it_mass : forall L (len : nat),
  (1 <= len <= 15)%nat ->
  Z.of_nat (nc L len) = 2 * it_mass (len - 1) 1 (cntL L).
Proof.
  intros L len Hlen.
  induction len as [|len IH]; [lia|].
  destruct len as [|len'].
  - cbn. lia.
  - change (nc L (S (S len')))
      with (2 * (nc L (S len') + bl_count L (S len')))%nat.
    rewrite Nat2Z.inj_mul, Nat2Z.inj_add.
    rewrite IH by lia.
    replace (S (S len') - 1)%nat with (S (S len' - 1))%nat by lia.
    rewrite it_mass_S_shift.
    replace (1 + Z.of_nat (S len' - 1)) with (Z.of_nat (S len')) by lia.
    rewrite bl_count_pos by lia.
    rewrite cntL_in_window by lia.
    lia.
Qed.

(** Scaled form at the 15-bit mass scale: the first length-[len] code's
    canonical position.  [nc * 2^(15-len) = mass of all shorter codes at
    weight 2^(15-l)] — the reading [Pos]/[UnitStart] use. *)
Lemma it_mass_split : forall (k n : nat) (len : Z) (cnt : zarr),
  (k <= n)%nat ->
  it_mass n len cnt
  = it_mass (n - k) len cnt * 2 ^ Z.of_nat k
    + it_mass k (len + Z.of_nat (n - k)) cnt.
Proof.
  intros k n. revert k.
  induction n as [|n IH]; intros k len cnt Hk.
  - assert (k = 0)%nat by lia. subst k. cbn. lia.
  - destruct (Nat.eq_dec k (S n)) as [->|Hne].
    + replace (S n - S n)%nat with 0%nat by lia.
      cbn [it_mass]. change (Z.of_nat 0) with 0.
      rewrite Z.add_0_r. lia.
    + assert (Hk' : (k <= n)%nat) by lia.
      change (it_mass (S n) len cnt)
        with (cnt len * 2 ^ Z.of_nat n + it_mass n (len + 1) cnt).
      rewrite (IH k (len + 1) cnt Hk').
      replace (S n - k)%nat with (S (n - k))%nat by lia.
      change (it_mass (S (n - k)) len cnt)
        with (cnt len * 2 ^ Z.of_nat (n - k) + it_mass (n - k) (len + 1) cnt).
      replace (len + 1 + Z.of_nat (n - k)) with (len + Z.of_nat (S n - k))
        by lia.
      replace (Z.of_nat n) with (Z.of_nat (n - k) + Z.of_nat k) by lia.
      rewrite Z.pow_add_r by lia.
      replace (S n - k)%nat with (S (n - k))%nat by lia.
      lia.
Qed.
