(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZChecksum.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition AMAGIC_IMAGE : Z := 983265 * 4294967296 + 221234637.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mulhu_eq : forall x, 0 <= x < 1099511627776 ->
  mulhu x AMAGIC_IMAGE = (15 * x) / ABASE.
Proof.
  intros x Hx. unfold mulhu.
  pose proof (Z.div_mod (15 * x) ABASE ltac:(unfold ABASE; lia)) as Hdm.
  pose proof (Z.mod_pos_bound (15 * x) ABASE ltac:(unfold ABASE; lia)) as Hs.
  set (g0 := (15 * x) / ABASE) in *.
  set (s := (15 * x) mod ABASE) in *.
  unfold ABASE, AMAGIC_IMAGE in *.
  assert (Hlo : 18446744073709551616 * g0 <= x * (983265 * 4294967296 + 221234637))
    by lia.
  assert (Hhi : x * (983265 * 4294967296 + 221234637)
                < 18446744073709551616 * g0 + 18446744073709551616) by lia.
  replace (x * (983265 * 4294967296 + 221234637))
    with (g0 * 18446744073709551616
          + (x * (983265 * 4294967296 + 221234637) - 18446744073709551616 * g0))
    by ring.
  rewrite Z.div_add_l by lia.
  rewrite Z.div_small by lia.
  lia.
Qed.

(* [comment removed for export] *)
Lemma div15_split : forall N r, 0 <= N -> 0 <= r < ABASE ->
  (15 * (ABASE * N + r)) / ABASE = 15 * N + (15 * r) / ABASE.
Proof.
  intros N r HN Hr.
  replace (15 * (ABASE * N + r)) with (15 * N * ABASE + 15 * r) by ring.
  apply Z.div_add_l. unfold ABASE; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mdiv_core : forall N r, 0 <= N -> 0 <= r < ABASE ->
  ABASE * N + r < 1099511627776 ->
  Z.shiftr (mulhu (ABASE * N + r) AMAGIC_IMAGE
            + Z.shiftr (ABASE * N + r - mulhu (ABASE * N + r) AMAGIC_IMAGE) 1) 15
  = N.
Proof.
  intros N r HN Hr Hx.
  assert (Hx0 : 0 <= ABASE * N + r < 1099511627776) by (unfold ABASE in *; lia).
  rewrite (mulhu_eq _ Hx0), (div15_split N r HN Hr).
  set (g := (15 * r) / ABASE) in *.
  assert (Hg : 0 <= g < 15).
  { unfold g; split.
    - apply Z.div_pos; [lia | unfold ABASE; lia].
    - apply Z.div_lt_upper_bound; unfold ABASE in *; lia. }
  (* [comment removed for export] *)
  rewrite !Z.shiftr_div_pow2 by lia.
  change (2 ^ 1) with 2. change (2 ^ 15) with 32768.
  set (D := ABASE * N + r - (15 * N + g)) in *.
  pose proof (Z.div_mod D 2 ltac:(lia)) as HD.
  pose proof (Z.mod_pos_bound D 2 ltac:(lia)) as He.
  set (e := D mod 2) in *.
  (* [comment removed for export] *)
  assert (Hlow : 0 <= r + g - e).
  { destruct (Z.eq_dec r 0) as [Hr0 | Hr0].
    - assert (Hg0 : g = 0) by (unfold g; rewrite Hr0; reflexivity).
      assert (HD2 : D = 32753 * N * 2)
        by (unfold D; rewrite Hr0, Hg0; unfold ABASE; ring).
      assert (He0 : e = 0) by (unfold e; rewrite HD2; apply Z.mod_mul; lia).
      lia.
    - lia. }
  assert (Hhigh : r + g - e <= 65534) by (unfold ABASE in *; lia).
  (* [comment removed for export] *)
  replace (15 * N + g + D / 2)
    with (N * 32768 + (15 * N + g + D / 2 - N * 32768)) by ring.
  rewrite Z.div_add_l by lia.
  rewrite Z.div_small by (unfold ABASE in *; lia).
  lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem mdiv_image_correct : forall x, 0 <= x < 1099511627776 ->
  Z.shiftr (mulhu x AMAGIC_IMAGE + Z.shiftr (x - mulhu x AMAGIC_IMAGE) 1) 15
  = x / ABASE.
Proof.
  intros x Hx.
  pose proof (Z.div_mod x ABASE ltac:(unfold ABASE; lia)) as Hxd.
  pose proof (Z.mod_pos_bound x ABASE ltac:(unfold ABASE; lia)) as Hr.
  assert (HN : 0 <= x / ABASE) by (apply Z.div_pos; [lia | unfold ABASE; lia]).
  rewrite Hxd at 1 2 3.
  apply mdiv_core; [exact HN | exact Hr | unfold ABASE in *; lia].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

