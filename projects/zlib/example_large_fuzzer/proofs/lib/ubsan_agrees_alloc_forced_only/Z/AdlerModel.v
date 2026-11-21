(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZChkArith.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZChkAdl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition csub (x : Z) : Z := if 65520 <? x then x - 65521 else x.

(* [comment removed for export] *)
Definition lo16 (a : Z) : Z := a mod 2 ^ 16.
Definition hi16 (a : Z) : Z := (a mod 2 ^ 32) / 2 ^ 16.

(* [comment removed for export] *)
Definition eqm (x y : Z) : Prop := x mod ABASE = y mod ABASE.

Definition adler32_z_spec (adler P : Z) (d : list byte) : Z :=
  let s1 := lo16 adler in
  let s2 := hi16 adler in
  if Z.of_nat (length d) =? 1 then
    let a := csub (s1 + bnth d 0) in
    let b := csub (a + s2) in
    Z.lor (b * 2 ^ 16) a
  else if P =? 0 then 1
  else let (a, b) := adl_raw (bZ d) s1 s2 in
       Z.lor ((b mod ABASE) * 2 ^ 16) (a mod ABASE).

Lemma mod32_div16 : forall a, 0 <= a -> (a mod 2 ^ 32) / 2 ^ 16 = (a / 2 ^ 16) mod 2 ^ 16.
Proof.
  intros a Ha.
  replace (2 ^ 32) with (2 ^ 16 * 2 ^ 16) by reflexivity.
  rewrite Z.rem_mul_r by lia.
  rewrite (Z.mul_comm (2 ^ 16)), Z.div_add by lia.
  rewrite Z.mod_div by lia. lia.
Qed.

Lemma adler32_z_spec_model : forall adler P d,
  0 <= adler -> Z.of_nat (length d) <> 1 -> P <> 0 ->
  adler32_z_spec adler P d = adler32_model adler (bZ d).
Proof.
  intros adler P d Ha Hl HP. unfold adler32_z_spec, lo16, hi16.
  replace (Z.of_nat (length d) =? 1) with false by (symmetry; apply Z.eqb_neq; exact Hl).
  replace (P =? 0) with false by (symmetry; apply Z.eqb_neq; exact HP).
  unfold adler32_model.
  assert (H1 : Z.land adler 65535 = adler mod 2 ^ 16).
  { change 65535 with (Z.ones 16). apply Z.land_ones. lia. }
  assert (H2 : Z.land (Z.shiftr adler 16) 65535 = (adler mod 2 ^ 32) / 2 ^ 16).
  { change 65535 with (Z.ones 16). rewrite Z.land_ones, Z.shiftr_div_pow2 by lia.
    symmetry. apply mod32_div16. exact Ha. }
  rewrite H1, H2, adl_raw_mod.
  destruct (adl_raw (bZ d) (adler mod 2 ^ 16) (adler mod 2 ^ 32 / 2 ^ 16)) as [a b]. cbn [fst snd].
  pose proof (Z.mod_pos_bound a ABASE ltac:(unfold ABASE; lia)) as Hma.
  pose proof (Z.mod_pos_bound b ABASE ltac:(unfold ABASE; lia)) as Hmb.
  rewrite <- Z.shiftl_mul_pow2 by lia. apply combine_lor; unfold ABASE in *; lia.
Qed.

Lemma Forall_skipn : forall {A} (Q : A -> Prop) n (l : list A), Forall Q l -> Forall Q (skipn n l).
Proof.
  intros A Q n l H. revert n. induction H; intros [|n]; cbn; try constructor; auto.
Qed.

Lemma adl_raw_cons : forall b l u v, adl_raw (b :: l) u v = adl_raw l (u + b) (v + (u + b)).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma adl_raw_bound : forall l u v,
  Forall (fun b => 0 <= b < 256) l -> 0 <= u -> 0 <= v ->
  u <= fst (adl_raw l u v) <= u + 255 * Z.of_nat (length l)
  /\ v <= snd (adl_raw l u v) <= v + Z.of_nat (length l) * (u + 255 * Z.of_nat (length l)).
Proof.
  intros l. induction l as [|b l IH]; intros u v Hl Hu Hv.
  - cbn. lia.
  - inversion Hl as [|b' l' Hb Hl']; subst. rewrite adl_raw_cons.
    destruct (IH (u + b) (v + (u + b)) Hl' ltac:(lia) ltac:(lia)) as [H1 H2].
    cbn [length]. rewrite Nat2Z.inj_succ.
    set (n := Z.of_nat (length l)) in *.
    assert (Hn : 0 <= n) by lia.
    assert (Hm : n * (u + b + 255 * n) <= n * (u + 255 * (n + 1))) by (apply Z.mul_le_mono_nonneg_l; lia).
    assert (Hm2 : n * (u + 255 * (n + 1)) + (u + 255 * (n + 1)) = (n + 1) * (u + 255 * (n + 1))) by ring.
    split; [lia|]. split; [lia|].
    assert (0 <= n * (u + 255 * (n + 1))) by (apply Z.mul_nonneg_nonneg; lia). nia.
Qed.

(* [comment removed for export] *)
Lemma adl_raw_congr : forall l u v u' v',
  u mod ABASE = u' mod ABASE -> v mod ABASE = v' mod ABASE ->
  fst (adl_raw l u v) mod ABASE = fst (adl_raw l u' v') mod ABASE
  /\ snd (adl_raw l u v) mod ABASE = snd (adl_raw l u' v') mod ABASE.
Proof.
  intros l. induction l as [|b l IH]; intros u v u' v' Hu Hv; cbn [adl_raw fst snd].
  - auto.
  - apply IH.
    + rewrite (Zplus_mod u b), (Zplus_mod u' b), Hu. reflexivity.
    + rewrite (Zplus_mod v (u + b)), (Zplus_mod v' (u' + b)), Hv, (Zplus_mod u b), (Zplus_mod u' b), Hu.
      reflexivity.
Qed.

Lemma adl_raw_app' : forall xs ys u v,
  adl_raw (xs ++ ys) u v = adl_raw ys (fst (adl_raw xs u v)) (snd (adl_raw xs u v)).
Proof. apply adl_raw_app. Qed.

(* [comment removed for export] *)
Definition magq (x : Z) : Z := x * 4223091239536077 / 2 ^ 64.
Definition magT (x : Z) : Z := (magq x + (x - magq x) mod 2 ^ 64 / 2 ^ 1) / 2 ^ 15.
Definition magred (x : Z) : Z := x - ((magT x * 2 ^ 12 - magT x) * 2 ^ 4 + magT x).

Lemma csub_mod : forall x, 0 <= x < 2 * ABASE -> csub x = x mod ABASE.
Proof.
  intros x Hx. unfold csub. rewrite <- (condsub x Hx).
  destruct (Z.ltb_spec 65520 x); destruct (Z.leb_spec x 65520); unfold ABASE; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition adler_canon (a : Z) : Prop := 0 <= a < 2 ^ 32 /\ lo16 a < ABASE /\ hi16 a < ABASE.

Lemma adler_canon_1 : adler_canon 1.
Proof. unfold adler_canon, lo16, hi16, ABASE. cbn. lia. Qed.

Lemma adler32_model_canon : forall a bs, adler_canon (adler32_model a bs).
Proof.
  intros a bs. unfold adler32_model.
  pose proof (adl_canon bs (Z.land a 65535 mod ABASE) (Z.land (Z.shiftr a 16) 65535 mod ABASE)
                (Z.mod_pos_bound (Z.land a 65535) ABASE ltac:(unfold ABASE; lia))
                (Z.mod_pos_bound (Z.land (Z.shiftr a 16) 65535) ABASE ltac:(unfold ABASE; lia))) as Hc.
  destruct (adl bs (Z.land a 65535 mod ABASE) (Z.land (Z.shiftr a 16) 65535 mod ABASE)) as [u v].
  cbn [fst snd] in Hc. unfold ABASE in Hc.
  assert (E : Z.lxor (Z.shiftl v 16) u = v * 2 ^ 16 + u).
  { rewrite <- Z.add_nocarry_lxor.
    - rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
    - rewrite Z.land_comm. apply land_shiftl_disj; [change (2 ^ 16) with 65536; lia | lia | lia]. }
  rewrite E. unfold adler_canon, lo16, hi16, ABASE.
  split; [lia|]. split.
  - replace (v * 2 ^ 16 + u) with (u + v * 2 ^ 16) by lia. rewrite Z.mod_add by lia.
    rewrite Z.mod_small by lia. lia.
  - rewrite (Z.mod_small (v * 2 ^ 16 + u)) by lia.
    replace (v * 2 ^ 16 + u) with (u + v * 2 ^ 16) by lia. rewrite Z.div_add by lia.
    rewrite Z.div_small by lia. lia.
Qed.
