(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

(* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_ah.
Ltac2 gd_tbl_AFreeSlot () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.true"; "ARUN_1.zcount"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.snd"; "ARUN_1.rblocks"; "ARUN_1.rhits"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.Lists.List.In"; "ARUN_1.ebase"; "ARUN_1.elen"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.fst"; "ARUN_1.zsum"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.sub"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.
Definition zcount (P : Z -> bool) (a : Z) (J : nat) : nat := length (filter P (map (fun i => a + Z.of_nat i) (seq 0 J))).

#[using="Type"] Lemma zcount_S : forall P a J, zcount P a (S J) = ((if P a then 1 else 0) + zcount P (a + 1) J)%nat.
Proof.
  intros P a J. unfold zcount. cbn [seq map]. rewrite <- seq_shift, map_map.
  replace (a + Z.of_nat 0) with a by lia.
  replace (map (fun x : nat => a + Z.of_nat (S x)) (seq 0 J)) with (map (fun i : nat => a + 1 + Z.of_nat i) (seq 0 J))
    by (apply map_ext; intros; lia).
  cbn. destruct (P a); cbn; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma zcount_lt_exists : forall P J a, (zcount P a J < J)%nat -> exists j, a <= j < a + Z.of_nat J /\ P j = false.
Proof.
  intros P J. induction J as [|J IH]; intros a H; [cbn in H; lia|].
  rewrite zcount_S in H. destruct (P a) eqn:E.
  - ddestruct (IH (a + 1) ltac:(lia)) as (j & Hj & Pj). exists j. split; [lia| exact Pj].
  - exists a. split; [lia| exact E].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma zcount_or : forall P Q a J, (zcount (fun j => P j || Q j) a J <= zcount P a J + zcount Q a J)%nat.
Proof.
  intros P Q a J. revert a. induction J as [|J IH]; intros a; [cbn; lia|].
  rewrite !zcount_S. specialize (IH (a + 1)). destruct (P a), (Q a); cbn; lia.
Qed.
#[using="Type"] Lemma zcount_false : forall P a J, (forall j, a <= j < a + Z.of_nat J -> P j = false) -> zcount P a J = 0%nat.
Proof.
  intros P a J. revert a. induction J as [|J IH]; intros a H; [reflexivity|].
  rewrite zcount_S. rewrite (H a) by lia. cbn. apply IH. intros j Hj. apply H. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma zcount_interval : ltac2:(CDefT.buildp (gd_tbl_AFreeSlot ()) "PP,Px,$0.$1.Pa,$0.PJ,$2.Plo,$0.Pk,$0.P,(3.=R1.)P,Pj,$0.P,(4.(3.R6.R1.)(5.R1.(6.R6.(7.R5.))))P,(8.$1.A1.R8.R2.$9.)(4.(3.R6.R3.)(5.R3.(6.R6.R5.)))(3.(7.(:.R7.R6.R5.))R3.)")
(* [comment removed for export] *).
Proof.
  intros P a J lo k Hk H.
  enough (G : forall a' J', (forall j, a' <= j < a' + Z.of_nat J' -> P j = true -> lo <= j < lo + k) ->
                            Z.of_nat (zcount P a' J') <= Z.max 0 (Z.min (lo + k) (a' + Z.of_nat J') - Z.max lo a')).
  { specialize (G a J H). lia. }
  clear a J H. intros a J. revert a. induction J as [|J IH]; intros a H; [cbn; lia|].
  rewrite zcount_S. specialize (IH (a + 1) ltac:(intros j Hj Pj; apply H; [lia| exact Pj])). destruct (P a) eqn:E.
  - specialize (H a ltac:(lia) E). rewrite Nat2Z.inj_add. cbn [Z.of_nat Pos.of_succ_nat]. lia.
  - cbn [Nat.add]. lia.
Qed.

(* [comment removed for export] *)
Fixpoint zsum {A} (f : A -> Z) (l : list A) : Z := match l with [] => 0 | x :: r => f x + zsum f r end.
#[using="Type"] Lemma zsum_app : forall {A} (f : A -> Z) l1 l2, zsum f (l1 ++ l2) = zsum f l1 + zsum f l2.
Proof. intros A f l1 l2. induction l1 as [|x r IH]; cbn; [reflexivity| rewrite IH; lia]. Qed.
#[using="Type"] Lemma zsum_nonneg : forall {A} (f : A -> Z) l, (forall x, In x l -> 0 <= f x) -> 0 <= zsum f l.
Proof. intros A f l H. induction l as [|x r IH]; cbn; [lia|]. pose proof (H x ltac:(now left)). specialize (IH ltac:(intros y Hy; apply H; now right)). lia. Qed.

(* [comment removed for export] *)
Definition ebase (e : word * word) : Z := bv_unsigned (fst e).
Definition elen (e : word * word) : Z := bv_unsigned (snd e).

(* [comment removed for export] *)
Definition rhits (F S JS : Z) (R : Z * Z) : Z :=
  if (fst R + snd R <=? F) || (F + JS <=? fst R) then 0 else snd R / S + 2.
Definition hits (F S JS : Z) (e : word * word) : Z := rhits F S JS (ebase e, elen e).

#[using="Type"] Lemma rhits_nonneg : forall F S JS R, 0 < S -> 0 <= snd R -> 0 <= rhits F S JS R.
Proof.
  intros F S JS R HS HR. unfold rhits. destruct (_ || _); [lia|]. apply Z.add_nonneg_nonneg; [apply Z.div_pos; lia| lia].
Qed.

(* [comment removed for export] *)
Definition slot (F S : Z) (j : Z) : Z := F + j * S.
Definition rblocks (F S : Z) (R : Z * Z) (j : Z) : bool :=
  (slot F S j <? fst R + snd R) && (fst R <? slot F S j + S).
Definition blocks (F S : Z) (e : word * word) (j : Z) : bool := rblocks F S (ebase e, elen e) j.

#[using="Type"] Lemma rblocks_count : ltac2:(CDefT.buildp (gd_tbl_AFreeSlot ()) "PF,$0.PS,$0.PJ,$2.PR,(;.$0.$0.)P,(5.=R3.)P,(3.=R5.)P,(3.=(<.$0.$0.R3.))(3.(7.(:.(=.R7.R6.R4.)=R5.))(>.R7.R6.(?.(7.R5.)R6.)R4.))")
(* [comment removed for export] *).
Proof.
  intros F S J [b len] HS HF HL. unfold rhits. cbn [fst snd] in *.
  destruct (Z.leb_spec (b + len) F) as [L|L]; [| destruct (Z.leb_spec (F + Z.of_nat J * S) b) as [R|R]]; cbn [orb].
  - rewrite zcount_false; [cbn; lia|]. intros j Hj. unfold rblocks, slot. cbn [fst snd]. apply Bool.andb_false_iff. left. apply Z.ltb_ge. nia.
  - rewrite zcount_false; [cbn; lia|]. intros j Hj. unfold rblocks, slot. cbn [fst snd]. apply Bool.andb_false_iff. right. apply Z.ltb_ge. nia.
  - (* [comment removed for export] *)
    apply (zcount_interval (rblocks F S (b, len)) 0 J (Z.max 0 ((b - F) / S)) (len / S + 2)); [apply Z.add_nonneg_nonneg; [apply Z.div_pos; lia| lia]|].
    intros j Rj Hj. unfold rblocks, slot in Hj. cbn [fst snd] in Hj. apply andb_prop in Hj. destruct Hj as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
    pose proof (Z.div_mod (b - F) S ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (b - F) S ltac:(lia)) as M1.
    pose proof (Z.div_mod len S ltac:(lia)) as D2. pose proof (Z.mod_pos_bound len S ltac:(lia)) as M2.
    remember ((b - F) / S) as q1. remember (len / S) as q2. remember ((b - F) mod S) as r1. remember (len mod S) as r2.
    assert (A1 : q1 * S < (j + 1) * S) by lia.
    assert (A2 : j * S < (q1 + q2 + 2) * S) by lia.
    apply Z.mul_lt_mono_pos_r in A1; [| lia]. apply Z.mul_lt_mono_pos_r in A2; [| lia].
    split; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem free_slot_exists_cover : ltac2:(CDefT.buildp (gd_tbl_AFreeSlot ()) "Pmaps,(10.(;.(11.&40.)(11.&40.)))Pcover,(10.(;.$0.$0.))PF,$0.PS,$0.PJ,$2.P,(5.=R2.)P,(3.=R4.)P,(5.(6.R5.(?.(7.R3.)R4.))(12.+2.+40.))P,PR,(;.$0.$0.)P,(13.(;.$0.$0.)R1.R8.)(3.=(<.$0.$0.R2.))P,Pe,(;.(11.&40.)(11.&40.))P,(13.(;.(11.&40.)(11.&40.))R1.R:.)P,(5.R9.(6.(14.R2.)(15.R2.)))P,(5.(14.R3.)(6.R:.(?.(7.R8.)R9.)))(16.(;.$0.$0.)LR,(;.$0.$0.)(4.(13.(;.$0.$0.)R1.R=.)(4.(3.(17.$0.$0.R1.)(14.R5.))(3.(6.(14.R5.)(15.R5.))(6.(17.$0.$0.R1.)(<.$0.$0.R1.))))))P,(5.(18.(;.$0.$0.)(>.R8.R7.(?.(7.R6.)R7.))R9.)(7.R6.))(16.$0.Lj,$0.(4.(4.(3.=R1.)(5.R1.(7.R8.)))(8.$1.(19.R<.(1:.&40.(6.R:.(?.R1.R9.)))(1:.&40.R9.))$9.)))")
(* [comment removed for export] *).
Proof.
  intros maps cover F S J HS HF HB HC COV HSUM.
  (* [comment removed for export] *)
  set (blocked := fun j => existsb (fun R => rblocks F S R j) cover).
  assert (CNT : Z.of_nat (zcount blocked 0 J) <= zsum (rhits F S (Z.of_nat J * S)) cover).
  { subst blocked. clear COV. induction cover as [|R r IH]; cbn [existsb zsum].
    - rewrite zcount_false; [cbn; lia| intros; reflexivity].
    - pose proof (zcount_or (rblocks F S R) (fun j => existsb (fun R0 => rblocks F S R0 j) r) 0 J) as U.
      pose proof (rblocks_count F S J R HS HF (HC R ltac:(now left))) as C1.
      assert (HS' : zsum (rhits F S (Z.of_nat J * S)) r < Z.of_nat J).
      { cbn [zsum] in HSUM. pose proof (rhits_nonneg F S (Z.of_nat J * S) R HS (HC R ltac:(now left))). lia. }
      specialize (IH ltac:(intros R' H'; apply HC; now right) HS'). lia. }
  ddestruct (zcount_lt_exists blocked J 0 ltac:(lia)) as (j & Hj & Bj).
  exists j. split; [lia|].
  apply region_free_intro. intros a sz Hin.
  assert (JS1 : (j + 1) * S <= Z.of_nat J * S) by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (SZ : 0 <= S < 2^64) by lia.
  assert (SL : 0 <= F + j * S < 2^64) by nia.
  pose proof (bv_unsigned_in_range 64 a) as B0. pose proof (bv_unsigned_in_range 64 sz) as B1.
  unfold iv_overlap. rewrite !Z_to_bv_unsigned. rewrite !bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2^64); lia).
  (* [comment removed for export] *)
  destruct (Z.ltb_spec (F + j * S) (bv_unsigned a + bv_unsigned sz)) as [O1|O1]; [| reflexivity].
  destruct (Z.ltb_spec (bv_unsigned a) (F + j * S + S)) as [O2|O2]; [| reflexivity]. exfalso.
  ddestruct (COV (a, sz) Hin ltac:(unfold ebase, elen; cbn [fst snd]; nia) ltac:(unfold ebase; cbn [fst]; nia)) as (R & HR & R1 & R2).
  unfold ebase, elen in R1, R2. cbn [fst snd] in R1, R2.
  assert (X : blocked j = true).
  { subst blocked. apply existsb_exists. exists R. split; [exact HR|]. unfold rblocks, slot. apply andb_true_intro. split; apply Z.ltb_lt; lia. }
  rewrite X in Bj. discriminate.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Corollary free_slot_exists_B : ltac2:(CDefT.buildp (gd_tbl_AFreeSlot ()) "Pmaps,(10.(;.(11.&40.)(11.&40.)))Pcover,(10.(;.$0.$0.))PF,$0.PS,$0.PB,$0.PJ,$2.P,(5.=R3.)P,(3.=R5.)P,(5.(6.R6.(?.(7.R3.)R5.))(12.+2.+40.))P,PR,(;.$0.$0.)P,(13.(;.$0.$0.)R1.R9.)(3.=(<.$0.$0.R2.))P,Pe,(;.(11.&40.)(11.&40.))P,(13.(;.(11.&40.)(11.&40.))R1.R;.)P,(5.R:.(6.(14.R2.)(15.R2.)))P,(5.(14.R3.)(6.R;.(?.(7.R8.)R:.)))(16.(;.$0.$0.)LR,(;.$0.$0.)(4.(13.(;.$0.$0.)R1.R>.)(4.(3.(17.$0.$0.R1.)(14.R5.))(3.(6.(14.R5.)(15.R5.))(6.(17.$0.$0.R1.)(<.$0.$0.R1.))))))P,(3.(18.(;.$0.$0.)(>.R9.R8.(?.(7.R6.)R8.))R:.)R7.)P,(5.R8.(7.R7.))(16.$0.La,$0.(4.(3.R<.R1.)(4.(3.(6.R1.R;.)(6.R<.(?.(7.R9.)R;.)))(4.(8.$0.(1;.(1<.R1.R<.)R;.)=)(8.$1.(19.R>.(1:.&40.R1.)(1:.&40.R;.))$9.)))))")
(* [comment removed for export] *).
Proof.
  intros maps cover F S B J HS HF HB HC COV H1 H2.
  ddestruct (free_slot_exists_cover maps cover F S J HS HF HB HC COV ltac:(lia)) as (j & Hj & RF).
  exists (F + j * S). split; [nia|]. split; [nia|]. split; [| exact RF].
  replace (F + j * S - F) with (j * S) by lia. apply Z_mod_mult.
Qed.

End ARUN_1.
