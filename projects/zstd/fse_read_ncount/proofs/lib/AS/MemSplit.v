(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (adds wok_lo (sp - stack_max_size + stack_window_reach) with win_lo_le_wok_lo, in_win (wok_lo up to sp) and wfJ; adds stack_zero with wfJ_stack_zero and stack_zero_in_win: under valid_launch and entry_launch_ok_va the window is zero from stack_window_lo up). *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import PropExec CatExec SeqExec StepTac StoreOk StreamSim.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Lemma wbytes_inside : forall bs m (a x : word),
bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs) ->
wbytes m a bs x = Some (nth (Z.to_nat (bv_unsigned x - bv_unsigned a)) bs (Z_to_bv 8 0)).
Proof.
induction bs as [|b rest IH]; intros m a x Hnw Hx; [cbn in Hx; lia|].
cbn [wbytes length] in *.
destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
- assert (x = a) by (apply bv_eq; exact Heq). subst x.
rewrite Z.sub_diag. cbn [Z.to_nat nth].
destruct rest as [|b' rest'].
+ cbn [wbytes]. rewrite bv_eqb_refl. reflexivity.
+ cbn [length] in Hnw. rewrite wbytes_below.
* rewrite bv_eqb_refl. reflexivity.
* rewrite u_add1 by lia. cbn [length]. lia.
* rewrite u_add1 by lia. lia.
- assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1)
by (apply u_add1; lia).
rewrite (IH _ (a + 1)%bv) by (rewrite Hu1; lia).
rewrite Hu1.
replace (Z.to_nat (bv_unsigned x - bv_unsigned a))
with (S (Z.to_nat (bv_unsigned x - (bv_unsigned a + 1)))) by lia.
reflexivity.
Qed.
Lemma wbytes_outside : forall bs m (a x : word),
bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
(bv_unsigned x < bv_unsigned a \/ bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned x) ->
wbytes m a bs x = m x.
Proof.
intros bs m a x Hnw [Hlt|Hge].
- apply wbytes_below; assumption.
- apply wbytes_above; assumption.
Qed.
Definition win_lo (sp0 : word) : Z := bv_unsigned sp0 - stack_max_size.
Definition wok_lo (sp0 : word) : Z :=
  bv_unsigned sp0 + stack_window_reach - stack_max_size.
Definition in_win (sp0 : word) (x : word) : Prop :=
  wok_lo sp0 <= bv_unsigned x < bv_unsigned sp0.

Lemma win_lo_le_wok_lo : forall sp0, win_lo sp0 <= wok_lo sp0.
Proof. intros. unfold win_lo, wok_lo, stack_window_reach. lia. Qed.

Definition cmem (sp0 : word) (mem0 J D : word -> option byte) : word -> option byte :=
fun a => if (bv_unsigned sp0 <=? bv_unsigned a) then mem0 a
else if (win_lo sp0 <=? bv_unsigned a) then J a else D a.
Definition wfJ (sp0 : word) (J : word -> option byte) : Prop :=
  forall x : word, in_win sp0 x -> J x <> None.
(* [stack_zero] and its two lemmas sat INSIDE [Section CMem], under that section's
   [Variable sp0], so their own [forall ... sp0 ...] shadowed it and [intros] reads
   "sp0 is already used" (:72, measured).  They do not use the section's
   variables.  zstd/simple_decompress AS/MemSplit.v states all three BEFORE
   [Section CMem] (:151, :154, :165) and compiled there.  Moved here verbatim; the
   statements and proofs are unchanged. *)
Definition stack_zero (lo : Z) : word -> option byte :=
  fun x => if lo <=? bv_unsigned x then Some (Z_to_bv 8 0) else None.

Lemma wfJ_stack_zero : forall inp (sp0 brk0 mbase : word) (rdraw : EntryDraw),
  valid_launch inp ->
  entry_launch_ok_va Sv48 (mkEntry sp0 brk0 mbase rdraw) inp ->
  wfJ sp0 (stack_zero (stack_window_lo (in_kernel inp) mbase rdraw)).
Proof.
  intros inp sp0 brk0 mbase rdraw Hvl Hlau x Hx. unfold in_win, wok_lo in Hx.
  pose proof (stack_window_lo_valid inp sp0 brk0 mbase rdraw Hvl Hlau).
  unfold stack_zero. rewrite (proj2 (Z.leb_le _ _)) by lia. discriminate.
Qed.

Lemma stack_zero_in_win :
  forall inp (sp0 brk0 mbase : word) (rdraw : EntryDraw) (x : word),
  valid_launch inp ->
  entry_launch_ok_va Sv48 (mkEntry sp0 brk0 mbase rdraw) inp ->
  in_win sp0 x ->
  stack_zero (stack_window_lo (in_kernel inp) mbase rdraw) x
  = Some (Z_to_bv 8 0).
Proof.
  intros inp sp0 brk0 mbase rdraw x Hvl Hlau Hx. unfold in_win, wok_lo in Hx.
  pose proof (stack_window_lo_valid inp sp0 brk0 mbase rdraw Hvl Hlau).
  unfold stack_zero. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
Qed.

Section CMem.
Variable sp0 : word.
Variable mem0 : word -> option byte.
Let csel := cmem sp0 mem0.

End CMem.
