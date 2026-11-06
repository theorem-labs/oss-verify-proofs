(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import ZBridge CellsX Bytes.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AXRep AXRep2.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition is_ws (b : byte) : bool := (zb b =? 32) || (zb b =? 9).
Fixpoint drop_ws (bs : list byte) : list byte :=
  match bs with [] => [] | b :: bs' => if is_ws b then drop_ws bs' else bs end.
Definition trimB (bs : list byte) : list byte := rev (drop_ws (rev bs)).
Definition trim (bs : list byte) : list byte := trimB (drop_ws bs).

Lemma drop_ws_suffix : forall bs, exists k, drop_ws bs = skipn k bs.
Proof.
  induction bs as [|b bs IH]; [exists 0%nat; reflexivity|]. cbn. destruct (is_ws b).
  - destruct IH as [k E]. exists (S k). exact E.
  - exists 0%nat. reflexivity.
Qed.
Lemma drop_ws_length : forall bs, (length (drop_ws bs) <= length bs)%nat.
Proof. intros bs. destruct (drop_ws_suffix bs) as [k E]. rewrite E, length_skipn. lia. Qed.
Lemma trimB_length : forall bs, (length (trimB bs) <= length bs)%nat.
Proof. intros bs. unfold trimB. rewrite length_rev. pose proof (drop_ws_length (rev bs)) as K. rewrite length_rev in K. lia. Qed.
Lemma trim_length : forall bs, (length (trim bs) <= length bs)%nat.
Proof. intros bs. unfold trim. pose proof (trimB_length (drop_ws bs)). pose proof (drop_ws_length bs). lia. Qed.
Lemma trimB_snoc : forall l b, trimB (l ++ [b]) = if is_ws b then trimB l else l ++ [b].
Proof.
  intros l b. unfold trimB. rewrite rev_app_distr. cbn. destruct (is_ws b); [reflexivity|].
  cbn. rewrite rev_involutive. reflexivity.
Qed.
Lemma trimB_prefix : forall bs, exists k, (k <= length bs)%nat /\ trimB bs = firstn k bs.
Proof.
  induction bs as [|b bs IH] using rev_ind; [exists 0%nat; split; [cbn; lia| reflexivity]|].
  rewrite trimB_snoc, length_app. cbn [length]. destruct (is_ws b).
  - destruct IH as (k & K & E). exists k. split; [lia|]. rewrite firstn_app.
    replace (k - length bs)%nat with 0%nat by lia. cbn. rewrite app_nil_r. exact E.
  - exists (length bs + 1)%nat. split; [lia|]. rewrite firstn_app, firstn_all2 by lia.
    replace (length bs + 1 - length bs)%nat with 1%nat by lia. reflexivity.
Qed.
Lemma firstn_S_snoc : forall {A} (l : list A) k x, nth_error l k = Some x -> firstn (S k) l = firstn k l ++ [x].
Proof.
  intros A l. induction l as [|y l IH]; intros [|k] x H; cbn in *; try discriminate.
  - injection H as ->. reflexivity.
  - f_equal. apply IH. exact H.
Qed.
Lemma is_ws_spec : forall b, is_ws b = true <-> (zb b = 32 \/ zb b = 9).
Proof. ltac2:(KReplay.run [|constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.iff); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.orb); constr:(@Stdlib.ZArith.BinInt.Z.eqb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AXRep.zb); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Classes.Morphisms.trans_co_eq_inv_impl_morphism); constr:(@Corelib.Classes.RelationClasses.iff_Transitive); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Classes.Morphisms.eq_proper_proxy); constr:(@Stdlib.Bool.Bool.orb_true_iff); constr:(@Corelib.Classes.Morphisms_Prop.or_iff_morphism); constr:(@Corelib.Classes.Morphisms.reflexive_proper_proxy); constr:(@Corelib.Classes.Morphisms.reflexive_reflexive_proxy); constr:(@Corelib.Classes.RelationClasses.iff_Reflexive); constr:(@Stdlib.ZArith.BinInt.Z.eqb_eq); constr:(@Corelib.Classes.Morphisms.Reflexive_partial_app_morphism); constr:(@Corelib.Classes.Morphisms.respectful); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.or_ind); constr:(@Corelib.Init.Logic.or_introl); constr:(@Corelib.Init.Logic.or_intror); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.X8_F_trim.is_ws)|] [|@lemma; @B; @H0; @H; @b|] "##k#&#F#&#-###/#5#9#8#3#0#=#<#@#6#,#*#)#4#$#:#;#>#?#B#A#%#E#F#D#C#G#.#+#1#2#7*#A&#B$#/%#C%#$%#D$#E,$P$#$#UQ#UR#(E$&$#UJ#&&#US#+UJ#&)#VK&##F#G#F(G#F&G%$#'&#(S$&#.&$,VK$##F#G#F&G#F&G%$##H*5#H+3%$#VS%C#)CDI*'E$$#j#$0#VS&:7#H?<'6#%+-WS'CDS(XLCD#/ZM1.E00#)CDI0&#--,j#$(#VNs#'s#$#Hs#(B'>#k#%CCXS)CCDDXLCD,6_S*C%D$OM7#96E)CDI/6#665j#$(#VNs#0s#*%4+k###:(S+#H#s#1#H$s#/WS,$#Ej#&A#WS-&%Ej#&B#ZS.s#$s##B%#Ej#',#XS/,,##V0/#V:9#Vs#$s###US0E#F#G'#3m#&#j#(s#E##"). Qed.
Lemma trimB_nonnil : forall bs, trimB bs <> [] -> bs <> [].
Proof. intros bs H ->. apply H. reflexivity. Qed.

Lemma land_neg8 : forall x, 0 <= x -> Z.land x (-8) = x - x mod 8.
Proof.
  intros x Hx. change (-8) with (Z.lnot (Z.ones 3)). rewrite <- Z.ldiff_land.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  change (2^3) with 8. rewrite Zmod_eq by lia. lia.
Qed.
Lemma land_M8 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551608 = x - x mod 8.
Proof.
  intros x Hx. change 18446744073709551608 with (Z.land (Z.ones 64) (-8)).
  rewrite Z.land_assoc, Z.land_ones, Z.mod_small by lia. apply land_neg8. lia.
Qed.
Lemma land_M1 : forall a, 0 <= a < 2^64 -> Z.land a 18446744073709551615 = a.
Proof. intros a Ha. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma land_M1l : forall a, 0 <= a < 2^64 -> Z.land 18446744073709551615 a = a.
Proof. intros a Ha. rewrite Z.land_comm. apply land_M1. exact Ha. Qed.
Lemma land_FFFF : forall a, 0 <= a < 2^16 -> Z.land a 65535 = a.
Proof. intros a Ha. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
(* [comment removed for export] *)
Lemma tc_size_eq : forall name tv, zlength name <= 65533 -> zlength tv <= 65535 ->
  Z.land (Z.land (zlength name + 2 + Z.land (zlength tv) 65535 + 65) 18446744073709551615) 18446744073709551608
  = elem_block_size name tv.
Proof.
  intros name tv HN HV. unfold elem_block_size, zlength in *.
  rewrite land_FFFF, land_M1, land_M8, land_neg8 by lia. reflexivity.
Qed.
Lemma elem_block_size_range : forall name tv,
  zlength name + zlength tv + 60 <= elem_block_size name tv <= zlength name + zlength tv + 67.
Proof. intros name tv. unfold elem_block_size, zlength. rewrite land_neg8 by lia. Z.div_mod_to_equations. lia. Qed.
Lemma elem_block_size_al8 : forall name tv, elem_block_size name tv mod 8 = 0.
Proof. intros name tv. unfold elem_block_size, zlength. rewrite land_neg8 by lia. Z.div_mod_to_equations. lia. Qed.
