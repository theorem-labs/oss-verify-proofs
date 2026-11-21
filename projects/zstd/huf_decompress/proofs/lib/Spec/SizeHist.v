(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (14 recorded proofs replaced by written proofs (bcs_kv, bcs_nonneg, BCs_nonneg and 11 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import MI_Inv LB_Inv LB_Sum.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_SizeHist () := "C47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C47Corelib4Init9Datatypes3appI47Corelib4Init9Datatypes4list00c59OSSVerify5KrLib4Spec8SizeHist3bcsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8SizeHist3BCsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init5Logic2eq01I47Corelib7Numbers7BinNums1Z00C46Stdlib5Lists4List7map_appC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec6MI_Inv4zsumC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib4Spec6LB_Sum8zsum_appC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib4Spec6LB_Inv6zcountC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib4Spec6LB_Sum;zcount_consC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8SizeHist4N24sC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01c59OSSVerify5KrLib4Spec8SizeHist3N4sC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Sum:zcount_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Sum=zcount_nonnegC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic3notK46Stdlib9micromega=RingMicromega5Psatz07K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes:comparison00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203c59OSSVerify5KrLib4Spec8SizeHist6itemszC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00c59OSSVerify5KrLib4Spec8SizeHist6bcs_kvC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00c59OSSVerify5KrLib4Spec8SizeHist6bcs_24C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8SizeHist3YWsC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List?Forall_cons_iffc59OSSVerify5KrLib4Spec8SizeHist:bcs_nonnegC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8SizeHist8BCs_consC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indI46Stdlib5Lists4List6Exists00C46Stdlib5Lists4List:Forall_appC47Corelib4Init5Logic3iffI46Stdlib7Sorting;Permutation;Permutation00C46Stdlib5Lists4List2InC47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms5flip2C46Stdlib5Lists4List=Forall_forallC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib7Sorting;Permutation?Permutation_symC46Stdlib7Sorting;Permutation>Permutation_inC47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC59OSSVerify5KrLib4Spec6LB_Sum=zsum_map_permC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Sum;zcount_permC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Peano2le00K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01c59OSSVerify5KrLib4Spec8SizeHist2HBC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationBPermutation_middleC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revc59OSSVerify5KrLib4Spec8SizeHist<HISTOK_introC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_leC46Stdlib7Sorting;Permutation@Permutation_reflK47Corelib4Init5Peano2le02C46Stdlib5Lists4List:fold_rightC59OSSVerify5KrLib4Spec6LB_Sum:zcount_nilC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8SizeHist9N24s_consC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8SizeHist8N4s_consC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv4zlenC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8SizeHist6HISTOKC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC59OSSVerify5KrLib4Spec6LB_Sum=zcount_le_lenC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8SizeHist9zlen_le_4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8SizeHist@zcount_items_linC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8leb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z8ltb_specK47Corelib4Init9Datatypes4bool02C56Stdlib6ZArith6BinInt1Z6leb_gtC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1ZBdiv_le_lower_boundC56Stdlib6ZArith6BinInt1Z3powC47Corelib4Init5Logic5proj1C59OSSVerify5KrLib4Spec6LB_Sum;zsum_map_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Sum<zsum_map_mulC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C46Stdlib5Lists4List9in_or_appK47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib4Spec6LB_Sum>zsum_map_constC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Sum;zlen_nonnegC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegI47Corelib4Init5Logic4True00C46Stdlib5Lists4List6filterc59OSSVerify5KrLib4Spec8SizeHist>HISTOK_big_sumC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Sum?zsum_map_filterC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6map_id".
Import ListNotations.
Open Scope Z_scope.

Definition itemsz (z : Z) : Prop := z = 24 \/ exists l, 0 <= l /\ z = 4 * (l + 1).
Definition YWs (L : list Z) : Prop := Forall itemsz L.
Definition bcs (z : Z) : Z := if z =? 24 then 1 else z / 4 - 1.
Definition BCs (L : list Z) : Z := zsum (map bcs L).
Definition N24s (L : list Z) : Z := zcount (fun z => z =? 24) L.
Definition N4s (L : list Z) : Z := zcount (fun z => z =? 4) L.

(* [comment removed for export] *)
Definition HB : Z := 2^24 + 2.

Definition HISTOK (M : list Z) : Prop :=
  exists I Z, Permutation M (I ++ Z) /\ YWs I /\ BCs I <= HB /\ N4s I <= 2 * N24s I + 2 /\ (length Z <= 4)%nat.

Lemma BCs_cons z L : BCs (z :: L) = bcs z + BCs L.
Proof.
ltac2:(KReplay.run1 (kr_t_SizeHist ()) [] "h01Lh11zp;1p;2p-1R0p10000p4p710p9P0p1000\R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001:p4p710p9P0p10022p4p710p8g002Oj14Tg002oj13Tg003ej10Tg004[j21Tg0058j22Tg005RR0%40R1f1R2#3f0R3#0'1,20X01X10P2P3O2W0W1o"). Qed.
Lemma BCs_app L1 L2 : BCs (L1 ++ L2) = BCs L1 + BCs L2.
Proof.
ltac2:(KReplay.run1 (kr_t_SizeHist ()) [] "h02L1h12L2h21lh31zp;1p;3p;2p;6p;5p;4g0060R0p4p7210g006LR1p4p710p8g002Oj1;Tg0022j36Tg006jj10Tg004[j24Tg007_j33Tg0058j2:Tg0089j29TP1j65TP0j58Tg003ej12Tg0092j47Tg005RR0P0g002oR1f0R2C7p=1%;0R3P3f1R4#1R5%12R6560R7%02f2#1#0%05R8'4R9530X23P0%06,48R8A3029X301:08%071956E5A6042R6#1P0P0P1P4P2D8E5%26%24%22'4530eX13X03P4P2O2X13W0o"). Qed.
Lemma N24s_cons z L : N24s (z :: L) = (if z =? 24 then 1 else 0) + N24s L.
Proof.
ltac2:(KReplay.run1 (kr_t_SizeHist ()) [] "h01zh11Lp;1p;2p;3p;4p;6g002Oj1<Tg009Nj1;Tg00:3j11Tg00:Xj15Tg00;6j23Tg00;Sj30Tg004[j22Tg007_j34Tg0058j2:Tg00<Jj39Tg00<jj47Tg006Lj68Tg00=fj16Tg005RR0%<0R1P0g00>]R2P0f1R3g00?=R4#;#1#1#1#5R5'3%54R4g00?bR6n0100000020000R7f0R8/35X00R9=008'2R:P2P0f2/35P4P6n0100000020000A0093'29408X001:0:A9038R:9009P0P9P3P8C7E8%6:%68,27540eX11X00P3P8O2W1W0o"). Qed.
Lemma N4s_cons z L : N4s (z :: L) = (if z =? 4 then 1 else 0) + N4s L.
Proof.
ltac2:(KReplay.run1 (kr_t_SizeHist ()) [] "h01zh11Lp;1p;2p;3p;4p;6g002Oj1;Tg00:3j16Tg00:Xj14Tg00;6j21Tg00;Sj32Tg004[j20Tg007_j35Tg0058j2:Tg00<Jj39Tg00<jj48Tg006Lj67Tg00@@j13Tg005RR0%;0R1P0g00>]R2P0f1R3g00?=R4#6#6#4R5'1%44R4g00?bR6n0100000020000R7f0R8/15X00R9=208'0R:P2P0f2/15P4P6n0100000020000A2093'09508X001:0:A9038R:9209P0P9P3P8C8E7%3:%38,07550eX11X00P3P8O2W1W0o"). Qed.
Lemma N24s_app L1 L2 : N24s (L1 ++ L2) = N24s L1 + N24s L2.
Proof.
ltac2:(KReplay.run1 (kr_t_SizeHist ()) [] "h02L1h12L2h21zp;1p;2p;4p;3g002Oj19Tg009Nj18Tg00:3j11Tg00:Xj12Tg00;6j27Tg00A6j45Tg0022j34Tg00=fj10Tg004[j23Tg007_j36Tg005RR0#9R1P0f0R2g00?=#8#1#1#1#2'7X20f1R3P2C5A4032#0%03%02'3560eX11X01P3P2O2X11W0o"). Qed.
Lemma N4s_app L1 L2 : N4s (L1 ++ L2) = N4s L1 + N4s L2.
Proof.
ltac2:(KReplay.run1 (kr_t_SizeHist ()) [] "h02L1h12L2h21zp;1p;2p;4p;3g002Oj18Tg00:3j11Tg00:Xj13Tg00;6j22Tg00A6j47Tg0022j36Tg00@@j10Tg004[j24Tg007_j35Tg005RR0#8R1P0f0R2g00?=#1#1#3'2X20f1R3P2C7A6032#0%03%02'4550eX11X01P3P2O2X11W0o"). Qed.
Lemma N24s_nonneg L : 0 <= N24s L.
Proof.
ltac2:(KReplay.run1 (kr_t_SizeHist ()) [] "h01Lh11zp;1p;2p;3g002Oj17Tg009Nj16Tg00:3j10Tg00:Xj11Tg00;6j25Tg00B1j34Tg00=fj13Tg00Boj22Tg005RR0#7R1f0R2g00?=#6#0#0#0#1'5X10=402g00?b%32'2eX01P2O1W0o"). Qed.
Lemma N4s_nonneg L : 0 <= N4s L.
Proof.
ltac2:(KReplay.run1 (kr_t_SizeHist ()) [] "h01Lh11zp;1p;2p;3g002Oj16Tg00:3j10Tg00:Xj12Tg00;6j21Tg00B1j35Tg00@@j14Tg00Boj23Tg005RR0#6R1f0R2g00?=#0#0#2'1X10=502g00?b%42'3eX01P2O1W0o"). Qed.
Lemma bcs_kv l : 0 <= l -> bcs (4 * (l + 1)) = (if l =? 5 then 1 else l).
Proof. intros Hl. unfold bcs. destruct (Z.eqb_spec (4 * (l + 1)) 24); destruct (Z.eqb_spec l 5); lia. Qed.
Lemma bcs_24 : bcs 24 = 1.
Proof.
ltac2:(KReplay.run1 (kr_t_SizeHist ()) [] "p;1p;2g00:Xj11Tg0058j20Tg005Rg00?=#1'0o"). Qed.
Lemma bcs_nonneg z : itemsz z -> 0 <= bcs z.
Proof. intros [->|(l & Hl & ->)]; [rewrite bcs_24; lia| rewrite bcs_kv by lia; destruct (l =? 5); lia]. Qed.
Lemma BCs_nonneg L : YWs L -> 0 <= BCs L.
Proof. induction L as [|z L IH]; intros HW; [cbn; unfold BCs, zsum; cbn; lia|]. apply Forall_cons_iff in HW as [Hz HW]. rewrite BCs_cons. pose proof (bcs_nonneg z Hz). specialize (IH HW). lia. Qed.
Lemma YWs_app L1 L2 : YWs (L1 ++ L2) <-> YWs L1 /\ YWs L2.
Proof.
ltac2:(KReplay.run1 (kr_t_SizeHist ()) [] "h02L1h12L2p;1p;4p;3p;2g002Oj15Tg00o0j44Tg0022j31Tg00j>j10Tg00Tij23Tg00oOj22Tg005RR0#5R1P0g00f_f1R2f0R3C4A1023#0%02%03'3'2eX11X01P2P3O2X11W0o"). Qed.
Lemma YWs_perm L1 L2 : Permutation L1 L2 -> YWs L1 -> YWs L2.
Proof. intros HP HW. unfold YWs in *. rewrite Forall_forall in *. intros z Hz. apply HW. eapply Permutation_in; [apply Permutation_sym; exact HP| exact Hz]. Qed.
Lemma BCs_perm L1 L2 : Permutation L1 L2 -> BCs L1 = BCs L2.
Proof.
ltac2:(KReplay.run1 (kr_t_SizeHist ()) [] "h02L1h12L2h22HPp;1p;3p;5g002Oj14Tg00ohj33Tg015Lj51Tg003ej10Tg007_j32Tg005RR0#4R1f1R2f0R3530P0g002of2R4P2P3D1%04%02520eW2X11X01P2P3O2X11W0o"). Qed.
Lemma N24s_perm L1 L2 : Permutation L1 L2 -> N24s L1 = N24s L2.
Proof.
ltac2:(KReplay.run1 (kr_t_SizeHist ()) [] "h02L1h12L2h22HPh31zp;1p;3p;2p;5g002Oj18Tg00ohj37Tg009Nj12Tg00:3j10Tg00:Xj16Tg00;6j24Tg016Jj53Tg00=fj11Tg007_j35Tg005RR0#8R1f1R2f0R3570P0g00?=#2#0#0#0#6,43X30f2R4P2P3D3%14%12550eW2X11X01P2P3O2X11W0o"). Qed.
Lemma N4s_perm L1 L2 : Permutation L1 L2 -> N4s L1 = N4s L2.
Proof.
ltac2:(KReplay.run1 (kr_t_SizeHist ()) [] "h02L1h12L2h22HPh31zp;1p;3p;2p;5g002Oj17Tg00ohj36Tg00:3j11Tg00:Xj12Tg00;6j25Tg016Jj54Tg00@@j10Tg007_j33Tg005RR0#7R1f1R2f0R3560P0g00?=#1#1#2,53X30f2R4P2P3D4%04%02530eW2X11X01P2P3O2X11W0o"). Qed.

(* [comment removed for export] *)
Lemma HISTOK_intro I Z M : Permutation M (I ++ Z) -> YWs I -> BCs I <= HB -> N4s I <= 2 * N24s I + 2 -> (length Z <= 4)%nat -> HISTOK M.
Proof. intros. exists I, Z. repeat split; assumption. Qed.

(* [comment removed for export] *)
Lemma HISTOK_amb n I Z : YWs I -> BCs I <= HB -> N4s I <= 2 * N24s I + 2 -> (length Z <= 3)%nat -> HISTOK (n :: I ++ Z).
Proof.
  intros HW HB0 H42 HL. apply (HISTOK_intro I (n :: Z)); auto; [| cbn; lia].
  apply Permutation_middle.
Qed.

(* [comment removed for export] *)
Lemma HISTOK_item n I Z : YWs (n :: I) -> BCs (n :: I) <= HB -> N4s (n :: I) <= 2 * N24s (n :: I) + 2 -> (length Z <= 3)%nat -> HISTOK (n :: I ++ Z).
Proof. intros HW HB0 H42 HL. apply (HISTOK_intro (n :: I) Z); auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma zcount_items_lin (f : Z -> bool) (a b c : Z) I : YWs I ->
  (forall z, itemsz z -> (if f z then 1 else 0) <= a * (if z =? 4 then 1 else 0) + b * bcs z + c * (if z =? 24 then 1 else 0)) ->
  zcount f I <= a * N4s I + b * BCs I + c * N24s I.
Proof.
  induction I as [|z I IH]; intros HW Hf.
  - unfold N4s, N24s, BCs, zsum. rewrite !zcount_nil. cbn. lia.
  - apply Forall_cons_iff in HW as [Hz HW]. rewrite zcount_cons, N4s_cons, BCs_cons, N24s_cons.
    specialize (IH HW Hf). specialize (Hf z Hz). lia.
Qed.

Lemma zlen_le_4 {A} (Z : list A) : (length Z <= 4)%nat -> zlen Z <= 4.
Proof. unfold zlen. lia. Qed.

(* [comment removed for export] *)
Lemma HISTOK_small M : HISTOK M -> zcount (fun z => z <=? 16) M <= 2 * HB + 6.
Proof.
  intros (I & Z & HP & HW & HBC & H42 & HL). rewrite (zcount_perm _ _ _ HP), zcount_app.
  pose proof (zcount_le_len (fun z => z <=? 16) Z). pose proof (zlen_le_4 Z HL).
  pose proof (zcount_items_lin (fun z => z <=? 16) 1 1 (-1) I HW) as HI.
  assert (N24 : N24s I <= BCs I).
  { pose proof (zcount_items_lin (fun z => z =? 24) 0 1 0 I HW) as H24. unfold N24s at 1.
    enough (E : forall z, itemsz z -> (if z =? 24 then 1 else 0) <= 0 * (if z =? 4 then 1 else 0) + 1 * bcs z + 0 * (if z =? 24 then 1 else 0)) by (specialize (H24 E); lia).
    intros z [->|(l & Hl & ->)]; [rewrite bcs_24; cbn; lia|]. rewrite bcs_kv by lia.
    destruct (Z.eqb_spec (4 * (l + 1)) 24); destruct (Z.eqb_spec l 5); lia. }
  enough (E : forall z, itemsz z -> (if z <=? 16 then 1 else 0) <= 1 * (if z =? 4 then 1 else 0) + 1 * bcs z + (-1) * (if z =? 24 then 1 else 0)) by (specialize (HI E); lia).
  intros z [->|(l & Hl & ->)]; [rewrite bcs_24; cbn; lia|]. rewrite bcs_kv by lia.
  destruct (Z.leb_spec (4 * (l + 1)) 16); destruct (Z.eqb_spec (4 * (l + 1)) 4); destruct (Z.eqb_spec (4 * (l + 1)) 24); destruct (Z.eqb_spec l 5); lia.
Qed.

(* [comment removed for export] *)
Lemma HISTOK_mid M : HISTOK M -> zcount (fun z => (16 <? z) && (z <=? 48)) M <= HB + 4.
Proof.
  intros (I & Z & HP & HW & HBC & H42 & HL). rewrite (zcount_perm _ _ _ HP), zcount_app.
  pose proof (zcount_le_len (fun z => (16 <? z) && (z <=? 48)) Z). pose proof (zlen_le_4 Z HL).
  pose proof (zcount_items_lin (fun z => (16 <? z) && (z <=? 48)) 0 1 0 I HW) as HI.
  enough (E : forall z, itemsz z -> (if (16 <? z) && (z <=? 48) then 1 else 0) <= 0 * (if z =? 4 then 1 else 0) + 1 * bcs z + 0 * (if z =? 24 then 1 else 0)) by (specialize (HI E); lia).
  intros z [->|(l & Hl & ->)]; [rewrite bcs_24; cbn; lia|]. rewrite bcs_kv by lia.
  destruct (Z.ltb_spec 16 (4 * (l + 1))); destruct (Z.leb_spec (4 * (l + 1)) 48); destruct (Z.eqb_spec l 5); cbn [andb]; lia.
Qed.

(* [comment removed for export] *)
Lemma HISTOK_large M : HISTOK M -> forall m, 6 <= m -> zcount (fun z => 4 * (m + 1) <=? z) M <= HB / m + 4.
Proof.
  intros (I & Z & HP & HW & HBC & H42 & HL) m Hm. rewrite (zcount_perm _ _ _ HP), zcount_app.
  pose proof (zcount_le_len (fun z => 4 * (m + 1) <=? z) Z). pose proof (zlen_le_4 Z HL).
  enough (HI : zcount (fun z => 4 * (m + 1) <=? z) I <= HB / m) by lia.
  apply Z.div_le_lower_bound; [lia|].
  pose proof (zcount_items_lin (fun z => 4 * (m + 1) <=? z) 0 1 0 I HW) as HI.
  enough (E : forall I', YWs I' -> m * zcount (fun z => 4 * (m + 1) <=? z) I' <= BCs I').
  { specialize (E I HW). lia. }
  clear - Hm. induction I' as [|z I' IH]; intros HW'.
  - rewrite zcount_nil. unfold BCs, zsum. cbn -[Z.mul]. lia.
  - apply Forall_cons_iff in HW' as [Hz HW']. rewrite zcount_cons, BCs_cons. specialize (IH HW').
    destruct Hz as [->|(l & Hl & ->)]; [rewrite bcs_24; replace (4 * (m + 1) <=? 24) with false by (symmetry; apply Z.leb_gt; lia); lia|].
    rewrite bcs_kv by lia. destruct (Z.leb_spec (4 * (m + 1)) (4 * (l + 1))); destruct (Z.eqb_spec l 5); lia.
Qed.

(* [comment removed for export] *)
Lemma HISTOK_big_sum M : HISTOK M -> Forall (fun z => 0 <= z <= 2^30) M ->
  zsum (map (fun z => if 64512 <? z then z else 0) M) <= 5 * HB + 4 * 2^30.
Proof.
  intros (I & Z & HP & HW & HBC & H42 & HL) HF.
  rewrite (zsum_map_perm _ _ _ HP), map_app, zsum_app.
  assert (HI : zsum (map (fun z => if 64512 <? z then z else 0) I) <= 5 * BCs I).
  { unfold BCs. rewrite <- (zsum_map_mul 5 bcs I). apply zsum_map_le. intros z Hz.
    pose proof (proj1 (Forall_forall _ _) HW z Hz) as [->|(l & Hl & ->)]; [rewrite bcs_24; cbn; lia|].
    rewrite bcs_kv by lia. destruct (Z.ltb_spec 64512 (4 * (l + 1))); destruct (Z.eqb_spec l 5); lia. }
  assert (HZ : zsum (map (fun z => if 64512 <? z then z else 0) Z) <= 2^30 * zlen Z).
  { rewrite <- (zsum_map_const (2^30) Z). apply zsum_map_le. intros z Hz.
    assert (Hin : In z M) by (eapply Permutation_in; [apply Permutation_sym; exact HP| apply in_or_app; right; exact Hz]).
    pose proof (proj1 (Forall_forall _ _) HF z Hin) as Hb. cbn beta in Hb. destruct (64512 <? z); lia. }
  pose proof (zlen_le_4 Z HL). pose proof (zlen_nonneg Z). nia.
Qed.

Lemma HISTOK_big_sum' M : HISTOK M -> Forall (fun z => 0 <= z <= 2^30) M ->
  zsum (filter (fun z => 64512 <? z) M) <= 5 * HB + 4 * 2^30.
Proof.
  intros H1 H2. rewrite <- (map_id (filter _ M)). rewrite (zsum_map_filter (fun z => 64512 <? z) (fun z => z) M). exact (HISTOK_big_sum M H1 H2).
Qed.
