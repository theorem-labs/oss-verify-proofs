(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (5 recorded proofs replaced by written proofs (size_to_class_low, S_mod16, kv_class_len and 2 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Malloc MI_Inv MI_Cnt LB_Tables LB_Inv LB_Sum LB_StmtA LB_Raw.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_LB_PCaps () := "K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib4Spec6MI_Cnt6zrangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbI47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00c59OSSVerify5KrLib4Spec8LB_PCaps8stc_lowfC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec6Malloc=size_to_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib4Spec6MI_Cnt@size_to_class_okC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec9LB_Tables2S_C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC59OSSVerify5KrLib4Spec6MI_Cnt5stc_kC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Cnt?size_to_class_kC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z7div_posK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundK47Corelib4Init5Logic3and01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_pos_boundK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib4Spec6MI_Cnt>forallb_zrangeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbI47Corelib4Init5Logic2or00C46Stdlib4Bool4Bool<orb_true_iffC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z6leb_leK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C47Corelib4Init5Logic8eq_ind_rK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega6VarMap1t03C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib4Spec6Malloc>MMAP_THRESHOLDC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01c59OSSVerify5KrLib4Spec8LB_PCaps>stc_low_b_trueC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4Zdiv:Z_mod_multC56Stdlib6ZArith6BinInt1Z8mul_commK46Stdlib9micromega:ZMicromega;ZArithProof03c59OSSVerify5KrLib4Spec8LB_PCaps4lminC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C47Corelib4Init5Logic3notc59OSSVerify5KrLib4Spec8LB_PCapsAsize_to_class_lowC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8LB_PCaps7S_mod16C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC56Stdlib6ZArith6BinInt1Z7div_mulC56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib4Spec9LB_Tables4cmaxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Tables8std_spanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Tables7std_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Tables<tab_basic_okC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1ZBdiv_le_lower_boundK47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbc59OSSVerify5KrLib4Spec8LB_PCaps4PcapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv3PHIC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07c59OSSVerify5KrLib4Spec8LB_PCaps4RBIGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Raw7LBUDGETC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8LB_PCaps;PHI_Pcap_eqC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition stc_lowf (k : Z) : bool := let c := stc_k k in (c =? 0) || (size_class (c - 1) <=? k).
Lemma stc_low_b_true : forallb stc_lowf (zrange 0 8191) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PCaps ()) [] "p;2p;1p;3g0000j26Tg000Jj13Tg000hj22Tg001_j35Tg002;j34Tg002Uj11Tf0#1#1p=0g003:R0g003ZR1'6g004:g004Xg005Sg0061#0#0#0#0#0#0#3'235=401do"). Qed.

Lemma size_to_class_low n : 0 <= n < MMAP_THRESHOLD -> 1 <= size_to_class n -> S_ (size_to_class n - 1) - IB < n.
Proof.
  intros Hn Hc. pose proof (size_to_class_ok n Hn) as [R _]. revert Hc. rewrite size_to_class_k in *. rewrite Z.shiftr_div_pow2 in * by lia.
  unfold IB, UNIT, MMAP_THRESHOLD, S_ in *.
  set (k := (n + 4 - 1) / 2 ^ 4) in *.
  assert (Hk : 0 <= k < 8191) by (subst k; change (2 ^ 4) with 16; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  assert (Hk2 : 16 * k <= n + 3 < 16 * k + 16) by (subst k; change (2 ^ 4) with 16; pose proof (Z.div_mod (n + 4 - 1) 16 ltac:(lia)); pose proof (Z.mod_pos_bound (n + 4 - 1) 16 ltac:(lia)); lia).
  pose proof (forallb_zrange stc_lowf 0 8191 k stc_low_b_true ltac:(lia) ltac:(lia)) as H. unfold stc_lowf in H. cbn zeta in H.
  intros Hc. apply Bool.orb_true_iff in H as [H|H]; [apply Z.eqb_eq in H; lia|]. apply Z.leb_le in H. unfold UNIT. lia.
Qed.

(* [comment removed for export] *)
Definition lmin (c : Z) : Z := if c =? 0 then 0 else (S_ (c - 1) - IB) / 4.

Lemma S_mod16 : forall c, 0 <= c < 48 -> S_ c mod 16 = 0.
Proof. intros c Hc. unfold S_, UNIT. rewrite Z.mul_comm. apply Z_mod_mult. Qed.

Lemma kv_class_len : forall len, 0 <= len -> 4 * (len + 1) < MMAP_THRESHOLD ->
  let c := size_to_class (4 * (len + 1)) in 0 <= c < 48 /\ lmin c <= len.
Proof.
  intros len Hlen Hsmall c. pose proof (size_to_class_ok (4 * (len + 1)) ltac:(lia)) as [R _]. fold c in R. split; [exact R|].
  unfold lmin. destruct (Z.eqb_spec c 0) as [E|NE]; [lia|].
  pose proof (size_to_class_low (4 * (len + 1)) ltac:(lia) ltac:(fold c; lia)) as L. fold c in L.
  pose proof (S_mod16 (c - 1) ltac:(lia)) as M. unfold IB in *.
  pose proof (Z.div_mod (S_ (c - 1)) 16 ltac:(lia)) as D. rewrite M, Z.add_0_r in D.
  set (t := S_ (c - 1) / 16) in *. rewrite D. replace (16 * t - 4) with (4 * (4 * t - 1)) by lia.
  rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

Lemma lmin_pos : forall c, 1 <= c < 48 -> 3 <= lmin c.
Proof.
  intros c Hc. unfold lmin. replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  pose proof (proj1 (tab_basic_ok (c - 1) ltac:(lia))). unfold IB. apply Z.div_le_lower_bound; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition W : Z := 2^24 + 1.
Definition AMBC : Z := 8.
(* [comment removed for export] *)
Lemma stc_24 : size_to_class 24 = 1.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PCaps ()) [] "p;1p;2g000Jj11Tg0000j20Tg004:g0061#1'0o"). Qed.

Definition kvcap (c : Z) : Z := if c =? 0 then 3 * W else W / lmin c.
(* [comment removed for export] *)
Definition Pcap (c : Z) : Z :=
  if c =? 63 then AMBC
  else if (0 <=? c) && (c <? 48) then AMBC
  else 0.

Lemma Pcap_nonneg : forall c, 0 <= Pcap c.
Proof.
  intros c. unfold Pcap, AMBC.
  destruct (c =? 63); [lia|]. destruct ((0 <=? c) && (c <? 48)); lia.
Qed.

(* [comment removed for export] *)
Definition RBIG : Z := 3 * (2^26 + 8192) + 5 * W + (24 * 2^24 + 8192).

Lemma PHI_Pcap_eq : PHI Pcap = 231057408.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PCaps ()) [] "p;1p;2p;3g002Uj10Tg0091j11Tg000Jj13Tg0000j26Tg016>j15Tg002;j34Tf0#1#1p=2g004:R0g0061#0#1#0#0#0#1#2#0#1#0#0#1#0#1#0#1#2#2#2#2#2#3R1'6g015G#5=401do"). Qed.

Lemma PHI_Pcap : PHI Pcap + RBIG <= LBUDGET.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PCaps ()) [] "h07__arithh14__ffh28__varmaph35__with41zp;1p;2p;3p;4p;7p;6g002Uj11Tg0091j10Tg000Jj12Tg00Llj23Tg007Tj29Tg00?kj1DTg00@Kj1BTg00@kj1ATg00AIj1@Tg00Agj1>Tg0172j1=Tg017Pj3<Tg00I@j3:Tg00H<j3PTg00XUj4OTg00Y@j7NTg00C5j2MTg0000j2KTg00CWj2CTg002;j3ETg00DCj3FTg00Dbj4GTg00?1j27Tg00Icj28Tg00:lj2HTg016>j1ITg00X7j6JTg00BRj2?Tg00Zlj3LTf0R0#0#0p=;%00#0#0#0p=6g004:R1/?0p=4f1R2=L10p=5P1g0061R3#1R4#0R5#1R6#1#1#0#;#1#0#1#1#0#1#0#1#0#;#6#6#2R7g0183R8,30g018jR9'9X41g00blR:#D%B:%A1%@1%>1R:g00^9g00^XR;P;g00_8R;P1%47%24R<#4%03R=#2R>#4R?%06R6#=5<1R@%6=#6#6#2RA#4RB'55:1%1=#2R=#4%;5R5#=9<1?RC%23R3#4'55:1'5%25R5#4=:1C/5B'5'5g00_X%14#1#1R4#=9<1?=P1@COg00`?FN1M:;P0f2R;g003:R:g003ZR@'K1C0;=E:@dg005S=F12CGb1b2b3%26,7>R6/3A,8<17>5R</33,8='3185</3A'3,37%24,7>/H6'9R6P0b0P6e1378/99eg015G#Ig019bEJo"). Qed.
