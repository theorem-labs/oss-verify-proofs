(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0p YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI03 YI04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YG0e YCcz YCd0.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI08 YI0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCe9 YCfx YChv YChx YChn YCf6 YCft YCey YCe4 YCi1 YCrr YCib YCrn YCrm YCrt YCrs YCru YCro YCrb YChy.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac rfb_chain HS HJn Hch1 :=
match goal with
| HCH : achain ?lyc (aview trbsegs (w_H ?W) ?memc) (?st + 24) (s0Z ?regs) ?ch, HKEPT : rfc_kept ?W ?memc ?W3 ?mN _ _ _ _ ?st _,
Hly : layout_le _ ?ly ?lyc, Hstk : astk_ok _ ?ly _, Usp : bv_unsigned (ew _ 2) = spZ ?regs, Hsp1 : _ <= ?sp1 <= spZ ?regs - 160 |- _ =>
lazymatch type of HJn with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyN _ _ _ _ _ =>
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let Qra := fresh "Qra" in let Qs0 := fresh "Qs0" in let HRstk := fresh "HRstk" in let Vra := fresh "Vra" in let Vs0 := fresh "Vs0" in
let Etop3 := fresh "Etop3" in let Etopc := fresh "Etopc" in let UPk := fresh "UPk" in let Htop := fresh "Htop" in let Htop2 := fresh "Htop2" in
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq);
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq);
pose proof Hstk as (_ & _ & _ & _ & _ & _ & _ & Htop & Htop2);
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_baseA rs 2%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch goal with AG : forall n, (n < 33)%nat -> ew _ n = ew ?E0 n, EE : forall n (r : bv 5), _ -> ew ?E0 n = getr regs r |- _ =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
ltac:(exact Usp) ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Qra) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
ltac:(exact Usp) ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Qs0) ltac:(cbn; lia)) as Vs0 end end;
clear HRstk;
change (N.to_nat 8) with 8%nat in Vra, Vs0;
replace (spZ regs + -8) with (spZ regs - 8) in Vra by (clear; lia); replace (spZ regs + -16) with (spZ regs - 16) in Vs0 by (clear; lia);
assert (Etop3 : ly_top lyN = ly_top lyc)
by (let T3 := fresh "T3" in let Tc := fresh "Tc" in
destruct (proj1 (proj2 HJn)) as (_ & _ & _ & _ & _ & _ & _ & _ & T3 & _); destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Tc & _); rewrite T3, Tc; reflexivity);
assert (Etopc : ly_top lyc = ly_top ly) by (let Tc := fresh "Tc" in destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Tc & _); exact Tc);
assert (UPk : forall a, st + 24 <= a < 2 ^ 64 -> aview trbsegs (w_H W3) (ms_mem msX) a = aview trbsegs (w_H W) memc a)
by (let a := fresh "a" in let Ha := fresh "Ha" in let K1 := fresh "K1" in intros a Ha; destruct HKEPT as (K1 & _); apply K1; lia);
assert (Hch1 : achain lyN (aview trbsegs (w_H W3) (ms_mem msX)) sp1 (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch))
by (apply (rf_chain_push lyc lyN (aview trbsegs (w_H W) memc) (aview trbsegs (w_H W3) (ms_mem msX)) st (spZ regs) (s0Z regs) (raZ regs) ch sp1 HCH Etop3);
[ rewrite Etopc; lia | exact UPk | lia
| exact (rdword_of_val_mem trbsegs _ _ _ _ Vra Qra) | exact (rdword_of_val_mem trbsegs _ _ _ _ Vs0 Qs0) | assumption
| lia
| lazymatch goal with Hal16 : spZ regs mod 16 = 0 |- _ =>
let D := fresh "D" in pose proof (Z.div_mod (spZ regs) 16 ltac:(clear; lia)) as D; rewrite Hal16, Z.add_0_r in D; rewrite D;
replace (16 * (spZ regs / 16)) with ((2 * (spZ regs / 16)) * 8) by (clear; lia); apply Z_mod_mult end
| rewrite Etopc; lia
| lia ]);
clear Vra Vs0 UPk Etop3 Etopc Qra Qs0 Htop Htop2
end end end.
