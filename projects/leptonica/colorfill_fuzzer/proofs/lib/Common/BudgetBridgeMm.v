(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem Require Import Sys.SyscallTable.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require Import BudgetBridgeCore BudgetBridgeTac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib Require TCodec.
Ltac2 tcn__Common_BudgetBridgeMm () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mremap."; "OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.BudgetBridgeCore."; "OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.BudgetBridgeMm."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1O"; "1bool"; "1false"; "1list"; "1prod"; "1true"; "2eq"; "3Z"; "0L"; "4Model"; "4SyscallEffect"; "4SyscallInput"; "4VmMaps"; "4alloc_top"; "4in_arg"; "4m_vmmaps"]; ["4page_round_up_Z"; "4page_size"; "4two_pow_64"; "4vm_backing_used"; "4vm_backing_within_limit"; "4vm_forget_range"; "4vm_limit"; "4vm_maps"; "5brk_budget_refused_b"; "5brk_r_ok"; "5brk_spec"; "5forget_vm_ranges"; "5mmap_budget_refused_b"; "5mmap_fixed_rw_budget_ok"; "5mmap_fixed_rw_span_budget_ok"; "5mmap_noreserve_backed_ok"]; ["5mmap_spec"; "5with_brk_next"; "5with_mmap_backing"; "5with_mmap_destroyed"; "5with_mmap_replacement"; "6mprotect_budget_ok"; "6mprotect_budget_refused_b"; "6mprotect_spec"; "7mremap_budget_refused_b"; "7mremap_final_budget_b"; "7mremap_fresh_b"; "7mremap_inplace_grow_b"; "7mremap_model_next"; "7mremap_move_budget_b"; "7mremap_spec"; "7page_align_is0_b"]; ["8Sim1"; "8setlim"; "8setlimh"; "9maps_bounded"; ":le"; ":lt"; ":modulo"; "0a"; "0b"; "0dst"; "0flags"; "0h"; "0h'"; "0hi"; "0i"; "0len"]; ["0lo"; "0m"; "0n"; "0nZ"; "0new_n"; "0new_nZ"; "0old"; "0old_n"; "0old_nZ"; "0r"; "0req"; "0rs"; ";Z_to_bv"; ";bv"; ";bv_unsigned"; "0w"]; ["0x"; "0z"]]).
Lemma vm_backing_used_setlim : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMm "='7'9'6&C&QAr2r1%3221%511%613%83:21pT4:1pB<1").
Proof. reflexivity. Qed.
Lemma m_vmmaps_setlim : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMm "@'7'9'6'<&?&QAr2r1%3221%511&QB%714%2261%;3:41pT4=1pB?1").
Proof. reflexivity. Qed.
Lemma vm_limit_setlimh : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMm "<'7'<'6&F&QBr2r1%3221%511%73914pSH91pB;1").
Proof. reflexivity. Qed.
Lemma vm_forget_range_setlim : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMm "B'7'9'6&Er4r3&QAr2r1%3221%73651%83763%6251%;3<31pT4=1pB?1pSL@1pT2A1").
Proof. reflexivity. Qed.
Lemma forget_vm_ranges_setlim : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMm "G'3'4'R=yR0%211%4211%611'7'9'6&Kr3&QAr2r1%3221%6251%7263%6251%:3;31pT4<1pB>1pTH@1").
Proof.
induction rs as [|[a n] rs IH]; intros L m; [reflexivity|].
cbn [forget_vm_ranges]. rewrite vm_forget_range_setlim. apply IH.
Qed.
Lemma with_brk_next_setlim : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMm "E'7'9'R=yR0%211'6&Q1&QAr4r3%3221r2r1%73321%83532%8271%;3?31pTD=1pTF>1pT4B1pBD1").
Proof.
intros L m req r. unfold with_brk_next.
rewrite <- forget_vm_ranges_setlim. reflexivity.
Qed.
#[export] Hint Rewrite with_brk_next_setlim forget_vm_ranges_setlim : bb_lim_comm.
Lemma brk_r_ok_setlim : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMm "Q2'7'9'R=yR0%211'6'1&Hr3r2%3221(2%73621&QD&F&?r4%211%411r5%7221&I&QAr6%2215%4319A%537:B%F3E21p081p0A1pTDJ1pTFK1pT4O1pBQ11").
Proof.
intros L m req r Hmk Hle.
unfold brk_r_ok, brk_grow_ok, brk_budget_ok, brk_budget_refused_b in *.
rewrite vm_backing_used_setlim, m_vmmaps_setlim.
set (h := m_vmmaps m) in *.
cbn [setlimh vm_brk vm_reserved vm_maps vm_limit vm_start_brk vm_init_sp min_brk alloc_top].
unfold min_brk, alloc_top in *. cbn [setlimh vm_start_brk vm_init_sp].
destruct (w_is0 req || (bv_unsigned req <? bv_unsigned (vm_start_brk h))%Z) eqn:E1;
[reflexivity|].
destruct (bv_unsigned req <? bv_unsigned (vm_brk h))%Z eqn:E2; [reflexivity|].
destruct (bv_eqb r req || bv_eqb r (vm_brk h)) eqn:E3; [|reflexivity].
cbn [andb].
destruct ((0 <? bv_unsigned (vm_brk h)) && (bv_unsigned (vm_brk h) <? bv_unsigned r))%Z eqn:E4;
[|reflexivity].
apply orb_true_iff in E3. destruct E3 as [E3 | E3]; apply bv_eqb_eq in E3; subst r.
- apply andb_true_iff in E4. destruct E4 as [E4a E4b].
rewrite ?E1, ?E4a, ?E4b in Hmk. unfold brk_budget_ok in Hmk. cbn [negb andb] in Hmk.
apply negb_false_iff in Hmk. fold h in Hmk. rewrite Hmk.
apply Z.leb_le in Hmk. replace (_ <=? L) with true by (symmetry; apply Z.leb_le; lia).
reflexivity.
- apply andb_true_iff in E4. destruct E4 as [_ E4]. apply Z.ltb_lt in E4. lia.
Qed.
Lemma brk_nat : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMm "Q3'7';'9'6'1&Hr1&>r2(0%3221%6251(2%:3921&QD&F&?%119%311r4%6221&Q@r5':qU21B&J%C27A%211r3%88766522:1p0:1p0B1pT4N1pSNQ01pBQ21").
Proof.
intros L i m Hmk Hle. unfold brk_spec.
eapply sim1_bind; [apply sim1_of_sim, sim_get |].
intros x m' e He. cbv [get_model] in He. injection He as -> -> ->. cbv beta zeta.
eapply sim1_bind.
{ apply sim1_choose. intros r. rewrite (brk_r_ok_setlim L m (in_arg i 0) r Hmk Hle). reflexivity. }
intros r m' e _. cbv beta.
apply sim1_of_sim. sim_auto.
Qed.
Lemma vm_backing_within_limit_mono : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMm "J'7'9&QD&F&?r1%211%411r2%7221'6'1&D%115(5%53421&QAr4r3%3221%811%;3:17p071p0>1pT4G1pBI1").
Proof.
intros L m Hle H. unfold vm_backing_within_limit in *.
rewrite vm_backing_used_setlim, m_vmmaps_setlim, vm_limit_setlimh.
apply Z.leb_le in H. apply Z.leb_le. lia.
Qed.
Lemma mprotect_budget_ok_mono : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMm "Q0'7'9'R=yR0%211&QD&F&?r3%211%411r4%7221'6'1&Q5r2%23691(5%63521&QAr6r5%3221%931=@%<3;17p071p0?1pT6H1pS@I1pT4M1pBO1").
Proof.
intros L m a n Hle H. unfold mprotect_budget_ok in *.
change (mprotect_model_next (setlim L m) a n) with (setlim L (mprotect_model_next m a n)).
apply vm_backing_within_limit_mono; [exact Hle | exact H].
Qed.
Ltac gate_tac ::=
match goal with
| Hmk : negb (mprotect_budget_ok ?m ?a ?n) = false, Hle : vm_limit (m_vmmaps ?m) <= ?L |- _ =>
let G := fresh "G" in
pose proof (proj1 (negb_false_iff _) Hmk) as G;
rewrite (mprotect_budget_ok_mono L m a n Hle G), G; reflexivity
end.
Lemma mprotect_nat : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMm "Q9'7';'9'6'1&Q6&>r2(0%3221u1%5241u2%7261r1%:46421(2%>3=21&QD&F&?%11>%311r4%6221&Q@r5':qU21>&Q7%H27F%I28E%J29D%43321r3%:8988722<1p0<1p0D1pT4Q41pSNQ61pBQ81").
Proof.
intros L i m Hmk Hle. unfold mprotect_budget_refused_b in Hmk. cbv zeta in Hmk.
unfold mprotect_spec.
sim1_auto.
Qed.
Lemma with_mmap_backing_setlim : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMm "G'R=yR0%211'7'9'6&Q2r5r4r3&QAr2r1%3221%847651%948763%6251%<3=31pT4>1pB@1pT6B1pS@C1pSFD1").
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.
Lemma with_mmap_replacement_setlim : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMm "G'R=yR0%211'7'9'6&Q4r5r4r3&QAr2r1%3221%847651%948763%6251%<3=31pT4>1pB@1pT6B1pS@C1pSFD1").
Proof.
intros. unfold with_mmap_replacement. rewrite vm_forget_range_setlim.
apply with_mmap_backing_setlim.
Qed.
Lemma with_mmap_destroyed_setlim : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMm "J'R=yR0%211'<'7'9'6&Q3r5r4&QBr2r3%3221&QAr1%2251%:49841%;4:963%5281%>3?31pT4@1pBB1pSJD1pT6F1pS@G1").
Proof. reflexivity. Qed.
#[export] Hint Rewrite with_mmap_backing_setlim with_mmap_replacement_setlim : bb_lim_comm.
Lemma mmap_noreserve_backed_ok_mono : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMm "Q0'7'9'R=yR0%211&QD&F&?r3%211%411r4%7221'6'1&Or2%23961(5%63521&QAr6r5%3221%93=1@%<3;17p071p0?1pT8L1pSFI1pT4M1pBO1").
Proof.
intros L m flags nZ Hle H. unfold mmap_noreserve_backed_ok in *.
destruct (mmap_noreserve_b flags); [reflexivity|].
rewrite vm_backing_used_setlim, m_vmmaps_setlim, vm_limit_setlimh.
apply Z.leb_le in H. apply Z.leb_le. lia.
Qed.
Lemma mmap_fixed_rw_budget_ok_mono : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMm "Q2'7'9'R=yR0%211&QD&F&?r4%211%411r5%7221'6'1&Mr3r2%34:721(5%73621&QAr7r6%3221%:4>1A9%=3<17p071p0@1pT6I1pS@J1pSFK1pT4O1pBQ11").
Proof.
intros L m flags a n Hle H. unfold mmap_fixed_rw_budget_ok in *.
change (with_vmmaps (mmap_fixed_rw_next (m_vmmaps (setlim L m)) a n) (setlim L m))
with (setlim L (with_vmmaps (mmap_fixed_rw_next (m_vmmaps m) a n) m)).
rewrite with_mmap_replacement_setlim.
apply vm_backing_within_limit_mono; [|exact H].
unfold with_mmap_replacement, with_mmap_backing.
destruct (mmap_noreserve_b flags); exact Hle.
Qed.
Lemma mmap_fixed_rw_span_budget_ok_mono : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMm "Q2'7'9'R=yR0%211&QD&F&?r4%211%411r5%7221'6'1&Nr3r2%34:721(5%73621&QAr7r6%3221%:4>1A9%=3<17p071p0@1pT6I1pS@J1pSFK1pT4O1pBQ11").
Proof.
intros L m flags a n Hle H. unfold mmap_fixed_rw_span_budget_ok in *.
change (with_vmmaps (mmap_fixed_rw_span_next (m_vmmaps (setlim L m)) a n) (setlim L m))
with (setlim L (with_vmmaps (mmap_fixed_rw_span_next (m_vmmaps m) a n) m)).
rewrite with_mmap_replacement_setlim.
apply vm_backing_within_limit_mono; [|exact H].
unfold with_mmap_replacement, with_mmap_backing.
destruct (mmap_noreserve_b flags); exact Hle.
Qed.
Ltac gate_tac ::=
match goal with
| Hmk : negb (mmap_noreserve_backed_ok ?f ?m ?nZ) = false, Hle : vm_limit (m_vmmaps ?m) <= ?L |- _ =>
let G := fresh "G" in
pose proof (proj1 (negb_false_iff _) Hmk) as G;
rewrite (mmap_noreserve_backed_ok_mono L m f nZ Hle G), G; reflexivity
| Hmk : negb (mmap_fixed_rw_budget_ok ?f ?m ?a ?n) = false, Hle : vm_limit (m_vmmaps ?m) <= ?L |- _ =>
let G := fresh "G" in
pose proof (proj1 (negb_false_iff _) Hmk) as G;
rewrite (mmap_fixed_rw_budget_ok_mono L m f a n Hle G), G; reflexivity
| Hmk : negb (mmap_fixed_rw_span_budget_ok ?f ?m ?a ?n) = false, Hle : vm_limit (m_vmmaps ?m) <= ?L |- _ =>
let G := fresh "G" in
pose proof (proj1 (negb_false_iff _) Hmk) as G;
rewrite (mmap_fixed_rw_span_budget_ok_mono L m f a n Hle G), G; reflexivity
end.
Lemma mmap_nat : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMm "QB'7';'9'6'1&L&>r2(0%3221u1%5241u2%7261u3%9281u4%;2:1u5%=2<1r1%@7<:86421(2%D3C21&QD&F&?%11D%311r4%6221&Q@r5':qU21>&Q0%N27L%O28K%Q029J%Q12:I%Q22;H%Q32<G%76654321r3%=8<;;:22?1p0?1p0G1pT4Q=1pSNQ?1pBQA1").
Proof.
intros L i m Hmk Hle. unfold mmap_budget_refused_b in Hmk. cbv zeta in Hmk.
unfold mmap_spec.
sim1_auto.
Qed.
Definition maps_bounded (l : list (word * word)) : Prop :=
forall (a sz : word), In (a, sz) l -> bv_unsigned a + bv_unsigned sz <= two_pow_64.
Definition move_charge_le_stmt : Prop :=
forall m old old_n dst new_n,
maps_bounded (vm_maps (m_vmmaps m)) ->
bv_unsigned dst mod page_size = 0 ->
bv_unsigned new_n mod page_size = 0 ->
0 < bv_unsigned new_n ->
bv_unsigned dst + bv_unsigned new_n < two_pow_64 ->
region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) dst new_n = true ->
vm_backing_used (mremap_model_next m old old_n dst new_n)
<= mremap_move_charge m old old_n new_n.
Lemma mremap_model_next_setlim : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMm "I'7'9'R=yR0%211'6&Q<&QAr6r5%3221r4r3r2r1%9554321%:575432%:291%=3A31pT:?1pSD@1pT@A1pT>B1pT4F1pBH1").
Proof. reflexivity. Qed.
#[export] Hint Rewrite mremap_model_next_setlim : bb_lim_comm.
Lemma mremap_model_next_limit : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMm "I'9'R=yR0%211'6'7&F&?&Q<r5r4r3r2r1%6554321%811%:11%:18%<11%?3>31pT:A1pSDB1pT@C1pT>D1pT4H1").
Proof. reflexivity. Qed.
Lemma mremap_final_budget_mono : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMm "Q4'7'9'R=yR0%211&QD&F&?r5%211%411r6%7221'6'1&Q9r4r3r2%458;321(5%83721&QAr8r7%3221%;51?B:9%>3=17p071p0A1pT:J1pSDK1pT@L1pT>M1pT4Q11pBQ31").
Proof.
intros L m old old_n dst new_n Hle H. unfold mremap_final_budget_b in *.
rewrite mremap_model_next_setlim. apply vm_backing_within_limit_mono; [|exact H].
rewrite mremap_model_next_limit. exact Hle.
Qed.
Lemma mremap_inplace_grow_setlim : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMm "Q7'7'9'R=yR0%211&QD&F&?r6%211%411r7%7221'6'1&Q9r5r4%357:2:1(5%73621&Q;&QAr9r8%3221r3%662@C;:1%764AD<;2%@3?21p0:1p0C1pSBQ01pS@Q11pT:N1pT@O1pT>Q01pT4Q41pBQ61").
Proof.
intros L m old old_n new_n a b Hle H. unfold mremap_inplace_grow_b.
rewrite (mremap_final_budget_mono L m old old_n old new_n Hle H), H. reflexivity.
Qed.
Lemma alloc_top_lt' : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMm "8'<&QE&=r1%211&B%5221pSH71").
Proof.
intros h. unfold alloc_top, stack_max_size, two_pow_64.
pose proof (bv_unsigned_in_range 64 (vm_init_sp h)) as R.
change (bv_modulus 64) with (2 ^ 64) in R. lia.
Qed.
Lemma page_round_up_Z_nonneg' : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMm ";'7&QDzr1%3221&@r2%211%7261p051pU4:1").
Proof.
intros z Hz. unfold page_round_up_Z, page_size.
apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia | lia].
Qed.
Lemma page_round_up_Z_mod' : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMm ";'7'6&QF&@r1%211&A%5221z%83921pU4:1").
Proof. intros z. unfold page_round_up_Z, page_size. apply Z_mod_mult. Qed.
Lemma bv_unsigned_nonneg : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMm ":'R=yR0%211&QDz&R>r1%2261%5241pU071").
Proof. intros w. pose proof (bv_unsigned_in_range 64 w). lia. Qed.
Lemma page_align_is0_b_false_pos : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMm "D'R=yR0%211'6'1&Q?r1%211(2%63521&QEz&@&R>r2%22>1%411%7261p091pT0A1").
Proof.
intros len H. unfold page_align_is0_b in H. apply orb_false_iff in H as [H0 _].
unfold w_is0 in H0.
assert (Hn : bv_unsigned len <> 0).
{ intros E. assert (len = Z_to_bv 64 0) as E'.
{ apply bv_eq. rewrite E. reflexivity. }
apply bv_eqb_eq in E'. congruence. }
pose proof (bv_unsigned_nonneg len).
unfold page_round_up_Z, page_size.
assert (1 <= (bv_unsigned len + 4096 - 1) / 4096).
{ apply Z.div_le_lower_bound; lia. }
lia.
Qed.
Section Mremap.
Hypothesis MCLE : move_charge_le_stmt.
Lemma mremap_fresh_setlim : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMm "QL'7'9'R=yR0%211&QC&G&?r6%211%411%611&QD&Fr7%811%311r8%6221z%821<'6&QF&A%22:1%43I16&QE%128:'1&Q=r;&R<r9%22N1%544AD1(5%?3821&Q:&QAr=r<%3221r:%<2Q81%773>2<KN1%875?3=LO2%I3B21p0;1p0E1p0H1p0N1p0Q11p0Q91pSDQA1pT@QB1pT>QC1pT<QH1pTBQI1pT4QI1pBQK1").
Proof.
intros L m old_nZ new_nZ old old_n dst Hb Hle Hn0 Hnal Hnpos Hmv.
unfold mremap_fresh_b. cbv zeta.
rewrite m_vmmaps_setlim. cbn [setlimh vm_reserved vm_maps].
change (alloc_top (setlimh L (m_vmmaps m))) with (alloc_top (m_vmmaps m)).
destruct (negb (bv_eqb dst old) && (bv_unsigned dst mod page_size =? 0)
&& (0 <? bv_unsigned dst) && (bv_unsigned dst + new_nZ <=? alloc_top (m_vmmaps m))
&& region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) dst (Z_to_bv 64 new_nZ))
eqn:E; [|reflexivity].
cbn [andb].
assert (G : mremap_final_budget_b m old old_n dst (Z_to_bv 64 new_nZ) = true).
{ unfold mremap_final_budget_b, vm_backing_within_limit, mremap_move_budget_b in *.
apply Z.leb_le in Hmv. apply Z.leb_le. rewrite mremap_model_next_limit.
repeat (apply andb_true_iff in E; destruct E as [E ?]).
match goal with H : (bv_unsigned dst + new_nZ <=? _) = true |- _ => apply Z.leb_le in H end.
match goal with H : (bv_unsigned dst mod page_size =? 0) = true |- _ => apply Z.eqb_eq in H end.
pose proof (alloc_top_lt' (m_vmmaps m)).
assert (Hu : bv_unsigned (Z_to_bv 64 new_nZ) = new_nZ).
{ apply Z_to_bv_small. change (bv_modulus 64) with two_pow_64. lia. }
eapply Z.le_trans; [| exact Hmv].
apply MCLE; try assumption; rewrite ?Hu; try lia. }
rewrite G. rewrite (mremap_final_budget_mono L m old old_n dst _ Hle G). reflexivity.
Qed.
Ltac disc_tac ::=
match goal with
| HA : mremap_final_budget_b ?m ?o ?on ?o ?nn = true, Hle : vm_limit (m_vmmaps ?m) <= ?L
|- mremap_inplace_grow_b (setlim ?L ?m) _ _ _ _ _ = _ =>
exact (mremap_inplace_grow_setlim L m _ _ _ _ _ Hle HA)
end.
Ltac gate_tac ::=
match goal with
| HB : mremap_move_budget_b ?m ?o ?on (Z_to_bv 64 ?nZ) = true, Hle : vm_limit (m_vmmaps ?m) <= ?L,
Hb : maps_bounded (vm_maps (m_vmmaps ?m))
|- (mremap_fresh_b (setlim ?L ?m) _ ?nZ _ _ _ _ = true) <-> _ =>
rewrite (mremap_fresh_setlim L m _ nZ _ _ _ Hb Hle); [reflexivity | | | | exact HB];
[ apply page_round_up_Z_nonneg'; apply bv_unsigned_nonneg
| apply page_round_up_Z_mod'
| apply page_align_is0_b_false_pos; assumption ]
end.
Lemma mremap_nat : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeMm "QC'7';'9'6'1&Q8&>r2(0%3221u1%5241u2%7261u3%9281r1%<586421(2%@3?21&QD&F&?%11@%311r4%6221&QC&Gr3%811%311%511&Q@r6':qU21D&Q>r5%Q121O%Q222N%Q323M%Q424L%644321%;8:998116Cp0=1p0D1p0L1pT4Q>1pSNQ@1pBQB1").
Proof.
intros L i m Hmk Hle Hb. unfold mremap_budget_refused_b in Hmk. cbv zeta in Hmk.
unfold mremap_spec.
sim1_auto.
match goal with
| H1 : (?n2 <? ?n1) = false, H2 : (?n1 =? ?n2) = false |- _ =>
assert (Hgt : (n2 <=? n1) = false)
by (apply Z.leb_gt; apply Z.ltb_ge in H1; apply Z.eqb_neq in H2; lia)
end.
rewrite Hgt in Hmk. cbv beta iota in Hmk.
apply negb_false_iff, andb_true_iff in Hmk. destruct Hmk as [HA HB].
sim1_auto.
Qed.
End Mremap.
