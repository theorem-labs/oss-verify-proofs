(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK15 YK0n YP0n YM06 YK0s YM02 YK1j YK0v YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a YO0b YO0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH00 YH03 YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0h YO0w YO0s YO0u YO15 YO10 YO12 YO14 YO0t YO0q YO0v YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN03 YN02 YN2b YN25 YN26
YN2a YN2q YN2o YN0b YN07 YN0a YN08
YN0t YN2u YN2t YN0k YN0p YN2r YN2s
YN0u YN0v YN0r YN0s YN0q YN2p YN0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Record ntcall (fuel : nat) (L : layout) (A0 : astate) (g : sptr) (regs0 regs2 : bvmap 5 word)
(mem0 mem2 : word -> option byte) (gv : Z) : Prop := {
nc_ra : getr regs2 (nat_to_reg 1) = Z_to_bv 64 XJ;
nc_s3 : getr regs2 (nat_to_reg 19) = Z_to_bv 64 (ptr_addr L g);
nc_s1 : getr regs2 (nat_to_reg 9) = Z_to_bv 64 GUARD;
nc_s2 : getr regs2 (nat_to_reg 18) = Z_to_bv 64 CTX;
nc_sp : getr regs2 (nat_to_reg 2) = Z_to_bv 64 (spZ regs0 - 96);
nc_keep : forall r, In r kept_regs -> getr regs2 (nat_to_reg r) = getr regs0 (nat_to_reg r);
nc_frame :
bytes_are mem2 (spZ regs0 - 48) 8 gv /\
bytes_are mem2 (spZ regs0 - 40) 8 (bv_unsigned (getr regs0 (nat_to_reg 19))) /\
bytes_are mem2 (spZ regs0 - 32) 8 (bv_unsigned (getr regs0 (nat_to_reg 18))) /\
bytes_are mem2 (spZ regs0 - 24) 8 (bv_unsigned (getr regs0 (nat_to_reg 9))) /\
bytes_are mem2 (spZ regs0 - 16) 8 (bv_unsigned (getr regs0 (nat_to_reg 8))) /\
bytes_are mem2 (spZ regs0 - 8) 8 (bv_unsigned (getr regs0 (nat_to_reg 1)));
nc_guard : word_mem src0segs mem2 GUARD gv;
nc_ret : YK0s.ret_ok (getr regs0 (nat_to_reg 1));
nc_tp : getr regs0 (nat_to_reg 4) = Z_to_bv 64 (ms_tp B1);
nc_spf : spZ regs0 mod 16 = 0 /\ alloc_ceiling + NT_FRAME * Z.of_nat (S fuel) <= spZ regs0 /\ spZ regs0 < 2 ^ 63;
nc_stkw : forall a, spZ regs0 - NT_FRAME * Z.of_nat (S fuel) <= a < spZ regs0 -> writable_at src0segs mem2 a;
nc_unch : forall a, 0 <= a < 2 ^ 64 -> ~ alloc_owned L A0 a -> ~ (spZ regs0 - NT_FRAME * Z.of_nat (S fuel) <= a < spZ regs0) ->
mem2 (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)
}.
Lemma upd_slot_fields2 am i x :
am_aidx (upd_slot am i x) = am_aidx am /\ am_avail (upd_slot am i x) = am_avail am /\ am_freed (upd_slot am i x) = am_freed am /\
am_prev (upd_slot am i x) = am_prev am /\ am_next (upd_slot am i x) = am_next am.
Proof. destruct am; repeat split; reflexivity. Qed.
Lemma ret_ok_XJ : YK0s.ret_ok (Z_to_bv 64 XJ).
Proof. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Section e.
Variables (X : list sptr) (U1 U : Z -> Z) (fuel : nat) (L : layout) (A s1 : astate) (g : sptr) (am1 : ameta).
Variables (regs regs1 : bvmap 5 word) (mem mem1 : word -> option byte) (md : Model) (gv : Z).
Variables (g' : sptr) (am' : ameta) (i' : Z) (fr' : frame).
Hypothesis NM : ntmid (g :: X) fuel L A s1 g regs regs1 mem mem1 md gv.
Hypothesis HI1 : Inv (g :: X) None U1 s1.
Hypothesis Mg1 : MT s1 g = Some (MUsed am1).
Hypothesis Hsc : 0 <= am_sc am1 < 48.
Hypothesis Hlast : 0 <= am_last am1 <= 31.
Hypothesis Hml0 : am_maplen am1 = 0.
Hypothesis Eus : st_usage s1 = st_usage A.
Hypothesis AO1 : forall a, alloc_owned L s1 a -> alloc_owned L A a.
Hypothesis Ug' : usedX (g :: X) s1 g' am'.
Hypothesis Hi' : 0 <= i' <= am_last am'.
Hypothesis Hfr' : ss_fr (nth_slot am' i') = Some fr'.
Hypothesis Hk' : fr_kind fr' = FGroup.
Hypothesis Emem : am_mem am1 = slot_start am' i'.
Hypothesis Hsc' : 0 <= am_sc am' < 48.
Hypothesis Hg'g : g' <> g.
Hypothesis NOSL : forall c ac, usedX (g :: X) s1 c ac -> am_maplen ac = 0 -> am_mem ac <> slot_start am' i'.
Let sc := am_sc am1.
Let G := ptr_addr L g.
Let SP0 := spZ regs.
Let G' := ptr_addr L g'.
Let PM := ptr_addr L (am_mem am').
Let GM := ptr_addr L (am_mem am1).
Let sc' := am_sc am'.
Let ST := stride_of am'.
Definition h16 : Z := ST * i' / 16.
Definition m : bool := 0 <? am_maplen am'.
Definition s2 : astate := A_usg A sc am1 s1.
Definition s3 : astate := upd_meta g' (MUsed (am_forget am' i')) s2.
Hypothesis HI3 : Inv (g :: X) (Some (g', i')) U s3.
Lemma HL1 : layout_ok L s1. Proof. exact (nm_layout _ _ _ _ _ _ _ _ _ _ _ _ NM). Qed.
Lemma SO : syms_ok B1. Proof. exact (nm_syms _ _ _ _ _ _ _ _ _ _ _ _ NM). Qed.
Lemma Hctx : ly_ctx L = CTX. Proof. exact (nm_ctx _ _ _ _ _ _ _ _ _ _ _ _ NM). Qed.
Lemma Hsec : 0 <= ly_sec L < 2 ^ 64. Proof. exact (nm_sec _ _ _ _ _ _ _ _ _ _ _ _ NM). Qed.
Lemma MR1 : memrepX B1 (g :: X) L s1 mem1. Proof. exact (nm_rep _ _ _ _ _ _ _ _ _ _ _ _ NM). Qed.
Lemma ST1 : statics_ok B1 mem1. Proof. exact (nm_statics _ _ _ _ _ _ _ _ _ _ _ _ NM). Qed.
Lemma LG1 : ledger_ok B1 L s1 md. Proof. exact (nm_ledger _ _ _ _ _ _ _ _ _ _ _ _ NM). Qed.
Lemma Mg' : MT s1 g' = Some (MUsed am'). Proof. exact (proj1 (usedX_MT _ _ _ _ Ug')). Qed.
Lemma g_facts3 : 4096 <= G /\ G + 40 <= alloc_ceiling /\ G mod 8 = 0 /\ (forall y, G <= y < G + 40 -> ~ in_img B1 y).
Proof. destruct (key_facts (g :: X) None U1 L s1 md HI1 LG1 g _ Mg1) as (A1 & A2 & A3 & A4 & _). unfold G. auto. Qed.
Lemma Ebits : meta_bits am1 = bits_enc (am_last am1) sc 0.
Proof. unfold meta_bits, bits_enc. rewrite Hml0. reflexivity. Qed.
Lemma Ebits' : meta_bits am' = bits_enc (am_last am') sc' (am_maplen am').
Proof. reflexivity. Qed.
Lemma sp_facts3 :
SP0 mod 16 = 0 /\ alloc_ceiling + 96 + 96 * Z.of_nat fuel <= SP0 /\ SP0 < 2 ^ 63 /\
(forall x, SP0 - 96 * Z.of_nat (S fuel) <= x < SP0 -> writable_at src0segs mem1 x).
Proof.
pose proof (nm_spf _ _ _ _ _ _ _ _ _ _ _ _ NM) as (S1 & S2 & S3). pose proof (nm_stkw _ _ _ _ _ _ _ _ _ _ _ _ NM) as W.
unfold NT_FRAME in *. unfold SP0. split; [exact S1|]. split; [lia|]. split; [exact S3|]. intros x Hx. apply W. lia.
Qed.
Lemma parent_facts :
0 <= am_last am' <= 31 /\ 0 <= am_avail am' < 2 ^ 32 /\ 0 <= am_freed am' < 2 ^ 32 /\
Z.testbit (am_avail am') i' = false /\ Z.testbit (am_freed am') i' = false /\
ss_hdr (nth_slot am' i') = Some (i' + 192, h16) /\ fr_off fr' = 0 /\ fr_n fr' = ST - IB /\
16 <= ST /\ ST mod 16 = 0 /\ 0 <= h16 <= 65535 /\ 16 * h16 = ST * i' /\
0 <= am_maplen am' < 2 ^ 40 /\ 0 <= meta_bits am' < 2 ^ 64 /\
1 <= scl_of sc' <= 8191 /\ scl_of sc' * i' <= h16 < scl_of sc' * (i' + 1) /\
(0 < am_maplen am' -> h16 <= 256 * am_maplen am' - 1 /\ poff (am_mem am') = 0).
Proof.
pose proof (inv_groups HI1 g' am' Ug') as GG. pose proof (stride_pos _ _ _ _ _ GG) as Sp.
pose proof GG as ((Glast & Gaidx & Glen & Gav & Gfrn & Gdisj & Gabove & Gavp & Gfra) & Gml & Gsl & Gcl & Gmp & Gns).
pose proof (Gsl i' Hi') as (_ & _ & S3'). rewrite Hfr' in S3'. destruct S3' as (Hal & _ & (Nf & Of & Bf & H16 & FG) & Hhdr).
destruct (FG Hk') as [Hoff Hn].
pose proof (stride_mod16 _ _ _ _ _ _ HI1 Ug') as Hst16.
assert (Hav32 : am_avail am' < 2 ^ 32) by (apply (mask_u32 _ (am_last am')); [lia|lia|intros j Hj; apply (proj1 (Gabove j Hj))]).
assert (Hfr32 : am_freed am' < 2 ^ 32) by (apply (mask_u32 _ (am_last am')); [lia|lia|intros j Hj; apply (proj2 (Gabove j Hj))]).
assert (Hbits : Z.testbit (am_avail am') i' = false /\ Z.testbit (am_freed am') i' = false).
{ unfold allocated in Hal. rewrite Z.lor_spec in Hal. destruct (Z.testbit (am_avail am') i'), (Z.testbit (am_freed am') i'); cbn in Hal; try discriminate; auto. }
assert (Hdiv : ST * i' / 16 * 16 = ST * i').
{ pose proof Hst16 as Hst. apply Z.div_exact in Hst; [|lia]. fold ST in Hst. rewrite Hst at 1. rewrite <- Z.mul_assoc, (Z.mul_comm 16), Z_div_mult by lia. lia. }
assert (Hh16 : hdr_off16 am' i' fr' = h16) by (unfold hdr_off16, h16, UNIT; fold ST; rewrite Hoff; lia).
assert (Hml40 : am_maplen am' < 2 ^ 40).
{ destruct (Z_lt_le_dec 0 (am_maplen am')) as [Hm'|Hm']; [|lia].
destruct (Gmp Hm') as (r1 & rg1 & Em1 & Hr1 & _ & Hl1 & Hlen1 & _).
destruct (lg_placed _ _ _ _ LG1 _ _ Hr1 Hl1) as (_ & R1 & R2 & _). pose proof (proj1 alloc_ceiling_val). unfold PGSZ in *. lia. }
pose proof (scl_range sc' Hsc') as SR. assert (Escl : scl_of sc' = znth sc' size_classes) by (unfold scl_of; replace (sc' <? 48) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
assert (Hcs : class_size sc' = 16 * znth sc' size_classes) by reflexivity.
destruct Gcl as [(C63 & _) | (Csc & CN1 & C26 & Cspan)]; [unfold sc' in *; lia|].
assert (P1 : 0 <= ST * i') by nia.
assert (K1 : ss_hdr (nth_slot am' i') = Some (i' + 192, h16)) by (rewrite (Hhdr Hoff); unfold hdr_byte3; rewrite Hk', Hh16; reflexivity).
assert (K2 : fr_n fr' = ST - IB) by (fold ST in Hn; exact Hn).
assert (K3 : 0 <= h16) by (unfold h16; apply Z.div_pos; lia).
assert (K4 : h16 <= 65535) by (rewrite <- Hh16; exact H16).
assert (K5 : 16 * h16 = ST * i') by (unfold h16; lia).
assert (K6 : 0 <= meta_bits am' < 2 ^ 64) by (rewrite Ebits'; split; [apply bits_nonneg | apply bits_lt64]; unfold sc'; lia).
assert (K7 : scl_of sc' * i' <= h16).
{ rewrite Escl. destruct (Z_lt_dec ST (class_size sc')) as [Hlt|Hge].
+ destruct (CN1 Hlt) as [Hl0 _]. assert (Hi0 : i' = 0) by lia. unfold h16. rewrite Hi0, !Z.mul_0_r. change (0 / 16) with 0. lia.
+ unfold h16. assert (znth sc' size_classes * i' * 16 <= ST * i' / 16 * 16) by (rewrite Hdiv; nia). lia. }
assert (K8 : h16 < scl_of sc' * (i' + 1)).
{ rewrite Escl. destruct (Z.eq_dec (am_last am') 0) as [Hl0 | Hl0].
+ assert (Hi0 : i' = 0) by lia. unfold h16. rewrite Hi0, !Z.mul_0_r, Z.add_0_l, Z.mul_1_r. change (0 / 16) with 0. lia.
+ assert (Es : ST = class_size sc') by (unfold ST, stride_of; replace (am_last am' =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hl0); reflexivity).
unfold h16. rewrite Es, Hcs. replace (16 * znth sc' size_classes * i') with (znth sc' size_classes * i' * 16) by lia. rewrite Z_div_mult by lia. nia. }
assert (K9 : 0 < am_maplen am' -> h16 <= 256 * am_maplen am' - 1 /\ poff (am_mem am') = 0).
{ intros Hm'. destruct (Gmp Hm') as (r1 & rg1 & Em1 & Hr1 & _ & _ & Hlen1 & Hfit & _). split; [| rewrite Em1; reflexivity].
unfold PGSZ, UNIT in Hfit. fold ST in Hfit.
assert (ST * i' + ST <= ST * (am_last am' + 1)) by nia. unfold h16.
assert (ST * i' / 16 * 16 <= (256 * am_maplen am' - 1) * 16) by (rewrite Hdiv; lia). lia. }
destruct Hbits as [Hb1 Hb2].
repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
Qed.
Lemma geo_facts :
exists AG AR RLO RLEN,
AG mod 4096 = 0 /\ 4096 <= AG /\ AG + 24 <= G /\ G + 40 <= AG + 4096 /\ AG + 4096 <= alloc_ceiling /\
(forall y, AG <= y < AG + 4096 -> ~ in_img B1 y) /\
AR mod 4096 = 0 /\ 4096 <= AR /\ (exists k, 0 <= k < 101 /\ G' = AR + 24 + 40 * k) /\ AR = G' - G' mod 4096 /\ AR + 4096 <= alloc_ceiling /\
(forall y, AR <= y < AR + 4096 -> ~ in_img B1 y) /\ (forall y, AR <= y < AR + 4096 -> present mem1 y) /\
bytes_are mem1 AR 8 (ly_sec L) /\
(AG = AR \/ AG + 4096 <= AR \/ AR + 4096 <= AG) /\
RLO mod 4096 = 0 /\ 4096 <= RLO /\ RLO + RLEN <= alloc_ceiling /\ (forall y, RLO <= y < RLO + RLEN -> ~ in_img B1 y) /\
(forall y, RLO <= y < RLO + RLEN -> present mem1 y) /\
RLO <= PM /\ PM mod 16 = 0 /\ PM + 16 + ST * i' = GM /\ GM + ST <= PM + group_extent am' + IB /\ PM + group_extent am' + IB <= RLO + RLEN /\
RLO = ly_reg L (prid (am_mem am')) /\
(AG + 4096 <= RLO \/ RLO + RLEN <= AG) /\ (AR + 4096 <= RLO \/ RLO + RLEN <= AR).
Proof.
pose proof (inv_keys HI1) as (NDk & KP & _ & _ & Hcnt). pose proof HL1 as (_ & _ & PW & _). pose proof (proj1 alloc_ceiling_val) as HCV.
pose proof parent_facts as (Plast & _ & _ & _ & _ & _ & _ & _ & Sp & Hst16 & _).
destruct (KP g (MT_Some_In_keys _ _ _ Mg1)) as (ag & kg & Hag & Hkg & Eg).
assert (Hkg' : 0 <= kg < METAS_PER_AREA) by (unfold handed in Hkg; destruct (sptr_eqb ag _); lia).
destruct (proj1 (proj2 (inv_areas HI1)) ag Hag) as (rag & oag & rgag & Eag & Hoag & Hoag0 & Hrag & Hragl & Hoaglen & Hragk).
destruct (lg_placed _ _ _ _ LG1 _ _ Hrag Hragl) as (AGal & AG4096 & AGceil & AGimg).
destruct (KP g' (MT_Some_In_keys _ _ _ Mg')) as (ar & kr & Har & Hkr & Eg').
assert (Hkr' : 0 <= kr < METAS_PER_AREA) by (unfold handed in Hkr; destruct (sptr_eqb ar _); lia).
destruct (proj1 (proj2 (inv_areas HI1)) ar Har) as (rar & oar & rgar & Ear & Hoar & Hoar0 & Hrar & Hrarl & Hoarlen & Hrark).
destruct (lg_placed _ _ _ _ LG1 _ _ Hrar Hrarl) as (ARal & AR4096 & ARceil & ARimg).
destruct (used_group_region (g :: X) None U1 s1 g' am' HI1 Ug') as (rg & Hr & Hk & Hl & Ho & Hext & Hml0').
destruct (lg_placed _ _ _ _ LG1 _ _ Hr Hl) as (Ral & R4096 & Rceil & Rimg).
pose proof (used_group_aligned (g :: X) None U1 s1 HI1 _ g' am' Ug' (Nat.le_refl _)) as Hal16.
pose proof (slot_in_span (g :: X) None U1 s1 HI1 g' am' i' Ug' Hi') as [S1 S2]. fold ST in S2.
set (AG := ly_reg L rag + oag). set (AR := ly_reg L rar + oar). set (RLO := ly_reg L (prid (am_mem am'))).
assert (InAG : In (LMem ag, PGSZ) (footprint s1)) by (right; apply in_app_iff; left; apply in_map_iff; exists ag; auto).
assert (InAR : In (LMem ar, PGSZ) (footprint s1)) by (right; apply in_app_iff; left; apply in_map_iff; exists ar; auto).
assert (InR : In (LMem (YO0i.SP (prid (am_mem am')) 0), rg_len rg) (footprint s1)) by (apply footprint_region_In; assumption).
assert (FA : forall a0, In (LMem a0, PGSZ) (footprint s1) -> forall y, loc_addr L (LMem a0) <= y < loc_addr L (LMem a0) + PGSZ -> present mem1 y).
{ intros a0 Ha0 y Hy. exact (proj1 (Forall_forall _ _) (proj2 (proj2 MR1)) _ Ha0 y Hy). }
exists AG, AR, RLO, (rg_len rg).
assert (EG : G = AG + 24 + 40 * kg) by (unfold G, ptr_addr, loc_addr; rewrite Eg, Eag; cbn [padd]; unfold AG, AREA_HDR, META_SIZE; lia).
assert (EG' : G' = AR + 24 + 40 * kr) by (unfold G', ptr_addr, loc_addr; rewrite Eg', Ear; cbn [padd]; unfold AR, AREA_HDR, META_SIZE; lia).
assert (EPM : PM = RLO + poff (am_mem am')) by (unfold PM, RLO, ptr_addr; destruct (am_mem am'); reflexivity).
assert (EGM : GM = RLO + poff (am_mem am') + 16 + ST * i').
{ unfold GM, RLO, ptr_addr. rewrite Emem. unfold slot_start. destruct (am_mem am'); cbn. unfold UNIT, ST. lia. }
rewrite poff_slot_start in S1, S2. fold ST in S1, S2.
unfold METAS_PER_AREA, PGSZ, UNIT, IB in *.
assert (DJ : forall e1 e2, In e1 (footprint s1) -> In e2 (footprint s1) -> e1 <> e2 ->
fst (crange L e1) + snd (crange L e1) <= fst (crange L e2) \/ fst (crange L e2) + snd (crange L e2) <= fst (crange L e1)).
{ intros e1 e2 I1 I2 NE. destruct (pairwise_map_In ranges_disjoint (crange L) (footprint s1) _ _ PW I1 I2 NE) as [D|D]; unfold ranges_disjoint in D; lia. }
assert (Q1 : AG mod 4096 = 0) by (unfold AG; rewrite Z.add_mod, AGal, Hoag by lia; reflexivity).
assert (Q2 : AR mod 4096 = 0) by (unfold AR; rewrite Z.add_mod, ARal, Hoar by lia; reflexivity).
assert (Q3 : exists k, 0 <= k < 101 /\ G' = AR + 24 + 40 * k) by (exists kr; lia).
assert (Q3a : forall y, AG <= y < AG + 4096 -> ~ in_img B1 y) by (intros y Hy; apply AGimg; unfold AG in Hy; lia).
assert (Q3b : AR = G' - G' mod 4096).
{ rewrite EG'. replace (AR + 24 + 40 * kr) with (24 + 40 * kr + (AR / 4096) * 4096) at 2 by (pose proof (proj2 (Z.div_exact AR 4096 ltac:(lia)) Q2); lia).
rewrite Z_mod_plus_full, Z.mod_small by lia. lia. }
assert (Q4 : forall y, AR <= y < AR + 4096 -> ~ in_img B1 y) by (intros y Hy; apply ARimg; unfold AR in Hy; lia).
assert (Q5 : forall y, AR <= y < AR + 4096 -> present mem1 y) by (intros y Hy; apply (FA ar InAR); rewrite Ear; cbn [loc_addr]; unfold AR in Hy; lia).
assert (Q6 : bytes_are mem1 AR 8 (ly_sec L)).
{ assert (Hc : In (MCell (LMem ar) 8 VSec) (areas_cells s1 (st_areas s1))).
{ apply (In_areas_cells_intro s1 (st_areas s1) ar _ Har). intros next. unfold area_cells. left. reflexivity. }
pose proof (CELL (g :: X) L s1 mem1 MR1 _ ltac:(unfold imageX; apply in_app_iff; right; apply in_app_iff; left; exact Hc)) as C.
unfold cell_mem in C. cbn [mc_val mc_loc mc_w sval_num] in C. rewrite Ear in C. cbn [loc_addr] in C. unfold AR. exact C. }
assert (Q7 : AG = AR \/ AG + 4096 <= AR \/ AR + 4096 <= AG).
{ destruct (sptr_eq_dec ag ar) as [E|NE].
+ left. unfold AG, AR. rewrite E in Eag. rewrite Eag in Ear. injection Ear as -> ->. reflexivity.
+ right. destruct (DJ _ _ InAG InAR ltac:(intros EE; injection EE as EE'; exact (NE EE'))) as [D|D]; rewrite Eag, Ear in D; cbn [crange fst snd loc_addr] in D; unfold AG, AR; lia. }
assert (Q8 : forall y, RLO <= y < RLO + rg_len rg -> ~ in_img B1 y) by (intros y Hy; apply Rimg; unfold RLO in Hy; lia).
assert (Q9 : forall y, RLO <= y < RLO + rg_len rg -> present mem1 y).
{ intros y Hy. apply (proj1 (Forall_forall _ _) (proj2 (proj2 MR1)) _ InR). cbn [fst snd loc_addr]. unfold RLO in Hy. lia. }
assert (Q10 : PM mod 16 = 0).
{ rewrite EPM. unfold RLO.
pose proof Ral as Ral'. apply Z.div_exact in Ral'; [|lia]. apply Z.div_exact in Hal16; [|lia].
replace (ly_reg L (prid (am_mem am')) + poff (am_mem am')) with ((ly_reg L (prid (am_mem am')) / 4096 * 256 + poff (am_mem am') / 16) * 16) by lia. apply Z_mod_mult. }
assert (Q11 : AG + 4096 <= RLO \/ RLO + rg_len rg <= AG).
{ destruct (DJ _ _ InAG InR ltac:(intros EE; exact (area_entry_not_region (g :: X) None U1 s1 HI1 ag _ rg Hag Hr Hk EE))) as [D|D];
rewrite Eag in D; cbn [crange fst snd loc_addr] in D; unfold AG, RLO; lia. }
assert (Q12 : AR + 4096 <= RLO \/ RLO + rg_len rg <= AR).
{ destruct (DJ _ _ InAR InR ltac:(intros EE; exact (area_entry_not_region (g :: X) None U1 s1 HI1 ar _ rg Har Hr Hk EE))) as [D|D];
rewrite Ear in D; cbn [crange fst snd loc_addr] in D; unfold AR, RLO; lia. }
repeat match goal with |- _ /\ _ => split end; try assumption; unfold AG, AR, RLO in *; try lia.
Qed.
Definition AR : Z := G' - (G' mod 4096).
Lemma AR_facts : AR mod 4096 = 0 /\ 4096 <= AR /\ AR + 24 <= G' /\ G' + 40 <= AR + 4096 /\ AR + 4096 <= alloc_ceiling /\
(forall y, AR <= y < AR + 4096 -> ~ in_img B1 y) /\ (forall y, AR <= y < AR + 4096 -> present mem1 y) /\ bytes_are mem1 AR 8 (ly_sec L) /\
Z.land G' (2 ^ 64 - 4096) = AR.
Proof.
destruct geo_facts as (AG & AR0 & RLO & RLEN & _ & _ & _ & _ & _ & _ & Q2 & A4096 & (k & Hk & EG') & EAR & Aceil & Aimg & Apres & Achk & _).
assert (E : AR = AR0) by (unfold AR; rewrite EAR; reflexivity).
rewrite E. pose proof (proj1 alloc_ceiling_val). destruct (key_facts (g :: X) None U1 L s1 md HI1 LG1 g' _ Mg') as (P1 & P2 & _).
repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
change (2 ^ 64 - 4096) with (2 ^ 64 - 2 ^ 12). rewrite land_neg_pow2_u64 by (unfold G' in *; lia). change (2 ^ 12) with 4096. unfold G' in *. lia.
Qed.
Definition xvN (k : nat) : Z :=
if (k <? 32)%nat then bv_unsigned (getr regs1 (nat_to_reg k))
else match k with
| 43%nat => GM
| 46%nat => meta_bits am1
| 48%nat => sc
| 49%nat => CTX + 80 + 8 * sc
| 54%nat => usage_of A sc mod 2 ^ 64
| 56%nat => am_last am1
| 65%nat => G'
| 66%nat => PM
| 67%nat => i' + 192
| 68%nat => h16
| 69%nat => meta_bits am'
| 70%nat => am_avail am'
| 71%nat => am_freed am'
| 72%nat => AR
| 74%nat => sc'
| 75%nat => scl_of sc'
| 76%nat => TBL + 2 * sc'
| 77%nat => am_maplen am'
| 78%nat => i'
| 79%nat => am_last am'
| 39%nat => ly_sec L
| _ => 0
end.
Lemma lin :
4096 <= G /\ G + 40 <= alloc_ceiling /\ G mod 8 = 0 /\
4096 <= G' /\ G' + 40 <= alloc_ceiling /\ G' mod 8 = 0 /\
4096 <= AR /\ AR + 24 <= G' /\ G' + 40 <= AR + 4096 /\ AR + 4096 <= alloc_ceiling /\ AR mod 4096 = 0 /\
4096 <= PM /\ PM mod 16 = 0 /\ PM + 16 + ST * i' = GM /\ GM + ST <= alloc_ceiling /\ 16 <= ST /\ 0 <= ST * i' /\
0 <= sc < 48 /\ 0 <= am_last am1 <= 31 /\ 0 <= meta_bits am1 < 2 ^ 64 /\
0 <= sc' < 48 /\ 0 <= am_last am' <= 31 /\ 0 <= i' <= am_last am' /\ 0 <= meta_bits am' < 2 ^ 64 /\
0 <= am_avail am' < 2 ^ 32 /\ 0 <= am_freed am' < 2 ^ 32 /\ 0 <= h16 <= 65535 /\ 16 * h16 = ST * i' /\
0 <= am_maplen am' < 2 ^ 40 /\ 1 <= scl_of sc' <= 8191 /\
(CEIL_MIN <= alloc_ceiling <= CEIL_MAX)   /\ alloc_ceiling + 96 + 96 * Z.of_nat fuel <= SP0 /\ SP0 < 2 ^ 63 /\
(G + 40 <= G' \/ G' + 40 <= G).
Proof.
pose proof g_facts3 as (G1 & G2 & G8 & _). destruct (key_facts (g :: X) None U1 L s1 md HI1 LG1 g' _ Mg') as (P1 & P2 & P8 & _).
pose proof AR_facts as (A1 & A2 & A3 & A4 & A5 & _). pose proof parent_facts as (F1 & F2 & F3 & _ & _ & _ & _ & _ & F9 & F10 & F11 & F12 & F13 & F14 & F15 & _).
destruct geo_facts as (AG & AR0 & RLO & RLEN & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R4096 & Rceil & _ & _ & RPM & PM16 & EGM & GMhi & EXT & _).
pose proof sp_facts3 as (_ & S2 & S3 & _). pose proof (proj1 alloc_ceiling_val) as HCV.
pose proof (keys_apart (g :: X) None U1 L s1 HI1 HL1 g g' _ _ Mg1 Mg' ltac:(intros E; exact (Hg'g (eq_sym E)))) as GG'.
assert (B1 : 0 <= meta_bits am1 < 2 ^ 64) by (rewrite Ebits; split; [apply bits_nonneg | apply bits_lt64]; unfold sc in *; lia).
pose proof (extent_pos _ _ _ _ _ (inv_groups HI1 g' am' Ug')). unfold IB in *. unfold sc, sc', G, G', PM, GM, SP0 in *.
repeat match goal with |- _ /\ _ => split end; try assumption; try lia; nia.
Qed.
Lemma XRN : forall k, 0 <= xvN k < 2 ^ 64.
Proof.
intros k. pose proof lin as LIN. pose proof Hsec as SECR. unfold xvN. destruct (k <? 32)%nat; [apply u64_range|].
assert (M64 : forall q, 0 <= q mod 2 ^ 64 < 2 ^ 64) by (intros q; apply Z.mod_pos_bound; lia).
unfold CTX, TBL, src0_D_malloc_context, src0_D_size_classes. unfold sc, sc', G', PM, GM in *.
do 80 (destruct k as [|k]; [first [apply M64 | lia | nia] |]). lia.
Qed.
Lemma EG : xvN 10 = G.
Proof.
pose proof (nm_a0 _ _ _ _ _ _ _ _ _ _ _ _ NM) as R. pose proof lin as LIN.
unfold xvN. cbn [Nat.ltb Nat.leb]. rewrite R. apply lit64_small. unfold G in *. lia.
Qed.
Lemma ESP : xvN 2 = SP0 - 96.
Proof.
pose proof (nm_sp _ _ _ _ _ _ _ _ _ _ _ _ NM) as R. pose proof lin as LIN.
unfold xvN. cbn [Nat.ltb Nat.leb]. rewrite R. apply lit64_small. unfold SP0 in *. lia.
Qed.
Ltac factsN := pose proof XRN as XR0; pose proof EG as EG0; pose proof ESP as ESP0; pose proof lin as LIN.
Ltac denN :=
let xr := match goal with H : forall k : nat, 0 <= xvN k < 2 ^ 64 |- _ => H end in
unfold SCX, MLCHKP;
cbn [sv_denot]; rewrite ?alu64_and, ?alu64_or, ?alu64_srl, ?alu64_sll, ?alu64_add, ?alu64_sub;
rewrite ?alu64_and, ?alu64_or, ?alu64_srl, ?alu64_sll, ?alu64_add, ?alu64_sub;
rewrite ?(ew_EV xvN xr);
unfold aNG, aGMEM, aGBITS, aSC, aACT, aUSG, aLAST, aPG, aPM, aH3, aH16, aPBITS, aPAV, aPFR, aAREA, aPSC, aPSCL, aPTQ2, aPML, aPI, aPLAST;
unfold xvN; cbn [Nat.ltb Nat.leb nat_to_reg]; rewrite ?Z.add_0_r.
Ltac weq := apply (proj2 (word_eq _ _)).
Ltac cprep := unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite ?branch_geu, ?branch_ltu, ?branch_eq, ?branch_ne.
Lemma regsN_ok : regs_ok (EV xvN) (regs_lit [(18%nat, CTX)]) regs1.
Proof.
pose proof (nm_s2 _ _ _ _ _ _ _ _ _ _ _ _ NM) as R18.
apply regs_ok_lit. intros n Hn.
do 32 (destruct n as [|n]; [cbn [find fst Nat.eqb]; first [exact R18 | unfold xvN; cbn [Nat.ltb Nat.leb]; symmetry; apply Z_to_bv_bv_unsigned] |]). lia.
Qed.
Lemma atomsN_ok : atoms_ok (EV xvN) (n_atoms m).
Proof.
factsN. clear LIN. pose proof lin as (G1 & G2 & G8 & P1 & P2 & P8 & A1 & A3 & A4 & A5 & A6 & M1 & M16 & EGM & GMhi & S16 & STi & Hsc0 & Hl1 & B1 & Hsc1 & Hl2 & Hi2 & B2 & AV & FR & H16 & H16' & ML & SCL & HCV & Sceil & S63 & GG').
assert (M64 : forall q, 0 <= q mod 2 ^ 64 <= 2 ^ 64 - 1) by (intros q; pose proof (Z.mod_pos_bound q (2 ^ 64) ltac:(lia)); lia).
assert (GM16 : GM mod 16 = 0).
{ rewrite <- EGM. pose proof parent_facts as (_&_&_&_&_&_&_&_&_&ST16&_). pose proof M16 as M16'.
apply Z.div_exact in ST16; [|lia]. apply Z.div_exact in M16'; [|lia].
replace (PM + 16 + ST * i') with ((PM / 16 + 1 + ST / 16 * i') * 16) by lia. apply Z_mod_mult. }
unfold n_atoms. apply atoms_ok_app.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite !(ew_EV xvN XR0). unfold aNG. rewrite EG0.
unfold aGMEM, aGBITS, aSC, aLAST, aACT, aUSG, aPG, aPM, aH3, aH16, aPBITS, aPAV, aPFR, aAREA, aPSC, aPSCL, aPTQ2, aPI, aPLAST, xvN. cbn [Nat.ltb Nat.leb].
change (2 ^ 3) with 8. change (2 ^ 4) with 16. change (2 ^ 0) with 1. change (2 ^ 1) with 2. rewrite ?Z.mod_1_r. pose proof (M64 (usage_of A sc)).
unfold CTX, src0_D_malloc_context, TBL, src0_D_size_classes. unfold sc, sc', G, G', PM, GM in *.
repeat split; try lia.
+ apply ctx_al8.
+ apply tbl_al2.
- unfold m. destruct (Z.ltb_spec 0 (am_maplen am')); cbn [atoms_ok]; [|exact I].
unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite !(ew_EV xvN XR0). unfold aPML, xvN. cbn [Nat.ltb Nat.leb].
change (2 ^ 0) with 1. rewrite ?Z.mod_1_r. repeat split; lia.
Qed.
Lemma off_img_range a0 ln : (forall x, a0 <= x < a0 + ln -> ~ in_img B1 x) -> 0 < ln -> a0 + ln <= 0x10000 \/ 0x51000 <= a0.
Proof.
intros Ho Hln. destruct (img_gap 0x10000 (0x51000 - 0x10000) a0 ln ltac:(intros x Hx; unfold in_img1; lia) ltac:(lia) Ho Hln); lia.
Qed.
Lemma sep :
exists AG RLO RLEN,
AG + 24 <= G /\ G + 40 <= AG + 4096 /\ (AG = AR \/ AG + 4096 <= AR \/ AR + 4096 <= AG) /\
RLO <= PM /\ GM + ST <= RLO + RLEN /\
(AG + 4096 <= RLO \/ RLO + RLEN <= AG) /\ (AR + 4096 <= RLO \/ RLO + RLEN <= AR) /\
(RLO + RLEN <= 0x10000 \/ 0x51000 <= RLO) /\ (AR + 4096 <= 0x10000 \/ 0x51000 <= AR) /\ (AG + 4096 <= 0x10000 \/ 0x51000 <= AG) /\
(forall y, RLO <= y < RLO + RLEN -> present mem1 y) /\ RLO = ly_reg L (prid (am_mem am')).
Proof.
destruct geo_facts as (AG & AR0 & RLO & RLEN & AGal & AG4096 & AG1 & AG2 & AGceil & AGimg & _ & _ & (k & Hk & EG') & EAR & _ & ARimg & _ & _ & Q7 & _ & R4096 & Rceil & Rimg & Rpres & RPM & _ & EGM & GMhi & EXT & ERLO & Q11 & Q12).
assert (E : AR = AR0) by (unfold AR; rewrite EAR; reflexivity).
rewrite E. exists AG, RLO, RLEN.
pose proof (extent_pos _ _ _ _ _ (inv_groups HI1 g' am' Ug')) as EP.
repeat match goal with |- _ /\ _ => split end; try assumption; try (unfold IB in *; lia).
- apply off_img_range; [exact Rimg | unfold IB in *; lia].
- apply off_img_range; [exact ARimg | lia].
- apply off_img_range; [exact AGimg | lia].
Qed.
Lemma U_SELFP : bv_unsigned (sv_denot (EV xvN) SELFP) = sx32 (2 ^ i').
Proof.
factsN. unfold SELFP.
change (sv_denot (EV xvN) (SAluw ALU_SLL (SLit 1) (SOff aPI 0))) with (sext 64 (alu32 ALU_SLL (low32 (sv_denot (EV xvN) (SLit 1))) (low32 (sv_denot (EV xvN) (SOff aPI 0))))).
rewrite sllw_rr_unsigned, (den_off0 _ XR0), U_lit, (lit64_small (xvN aPI)) by apply XR0. change (1 mod 2 ^ 64) with 1.
unfold aPI, xvN. cbn [Nat.ltb Nat.leb]. rewrite sllw_1 by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma aliasN_ok : alias_ok (EV xvN) (n_alias m).
Proof.
factsN. clear LIN. pose proof lin as (G1 & G2 & G8 & P1 & P2 & P8 & A1 & A3 & A4 & A5 & A6 & M1 & M16 & EGM & GMhi & S16 & STi & Hsc0 & Hl1 & B1 & Hsc1 & Hl2 & Hi2 & B2 & AV & FR & H16 & H16' & ML & SCL & HCV & Sceil & S63 & GG').
pose proof AR_facts as (_&_&_&_&_&_&_&_& HAR).
unfold n_alias. cbn [alias_ok]. repeat match goal with |- _ /\ _ => split end; try exact I; weq; denN;
unfold CTX, src0_D_malloc_context, TBL, src0_D_size_classes; rewrite ?(lit64_unsigned (-4096)); rewrite ?lit64_small by lia.
- change (52 mod 64) with 52. change (58 mod 64) with 58. rewrite Ebits. apply bits_sc; unfold sc in *; lia.
- change (3 mod 64) with 3. unfold sll64. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. rewrite Z.mod_small by lia. unfold sc. lia.
- change (12 mod 64) with 12. change (0 mod 2 ^ 64) with 0. rewrite Ebits. apply bits_shiftr12; unfold sc in *; lia.
- replace (i' + 192) with (i' + 32 * 6) by lia. apply land31; lia.
- change (4 mod 64) with 4. unfold sll64, sub64. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16. rewrite (Z.mod_small (h16 * 16)) by lia.
unfold GM, PM in *. rewrite Z.mod_small by lia. lia.
- change ((-4096) mod 2 ^ 64) with (2 ^ 64 - 4096). unfold G' in HAR. exact HAR.
- rewrite Ebits'. apply bits_land31; unfold sc' in *; lia.
- change (52 mod 64) with 52. change (58 mod 64) with 58. rewrite Ebits'. apply bits_sc; unfold sc' in *; lia.
- change (1 mod 64) with 1. unfold sll64. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. rewrite Z.mod_small by lia. unfold sc'. lia.
- unfold m. destruct (Z.ltb_spec 0 (am_maplen am')); denN; rewrite ?lit64_small by lia; change (12 mod 64) with 12; rewrite Ebits', bits_shiftr12 by (unfold sc' in *; lia); [reflexivity|].
change (0 mod 2 ^ 64) with 0. lia.
Qed.
Lemma condsN_ok : conds_ok (EV xvN) (n_conds m).
Proof.
factsN. clear LIN. pose proof lin as (G1 & G2 & G8 & P1 & P2 & P8 & A1 & A3 & A4 & A5 & A6 & M1 & M16 & EGM & GMhi & S16 & STi & Hsc0 & Hl1 & B1 & Hsc1 & Hl2 & Hi2 & B2 & AV & FR & H16 & H16' & ML & SCL & HCV & Sceil & S63 & GG').
pose proof parent_facts as (_ & _ & _ & Tav & Tfr & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [C1 C2] & C3). pose proof U_SELFP as US.
assert (BIT : forall (mm : Z) (a : nat), 0 <= mm < 2 ^ 32 -> Z.testbit mm i' = false -> xvN a = mm ->
acond_ok (EV xvN) (mkAC BC_EQ (SAlu ALU_AND (SExt true 32 (SOff a 0)) SELFP) (SLit 0))).
{ intros mm a Hmm Hb Ea. unfold acond_ok; cbn [ac_c ac_a ac_b]. rewrite branch_eq. apply Z.eqb_eq.
change (sv_denot (EV xvN) (SAlu ALU_AND (SExt true 32 (SOff a 0)) SELFP)) with (alu64 ALU_AND (sv_denot (EV xvN) (SExt true 32 (SOff a 0))) (sv_denot (EV xvN) SELFP)).
rewrite alu64_and, US, (U_sext32 xvN), (U_off0 _ XR0), Ea, U_lit. change (0 mod 2 ^ 64) with 0.
destruct (land_sx32_bit mm i' ltac:(lia) ltac:(lia)) as [-> E]. apply (proj2 E). exact Hb. }
unfold n_conds. apply conds_ok_app.
- cbn [conds_ok]. split; [| split; [| split; [| split; [| split; [| exact I]]]]].
+ cprep. denN. rewrite !lit64_small by lia. apply negb_true_iff. apply Z.ltb_ge. lia.
+ apply (BIT (am_avail am') aPAV); [lia | exact Tav | reflexivity].
+ apply (BIT (am_freed am') aPFR); [lia | exact Tfr | reflexivity].
+ cprep. denN. rewrite mul64_unsigned, !lit64_small by lia. apply negb_true_iff. apply Z.ltb_ge. unfold mul64.
assert (0 <= scl_of sc' * i' <= 8191 * 31) by nia. rewrite Z.mod_small by lia. lia.
+ cprep. cbn [sv_denot]. rewrite mul64_unsigned, ?(ew_EV xvN XR0). unfold aH16, aPI, aPSCL, xvN. cbn [Nat.ltb Nat.leb]. rewrite ?Z.add_0_r, !lit64_small by lia.
apply Z.ltb_lt. unfold mul64. assert (0 <= (i' + 1) * scl_of sc' <= 32 * 8191) by nia. rewrite Z.mod_small by lia. lia.
- unfold m. destruct (Z.ltb_spec 0 (am_maplen am')); cbn [conds_ok]; [|exact I]. split; [|exact I].
destruct (C3 ltac:(lia)) as [C4 _].
cprep. unfold MLCHKP. denN. rewrite (lit64_unsigned (-1)), !lit64_small by lia. change (8 mod 64) with 8.
apply negb_true_iff. apply Z.ltb_ge. unfold sll64, add64. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
rewrite (Z.mod_small (am_maplen am' * 256)) by lia.
replace (am_maplen am' * 256 + (2 ^ 64 - 1)) with ((am_maplen am' * 256 - 1) + 1 * 2 ^ 64) by lia. rewrite Z.mod_add, Z.mod_small by lia. lia.
Qed.
Lemma factsN_ok : facts_ok (EV xvN) (mkFacts (n_atoms m) (n_conds m) (n_alias m)).
Proof. split; [apply atomsN_ok | split; [apply condsN_ok | apply aliasN_ok]]. Qed.
Lemma group_cell_memX q a c : usedX (g :: X) s1 q a -> In c (group_cells q a) -> cell_mem B1 L mem1 c.
Proof.
intros Uq Hc. apply (CELL (g :: X) L s1 mem1 MR1). unfold imageX. apply in_app_iff. right. apply in_app_iff. right.
apply in_flat_map. exists (q, a). split; [|exact Hc].
unfold used_metasX. apply filter_In. split; [| cbn [fst]; rewrite (proj2 (usedX_MT _ _ _ _ Uq)); reflexivity].
apply (used_metas_iff s1 q a (proj1 (inv_keys HI1))). exact (proj1 (usedX_MT _ _ _ _ Uq)).
Qed.
Lemma bytesN :
bytes_are mem1 (G + 16) 8 GM /\ bytes_are mem1 (G + 32) 8 (meta_bits am1) /\
bytes_are mem1 (CTX + 464 + 8 * sc) 8 (usage_of A sc) /\
bytes_are mem1 (GM - 4) 1 0 /\ bytes_are mem1 (GM - 3) 1 (i' + 192) /\ bytes_are mem1 (GM - 2) 2 h16 /\
bytes_are mem1 PM 8 G' /\
bytes_are mem1 (G' + 16) 8 PM /\ bytes_are mem1 (G' + 24) 4 (am_avail am') /\ bytes_are mem1 (G' + 28) 4 (am_freed am') /\ bytes_are mem1 (G' + 32) 8 (meta_bits am') /\
bytes_are mem1 AR 8 (ly_sec L) /\ bytes_are mem1 CTX 8 (ly_sec L)   /\ bytes_are mem1 (TBL + 2 * sc') 2 (scl_of sc').
Proof.
pose proof parent_facts as (_ & _ & _ & _ & _ & Hhdr & _). pose proof AR_facts as (_&_&_&_&_&_&_& Bar & _). pose proof Hctx as HC. pose proof Hsec as HS.
assert (BYg : forall dd w val, match val with VLo5 _ => False | _ => True end -> In (MCell (LMem (padd g dd)) w val) (meta_slot_cells g (Some (MUsed am1))) ->
bytes_are mem1 (G + dd) w (sval_num L val)).
{ intros dd w val Hv Hc kk Hkk. pose proof (key_cell (g :: X) None U1 L s1 mem1 HI1 MR1 g _ _ Mg1 Hc) as C. unfold cell_mem in C. cbn [mc_val mc_loc mc_w] in C.
rewrite loc_addr_padd in C. destruct val; first [exact (C kk Hkk) | destruct Hv]. }
assert (BYg' : forall dd w val, match val with VLo5 _ => False | _ => True end -> In (MCell (LMem (padd g' dd)) w val) (meta_slot_cells g' (Some (MUsed am'))) ->
bytes_are mem1 (G' + dd) w (sval_num L val)).
{ intros dd w val Hv Hc kk Hkk. pose proof (key_cell (g :: X) None U1 L s1 mem1 HI1 MR1 g' _ _ Mg' Hc) as C. unfold cell_mem in C. cbn [mc_val mc_loc mc_w] in C.
rewrite loc_addr_padd in C. destruct val; first [exact (C kk Hkk) | destruct Hv]. }
assert (BYs : forall dd w z, In (MCell (LMem (padd (slot_start am' i') dd)) w (VZ z)) (slot_cells am' i') -> bytes_are mem1 (GM + dd) w z).
{ intros dd w z Hc kk Hkk. pose proof (group_cell_memX g' am' _ Ug' (In_group_slot g' am' i' _ Hi' Hc)) as C. unfold cell_mem in C. cbn [mc_val mc_loc mc_w sval_num] in C.
rewrite loc_addr_padd in C. unfold GM. rewrite Emem. exact (C kk Hkk). }
repeat match goal with |- _ /\ _ => split end.
- pose proof (BYg 16 8%nat (VP (am_mem am1)) I ltac:(cbn; tauto)) as B. exact B.
- exact (BYg 32 8%nat (VZ (meta_bits am1)) I ltac:(cbn; tauto)).
- pose proof (ctx_usage_cell (g :: X) L s1 mem1 HC MR1 (Z.to_nat sc) ltac:(unfold sc in *; lia)) as C.
rewrite Z2Nat.id in C by (unfold sc in *; lia). unfold usage_of, znth. rewrite <- Eus. exact C.
- replace (GM - 4) with (GM + -4) by lia. apply BYs. unfold slot_cells. left. reflexivity.
- replace (GM - 3) with (GM + -3) by lia. apply BYs. unfold slot_cells. rewrite Hhdr. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity.
- replace (GM - 2) with (GM + -2) by lia. apply BYs. unfold slot_cells. rewrite Hhdr. apply in_app_iff. right. apply in_app_iff. left. right. left. reflexivity.
- pose proof (group_cell_memX g' am' _ Ug' ltac:(unfold group_cells; left; reflexivity)) as C. unfold cell_mem in C. cbn [mc_val mc_loc mc_w sval_num] in C. exact C.
- exact (BYg' 16 8%nat (VP (am_mem am')) I ltac:(cbn; tauto)).
- exact (BYg' 24 4%nat (VZ (am_avail am')) I ltac:(cbn; tauto)).
- exact (BYg' 28 4%nat (VZ (am_freed am')) I ltac:(cbn; tauto)).
- exact (BYg' 32 8%nat (VZ (meta_bits am')) I ltac:(cbn; tauto)).
- exact Bar.
- assert (Hc : In (MCell (LCtx CTX_secret) 8 (if st_init_done s1 then VSec else VZ 0)) (ctx_cells s1)) by (unfold ctx_cells; apply in_app_iff; left; left; reflexivity).
pose proof (CELL (g :: X) L s1 mem1 MR1 _ ltac:(unfold imageX; apply in_app_iff; left; exact Hc)) as C.
unfold cell_mem in C. cbn [mc_val mc_loc mc_w loc_addr] in C. rewrite HC in C. unfold CTX_secret in C. rewrite Z.add_0_r in C.
assert (Hinit : st_init_done s1 = true).
{ destruct (st_init_done s1) eqn:Ei; [reflexivity|]. exfalso.
pose proof (inv_ctx HI1) as IM. destruct IM as (_&_&_&_&_&_&_&_&_&_&_& IM0).
destruct (IM0 Ei) as (EM & _). pose proof Mg1 as MG. unfold MT in MG. rewrite EM in MG. cbn in MG. discriminate MG. }
rewrite Hinit in C. cbn [sval_num] in C. exact C.
- exact (tq_bytes mem1 SO ST1 sc' Hsc').
Qed.
Lemma regionsN_ok : Forall (region_ok src0segs (EV xvN) mem1) (n_mem m).
Proof.
factsN. clear LIN. pose proof lin as (G1 & G2 & G8 & P1 & P2 & P8 & A1 & A3 & A4 & A5 & A6 & M1 & M16 & EGM & GMhi & S16 & STi & Hsc0 & Hl1 & B1 & Hsc1 & Hl2 & Hi2 & B2 & AV & FR & H16 & H16' & ML & SCL & HCV & Sceil & S63 & GG').
pose proof SO as SO0. pose proof bytesN as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14).
destruct sep as (AG & RLO & RLEN & _ & _ & _ & RPM & GMR & _ & _ & _ & _ & _ & PRES & _).
assert (M64 : forall q, 0 <= q mod 2 ^ 64 < 2 ^ (8 * Z.of_N 8)) by (intros q; apply Z.mod_pos_bound; cbn; lia).
assert (PG : forall y, G <= y < G + 40 -> present mem1 y) by (intros y Hy; exact (key_present (g :: X) None U1 L s1 mem1 md HI1 MR1 LG1 g _ y Mg1 Hy)).
unfold n_mem. repeat apply Forall_cons; [| | | | | | | | apply Forall_nil].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_gM]; rewrite (base_val_EV _ XR0); unfold aNG; rewrite EG0; [lia | lia | intros o Ho; lia |].
repeat apply Forall_cons; [| | apply Forall_nil].
+ apply (chunk_ok_val _ _ _ _ 8%N _ GM); [apply (U_off0 _ XR0) | change (8 * Z.of_N 8) with 64; lia | exact Y1].
+ apply (chunk_ok_val _ _ _ _ 8%N _ (meta_bits am1)); [apply (U_off0 _ XR0) | change (8 * Z.of_N 8) with 64; lia | exact Y2].
- pose proof (so_ctx_lo _ SO0) as CL. pose proof (so_ctx_hi _ SO0) as CH. cbn [ms_ctx src0_msyms] in CL, CH. fold CTX in CL, CH. unfold CTX_SIZE in CH.
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_usgw]; rewrite (base_val_EV _ XR0); unfold aACT, xvN; cbn [Nat.ltb Nat.leb]; [unfold sc in *; lia | unfold sc in *; lia | |].
+ intros o Ho. apply (ctx_writable mem1 SO0). unfold CTX_SIZE. unfold sc in *. lia.
+ apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_val _ _ _ _ 8%N _ (usage_of A sc mod 2 ^ 64)); [apply (U_off0 _ XR0) | apply M64 |].
intros kk Hkk. rewrite le_byte_mod64. replace (CTX + 80 + 8 * sc + 384) with (CTX + 464 + 8 * sc) by lia. exact (Y3 kk Hkk).
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_nm]; rewrite (base_val_EV _ XR0); unfold aGMEM; change (xvN 43) with GM; [lia | lia | |].
+ intros o Ho. apply present_writable. apply PRES. lia.
+ repeat apply Forall_cons; [| | | apply Forall_nil].
* apply (chunk_ok_val _ _ _ _ 1%N _ 0); [apply U_lit | cbn; lia | replace (GM + -4) with (GM - 4) by lia; exact Y4].
* apply (chunk_ok_val _ _ _ _ 1%N _ (i' + 192)); [apply (U_off0 _ XR0) | change (8 * Z.of_N 1) with 8; lia | replace (GM + -3) with (GM - 3) by lia; exact Y5].
* apply (chunk_ok_val _ _ _ _ 2%N _ h16); [apply (U_off0 _ XR0) | change (8 * Z.of_N 2) with 16; lia | replace (GM + -2) with (GM - 2) by lia; exact Y6].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_pgrp]; rewrite (base_val_EV _ XR0); unfold aPM; change (xvN 66) with PM; [lia | lia | intros o Ho; lia |].
apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_val _ _ _ _ 8%N _ G'); [apply (U_off0 _ XR0) | change (8 * Z.of_N 8) with 64; lia | rewrite Z.add_0_r; exact Y7].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_pmeta]; rewrite (base_val_EV _ XR0); unfold aPG; change (xvN 65) with G'; [lia | lia | intros o Ho; lia |].
repeat apply Forall_cons; [| | | | apply Forall_nil].
+ apply (chunk_ok_val _ _ _ _ 8%N _ PM); [apply (U_off0 _ XR0) | change (8 * Z.of_N 8) with 64; lia | exact Y8].
+ apply (chunk_ok_val _ _ _ _ 4%N _ (am_avail am')); [apply (U_off0 _ XR0) | change (8 * Z.of_N 4) with 32; lia | exact Y9].
+ apply (chunk_ok_val _ _ _ _ 4%N _ (am_freed am')); [apply (U_off0 _ XR0) | change (8 * Z.of_N 4) with 32; lia | exact Y10].
+ apply (chunk_ok_val _ _ _ _ 8%N _ (meta_bits am')); [apply (U_off0 _ XR0) | change (8 * Z.of_N 8) with 64; lia | exact Y11].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_parea]; rewrite (base_val_EV _ XR0); unfold aAREA; change (xvN 72) with AR; [lia | lia | intros o Ho; lia |].
apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_val _ _ _ _ 8%N _ (ly_sec L)); [apply (U_off0 _ XR0) | change (8 * Z.of_N 8) with 64; pose proof Hsec; lia | rewrite Z.add_0_r; exact Y12].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_ctx0 base_val]; unfold CTX, src0_D_malloc_context; [lia | lia | intros o Ho; lia |].
apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_val _ _ _ _ 8%N _ (ly_sec L)); [apply (U_off0 _ XR0) | change (8 * Z.of_N 8) with 64; pose proof Hsec; lia | rewrite Z.add_0_l; exact Y13].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_ptq]; rewrite (base_val_EV _ XR0); unfold aPTQ2, xvN; cbn [Nat.ltb Nat.leb]; unfold TBL, src0_D_size_classes; [unfold sc' in *; lia | unfold sc' in *; lia | intros o Ho; lia |].
apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_val _ _ _ _ 2%N _ (scl_of sc')); [apply (U_off0 _ XR0) | change (8 * Z.of_N 2) with 16; lia | rewrite Z.add_0_r; exact Y14].
Qed.
Lemma pdN : pairwise_disjoint (EV xvN) (n_mem m).
Proof.
factsN. clear LIN. pose proof lin as (G1 & G2 & G8 & P1 & P2 & P8 & A1 & A3 & A4 & A5 & A6 & M1 & M16 & EGM & GMhi & S16 & STi & Hsc0 & Hl1 & B1 & Hsc1 & Hl2 & Hi2 & B2 & AV & FR & H16 & H16' & ML & SCL & HCV & Sceil & S63 & GG').
destruct sep as (AG & RLO & RLEN & AG1 & AG2 & AGAR & RPM & GMR & AGR & ARR & RI & ARI & AGI & _).
unfold n_mem. cbn [app pairwise_disjoint all_disjoint]. unfold extent_disjoint.
cbn [r_base r_lo r_hi reg_gM reg_usgw reg_nm reg_pgrp reg_pmeta reg_parea reg_ctx0 reg_ptq]. rewrite !(base_val_EV _ XR0). cbn [base_val].
unfold aNG. rewrite EG0. unfold aACT, aGMEM, aPM, aPG, aAREA, aPTQ2, xvN. cbn [Nat.ltb Nat.leb].
unfold CTX, TBL, src0_D_malloc_context, src0_D_size_classes. unfold G, G', PM, GM, sc, sc' in *.
clear XR0 EG0 ESP0 NM HI1 Mg1 AO1 Ug' Hfr' Hk' Emem HI3.
repeat split;
first [ (clear AGAR AGR ARR RI ARI AGI GG'; lia)
| (clear AGR ARR RI ARI AGI GG'; lia)
| (clear AGAR ARR RI ARI AGI GG'; lia)
| (clear AGAR AGR RI ARI AGI GG'; lia)
| (clear AGAR AGR ARR ARI AGI GG'; lia)
| (clear AGAR AGR ARR RI AGI GG'; lia)
| (clear AGAR AGR ARR RI ARI GG'; lia)
| (clear AGAR AGR ARR RI ARI AGI; lia)
| lia ].
Qed.
Theorem memN_ok : mem_ok src0segs (EV xvN) mem1 (n_mem m).
Proof. split; [unfold m; destruct (0 <? am_maplen am'); vm_compute; reflexivity|]. split; [apply regionsN_ok | apply pdN]. Qed.
Theorem N_entry_st_ok : st_ok src0segs (EV xvN) (ss_N m) (mkst regs1 (Z_to_bv 64 XU) mem1 (seg_rom src0segs)).
Proof.
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_resv ss_regs ss_mem ss_facts ss_N resv_denot].
repeat (split; [reflexivity|]). split; [apply regsN_ok|]. split; [apply memN_ok | apply factsN_ok].
Qed.
Lemma flat_map_ext_In {T1 T2} (f f' : T1 -> list T2) l : (forall x, In x l -> f x = f' x) -> flat_map f l = flat_map f' l.
Proof.
induction l as [|x t IH]; intros Hf; [reflexivity|]. cbn. rewrite (Hf x) by (left; reflexivity). rewrite IH by (intros y Hy; apply Hf; right; exact Hy). reflexivity.
Qed.
Lemma forget_cells q : group_cells q (am_forget am' i') = group_cells q am' /\ group_tail_cells (am_forget am' i') = group_tail_cells am' /\
meta_slot_cells q (Some (MUsed (am_forget am' i'))) = meta_slot_cells q (Some (MUsed am')).
Proof.
pose proof parent_facts as (Plast & _ & _ & _ & _ & Hhdr & Hoff & _).
pose proof (inv_groups HI1 g' am' Ug') as ((_ & _ & Glen & _) & _).
pose proof (upd_slot_fields am' i' (mkSlot (ss_hdr (nth_slot am' i')) None)) as (Fm & Fl & Fsc & Fml & Fst & Fex & Fss). fold (am_forget am' i') in Fm, Fl, Fsc, Fml, Fst, Fex, Fss.
assert (NS : forall j, 0 <= j -> nth_slot (am_forget am' i') j = if j =? i' then mkSlot (ss_hdr (nth_slot am' i')) None else nth_slot am' j).
{ intros j Hj. unfold am_forget. apply nth_slot_upd_slot; [lia | lia | rewrite Glen; lia]. }
assert (SC : forall j, 0 <= j -> slot_cells (am_forget am' i') j = slot_cells am' j).
{ intros j Hj. unfold slot_cells. rewrite Fss, (NS j Hj). destruct (Z.eqb_spec j i'); [|reflexivity]. subst j. cbn [ss_hdr ss_fr]. rewrite Hfr'.
replace (fr_off fr' =? 0) with true by (symmetry; apply Z.eqb_eq; exact Hoff). reflexivity. }
pose proof (upd_slot_fields2 am' i' (mkSlot (ss_hdr (nth_slot am' i')) None)) as (Faidx & Fav & Ffr & Fpr & Fnx). fold (am_forget am' i') in Faidx, Fav, Ffr, Fpr, Fnx.
split; [|split].
- unfold group_cells. rewrite Fm, Fml, Faidx, Fl. f_equal. apply flat_map_ext_In. intros j Hj. apply In_zseq in Hj. apply SC. lia.
- unfold group_tail_cells. rewrite Fm, Fex, Fl. f_equal. apply flat_map_ext_In. intros j Hj. apply In_zseq in Hj.
unfold frame_tail_cells. rewrite (NS j ltac:(lia)). destruct (Z.eqb_spec j i'); [|reflexivity]. subst j. cbn [ss_fr]. rewrite Hfr', Hk'. reflexivity.
- cbn [meta_slot_cells]. rewrite Fpr, Fnx, Fm, Fav, Ffr. unfold meta_bits. rewrite Fl, Fsc, Fml. reflexivity.
Qed.
Lemma s3_facts :
st_metas s2 = st_metas s1 /\ footprint s3 = footprint s1 /\ st_regions s3 = st_regions s1 /\ st_areas s3 = st_areas s1 /\ st_brk s3 = st_brk s1 /\
MT s3 g = Some (MUsed am1) /\ MT s2 g' = Some (MUsed am') /\
st_usage s3 = zset sc (usage_of A sc - (am_last am1 + 1)) (st_usage s1) /\
(forall c, In c (ctx_cells s2) -> c = usage_cell (Z.to_nat sc) (usage_of A sc - (am_last am1 + 1)) \/ In c (ctx_cells s1)) /\
In (usage_cell (Z.to_nat sc) (usage_of A sc - (am_last am1 + 1))) (ctx_cells s3).
Proof.
pose proof (inv_ctx HI1) as (_ & Lu & _).
assert (E2 : s2 = set_usage (zset sc (usage_of A sc - (am_last am1 + 1)) (st_usage s1)) s1).
{ unfold s2, A_usg. replace (sc <? 48) with true by (symmetry; apply Z.ltb_lt; unfold sc; lia). reflexivity. }
unfold s3. rewrite E2. rewrite footprint_upd_meta. cbn [st_metas st_regions st_areas st_brk st_usage upd_meta set_usage set_metas footprint].
repeat match goal with |- _ /\ _ => split end; try reflexivity.
- rewrite MT_upd_other by (intros E; exact (Hg'g (eq_sym E))). exact Mg1.
- exact Mg'.
- intros c Hc. destruct (ctx_cells_usq s1 (set_usage (zset sc (usage_of A sc - (am_last am1 + 1)) (st_usage s1)) s1) c) as [E|[(k & Hk & ->)|[(k & Hk & ->)|H]]]; try reflexivity; try exact Hc.
+ right. rewrite E. unfold seq_cell, ctx_cells. apply in_app_iff. left. cbn. tauto.
+ cbn [st_usage set_usage]. unfold zset. rewrite nth_zupd, Lu. destruct (Nat.eqb_spec k (Z.to_nat sc)).
* subst k. replace (Nat.ltb (Z.to_nat sc) 48) with true by (symmetry; apply Nat.ltb_lt; lia). cbn [andb]. left. reflexivity.
* cbn [andb]. right. unfold ctx_cells. rewrite !in_app_iff. right; right; left. apply in_map_iff. exists k. split; [reflexivity | apply in_seq; lia].
+ right. cbn [st_unmap_seq set_usage]. unfold ctx_cells. rewrite !in_app_iff. right; right; right; left. apply in_map_iff. exists k. split; [reflexivity | apply in_seq; lia].
+ right. exact H.
- rewrite ctx_cells_upd_meta. unfold ctx_cells. rewrite !in_app_iff. right; right; left. apply in_map_iff. exists (Z.to_nat sc).
cbn [st_usage set_usage]. unfold usage_cell, zset. rewrite nth_zupd, Nat.eqb_refl, Lu.
replace (Nat.ltb (Z.to_nat sc) 48) with true by (symmetry; apply Nat.ltb_lt; unfold sc in *; lia). split; [reflexivity | apply in_seq; unfold sc in *; lia].
Qed.
Definition NEWN : list mcell := [usage_cell (Z.to_nat sc) (usage_of A sc - (am_last am1 + 1))].
Lemma cells3 c : In c (imageX (g :: X) s3 ++ tail_cellsX (g :: X) s3) -> In c NEWN \/ In c (imageX (g :: X) s1 ++ tail_cellsX (g :: X) s1).
Proof.
pose proof s3_facts as (Em2 & _ & _ & Ea3 & _ & _ & Mg'2 & _ & CTX2 & _). pose proof (forget_cells g') as (GC & TC & MC).
assert (Ea3' : st_areas (upd_meta g' (MUsed (am_forget am' i')) s2) = st_areas s1) by exact Ea3.
assert (EUM : used_metasX (g :: X) s2 = used_metasX (g :: X) s1) by (unfold used_metasX, used_metas; rewrite Em2; reflexivity).
assert (OLD : forall c', In c' (meta_slot_cells g' (Some (MUsed am'))) -> In c' (imageX (g :: X) s1 ++ tail_cellsX (g :: X) s1)).
{ intros c' Hc'. exact (key_old_cell (g :: X) None U1 s1 HI1 g' _ c' Mg' Hc'). }
unfold s3, NEWN. intros Hc. apply in_app_iff in Hc as [Hc|Hc].
- unfold imageX in Hc. rewrite ctx_cells_upd_meta, Ea3' in Hc.
apply in_app_iff in Hc as [Hc|Hc]; [destruct (CTX2 c Hc) as [->|H]; [left; left; reflexivity | right; apply in_app_iff; left; unfold imageX; apply in_app_iff; left; exact H]|].
apply in_app_iff in Hc as [Hc|Hc].
+ destruct (areas_cells_upd s2 g' (MUsed (am_forget am' i')) (st_areas s1) c Hc) as [H|H].
* right. apply in_app_iff. left. unfold imageX. apply in_app_iff. right. apply in_app_iff. left. rewrite <- (areas_cells_ext' s1 s2 _ Em2). exact H.
* right. apply OLD. rewrite <- MC. exact H.
+ right. destruct (used_metasX_upd (g :: X) s2 g' am' (am_forget am' i') Mg'2) as (u1 & u2 & E1 & E2x). rewrite E2x in Hc. rewrite EUM in E1.
apply in_app_iff. left. unfold imageX. apply in_app_iff. right. apply in_app_iff. right. rewrite E1.
rewrite !flat_map_app in *. apply in_app_iff in Hc as [H|Hc]; [apply in_app_iff; left; exact H|].
apply in_app_iff. right. apply in_app_iff in Hc as [H|H]; apply in_app_iff; [left | right; exact H].
destruct (memb g' (g :: X)); [destruct H|]. cbn [flat_map fst snd] in *. rewrite GC in H. exact H.
- right. apply in_app_iff. right. unfold tail_cellsX in *.
destruct (used_metasX_upd (g :: X) s2 g' am' (am_forget am' i') Mg'2) as (u1 & u2 & E1 & E2x). rewrite E2x in Hc. rewrite EUM in E1. rewrite E1.
rewrite !flat_map_app in *. apply in_app_iff in Hc as [H|Hc]; [apply in_app_iff; left; exact H|].
apply in_app_iff. right. apply in_app_iff in Hc as [H|H]; apply in_app_iff; [left | right; exact H].
destruct (memb g' (g :: X)); [destruct H|]. cbn [flat_map fst snd] in *. rewrite TC in H. exact H.
Qed.
Section h.
Variable ms2 : machine_state.
Hypothesis HS2 : st_ok src0segs (EV xvN) (SSN m) ms2.
Hypothesis HF2 : frame_of (EV xvN) (n_mem m) mem1 (ms_mem ms2).
Let mem2 := ms_mem ms2.
Let regs2 := ms_regs ms2.
Lemma shapeN : ms2 = mkst regs2 (Z_to_bv 64 src0_A_nontrivial_free) mem2 (seg_rom src0segs).
Proof.
pose proof (SSN_shape m) as SH. pose proof HS2 as HS. remember (SSN m) as ss eqn:Ess. clear Ess.
destruct SH as (Hpc & Hrv & _). rewrite <- Hpc. apply (st_ok_mkst src0segs _ _ _ HS Hrv).
Qed.
Lemma regs2_facts :
(forall k, In k ([2; 9]%nat ++ kept) -> getr regs2 (nat_to_reg k) = getr regs1 (nat_to_reg k)) /\
getr regs2 (nat_to_reg 1) = Z_to_bv 64 XJ /\ getr regs2 (nat_to_reg 8) = Z_to_bv 64 GM /\
getr regs2 (nat_to_reg 10) = Z_to_bv 64 G' /\ getr regs2 (nat_to_reg 11) = Z_to_bv 64 i' /\
getr regs2 (nat_to_reg 18) = Z_to_bv 64 CTX /\ getr regs2 (nat_to_reg 19) = getr regs1 (nat_to_reg 10).
Proof.
factsN.
pose proof (SSN_shape m) as SH. pose proof HS2 as HS. remember (SSN m) as ss eqn:Ess. clear Ess.
destruct SH as (Hpc & Hrv & Hview & _).
pose proof (fun rr => st_ok_reg src0segs _ _ ms2 rr HS) as RR.
unfold view, kept, keptU in Hview. cbn [map app] in Hview.
injection Hview as V1 V2 V8 V9 V10 V11 V18 V19 V3 V4 V20 V21 V22 V23 V24 V25 V26 V27.
assert (NR : forall k, (1 <= k <= 31)%nat -> nat_to_reg k = Z_to_bv 5 (Z.of_nat k)).
{ intros k Hk. clear -Hk. apply bv_eq. rewrite nat_to_reg_unsigned by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. reflexivity. }
assert (K : forall k ex (V : sr_get (ss_regs ss) (Z_to_bv 5 (Z.of_nat k)) = ex), (1 <= k <= 31)%nat -> getr regs2 (nat_to_reg k) = sv_denot (EV xvN) ex).
{ intros k ex V Hk. unfold regs2. rewrite (NR k Hk), (RR (Z_to_bv 5 (Z.of_nat k))), V. reflexivity. }
assert (KE : forall k (V : sr_get (ss_regs ss) (Z_to_bv 5 (Z.of_nat k)) = SOff k 0), (1 <= k <= 31)%nat -> getr regs2 (nat_to_reg k) = getr regs1 (nat_to_reg k)).
{ intros k V Hk. rewrite (K k _ V Hk), (den_off0 _ XR0). unfold xvN. replace (k <? 32)%nat with true by (symmetry; apply Nat.ltb_lt; lia). apply Z_to_bv_bv_unsigned. }
repeat match goal with |- _ /\ _ => split end.
- intros k Hk. cbn [In app] in Hk. repeat (destruct Hk as [<-|Hk]; [eapply KE; [eassumption | lia] |]). destruct Hk.
- rewrite (K 1%nat _ V1 ltac:(lia)). reflexivity.
- rewrite (K 8%nat _ V8 ltac:(lia)), (den_off0 _ XR0). reflexivity.
- rewrite (K 10%nat _ V10 ltac:(lia)), (den_off0 _ XR0). reflexivity.
- rewrite (K 11%nat _ V11 ltac:(lia)), (den_off0 _ XR0). reflexivity.
- rewrite (K 18%nat _ V18 ltac:(lia)). reflexivity.
- rewrite (K 19%nat _ V19 ltac:(lia)), (den_off0 _ XR0). unfold xvN. cbn [Nat.ltb Nat.leb]. apply Z_to_bv_bv_unsigned.
Qed.
Lemma bytes2 :
bytes_are mem2 (CTX + 464 + 8 * sc) 8 (usage_of A sc - (am_last am1 + 1)) /\
(forall k, 0 <= k < 8 -> mbyte src0segs mem2 (GM + k) = Some (Z_to_bv 8 0)) /\
(forall k, 0 <= k < 8 -> writable_at src0segs mem2 (GM + k)).
Proof.
factsN. clear LIN. pose proof lin as (G1 & G2 & G8 & P1 & P2 & P8 & A1 & A3 & A4 & A5 & A6 & M1 & M16 & EGM & GMhi & S16 & STi & Hsc0 & Hl1 & B1 & Hsc1 & Hl2 & Hi2 & B2 & AV & FR & H16 & H16' & ML & SCL & HCV & Sceil & S63 & GG').
pose proof (SSN_shape m) as SH. pose proof HS2 as HS. remember (SSN m) as ss eqn:Ess. clear Ess.
destruct SH as (_ & _ & _ & Hm). pose proof (st_ok_mem_ok _ _ _ _ HS) as (_ & ROK & _). rewrite Hm in ROK. unfold n_mem_out in ROK.
apply Forall_cons_iff in ROK as [_ ROK]. apply Forall_cons_iff in ROK as [Ru ROK]. apply Forall_cons_iff in ROK as [Rn _].
destruct Ru as (_ & _ & _ & Cu). cbn [r_chunks r_base] in Cu. rewrite (base_val_EV _ XR0) in Cu. apply Forall_cons_iff in Cu as [Cu _].
unfold aACT, xvN in Cu. cbn [Nat.ltb Nat.leb] in Cu.
destruct Rn as (_ & _ & Wn & Cn). cbn [r_chunks r_base r_wlo r_whi] in Wn, Cn. rewrite (base_val_EV _ XR0) in Wn, Cn. unfold aGMEM in Wn, Cn. change (xvN 43) with GM in Wn, Cn.
apply Forall_cons_iff in Cn as [C0 _]. unfold mem2.
split; [|split].
- replace (CTX + 464 + 8 * sc) with (CTX + 80 + 8 * sc + 384) by lia.
intros kk Hkk. rewrite <- le_byte_mod64.
apply (chunk_bytes xvN mem2 _ 384 8 _ _ Cu); [| apply Z.mod_pos_bound; cbn; lia | exact Hkk].
change (sv_denot (EV xvN) (SAlu ALU_ADD (SOff aUSG 0) (SAlu ALU_OR (SAlu ALU_XOR (SOff aGBITS 0) (SLit (-1))) (SLit (-32))))) with
(alu64 ALU_ADD (sv_denot (EV xvN) (SOff aUSG 0)) (alu64 ALU_OR (alu64 ALU_XOR (sv_denot (EV xvN) (SOff aGBITS 0)) (sv_denot (EV xvN) (SLit (-1)))) (sv_denot (EV xvN) (SLit (-32))))).
rewrite alu64_add, alu64_or, alu64_xor, !(U_off0 _ XR0), !U_lit. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1). change ((-32) mod 2 ^ 64) with (2 ^ 64 - 32).
unfold aUSG, aGBITS, xvN. cbn [Nat.ltb Nat.leb]. rewrite lor_not_hi5 by lia. rewrite Ebits, bits_mod32 by (unfold sc in *; lia).
unfold add64. rewrite Zplus_mod_idemp_l. replace (usage_of A sc + (2 ^ 64 - 1 - am_last am1)) with ((usage_of A sc - (am_last am1 + 1)) + 1 * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. reflexivity.
- intros k Hk. destruct (C0 k ltac:(cbn; lia)) as (bb & Eb & Mb). cbn [c_off c_val cbyte] in Eb, Mb. rewrite Z.add_0_r in Mb. rewrite Mb.
injection Eb as <-. f_equal. unfold byte_of_word. change (bv_unsigned (sv_denot (EV xvN) (SLit 0))) with 0. rewrite Z.shiftr_0_l. reflexivity.
- intros k Hk. apply Wn. lia.
Qed.
Definition in_winN (a : Z) : Prop := (CTX + 464 + 8 * sc <= a < CTX + 464 + 8 * sc + 8) \/ (GM <= a < GM + 8).
Lemma frameN a : 0 <= a < 2 ^ 64 -> ~ in_winN a -> mem2 (Z_to_bv 64 a) = mem1 (Z_to_bv 64 a).
Proof.
factsN. intros Ha Hw. unfold mem2. apply (HF2 (Z_to_bv 64 a)). intros (rr & Hr & Hin). apply Hw.
rewrite Z_to_bv_unsigned in Hin. unfold bv_wrap in Hin. change (bv_modulus 64) with (2 ^ 64) in Hin. rewrite Z.mod_small in Hin by lia.
unfold n_mem in Hr. unfold in_winN. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];
cbn [reg_gM reg_usgw reg_nm reg_pgrp reg_pmeta reg_parea reg_ctx0 reg_ptq r_base r_wlo r_whi] in Hin; rewrite ?(base_val_EV _ XR0) in Hin; cbn [base_val] in Hin; try lia.
- unfold aACT, xvN in Hin. cbn [Nat.ltb Nat.leb] in Hin. left. lia.
- unfold aGMEM in Hin. change (xvN 43) with GM in Hin. right. lia.
Qed.
Lemma win_ownedN a : in_winN a -> alloc_owned L s1 a.
Proof.
pose proof HL1 as HL0. pose proof Hctx as HC. pose proof lin as LIN. destruct sep as (AG & RLO & RLEN & _ & _ & _ & RPM & GMR & _ & _ & _ & _ & _ & _ & ERLO).
destruct (used_group_region (g :: X) None U1 s1 g' am' HI1 Ug') as (rg & Hr & Hk & Hl & Ho & Hext & _).
intros [W|W].
- apply (ctx_bytes_owned (g :: X) None U1 s1 L HI1 HL0). rewrite HC. unfold CTX_SIZE. unfold sc in *. lia.
-
split.
+ exists (LMem (YO0i.SP (prid (am_mem am')) 0), rg_len rg). split; [apply footprint_region_In; assumption|]. cbn [fst snd loc_addr].
pose proof (slot_in_span (g :: X) None U1 s1 HI1 g' am' i' Ug' Hi') as [S1 S2]. pose proof parent_facts as (_&_&_&_&_&_&_&_& S16 & _).
assert (EGM : GM = ly_reg L (prid (am_mem am')) + poff (slot_start am' i')).
{ unfold GM. rewrite Emem, <- (prid_slot_start am' i'). apply loc_addr_LMem. }
fold ST in S2. unfold UNIT, IB in *. lia.
+ intros (bk & Hb & Hx). pose proof parent_facts as (_&_&_&_&_&_&_&_& S16 & _).
assert (HH : poff (slot_start am' i') + 8 <= poff (slot_start am' i') + stride_of am' - IB) by (unfold IB; unfold ST in S16; lia).
pose proof (slot_body_no_block (g :: X) None U1 s1 L HI1 HL0 g' am' i' (poff (slot_start am' i')) (poff (slot_start am' i') + 8) Ug' Hi'
ltac:(intros f Hf; rewrite Hfr' in Hf; injection Hf as <-; exact Hk') NOSL ltac:(lia) HH bk Hb) as D.
unfold ranges_disjoint, block_range in D. cbn [fst snd] in D. rewrite poff_slot_start in D. fold ST in D. rewrite <- ERLO in D.
pose proof (loc_addr_LMem L (am_mem am')) as EPM. change (loc_addr L (LMem (am_mem am'))) with PM in EPM. rewrite <- ERLO in EPM.
unfold UNIT in *. lia.
Qed.
Lemma HL3 : layout_ok L s3.
Proof. pose proof s3_facts as (_ & Efp & Erg & _). exact (layout_ok_same' L s1 s3 HL1 Erg Efp). Qed.
Theorem memrep3 : memrepX B1 (g :: X) L s3 mem2.
Proof.
pose proof sp_facts3 as (S16 & Sceil & S63 & _). pose proof s3_facts as (_ & Efp & Erg & _ & _ & _ & _ & _ & _ & UC3).
pose proof SO as SO0. pose proof Hctx as HC. pose proof LG1 as LG0. pose proof HL3 as HL3'. pose proof bytes2 as (Bu & Bz & Bw).
pose proof parent_facts as (_&_&_&_&_&_&_&_& ST16 & _). pose proof lin as LIN.
destruct sep as (AG & RLO & RLEN & _ & _ & _ & RPM & GMR & _ & _ & RI & _ & _ & PRES & ERLO).
pose proof (upd_slot_fields am' i' (mkSlot (ss_hdr (nth_slot am' i')) None)) as (Fm & Fl & Fsc & Fml & Fst & Fex & Fss). fold (am_forget am' i') in Fm, Fl, Fsc, Fml, Fst, Fex, Fss.
pose proof (inv_groups HI1 g' am' Ug') as ((_ & _ & Glen & _) & _).
assert (U3 : usedX (g :: X) s3 g' (am_forget am' i')).
{ unfold s3. apply usedX_upd. left. split; [reflexivity|]. split; [exact (proj2 (usedX_MT _ _ _ _ Ug')) | reflexivity]. }
assert (NF3 : ss_fr (nth_slot (am_forget am' i') i') = None).
{ unfold am_forget. rewrite nth_slot_upd_slot by (rewrite ?Glen; lia). rewrite Z.eqb_refl. reflexivity. }
assert (EGM : GM = ly_reg L (prid (am_mem am')) + poff (slot_start am' i')).
{ unfold GM. rewrite Emem, <- (prid_slot_start am' i'). apply loc_addr_LMem. }
refine (memrepX_after B1 (g :: X) (g :: X) None (Some (g', i')) U1 U s1 s3 L mem1 mem2 NEWN [(GM, 8)] (SP0 - 96, 96) HI1 HI3 HL1 Efp Erg MR1 cells3 _ _ _ _ _ _ _).
- intros c Hc. right. destruct Hc as [<-|[]]. exact UC3.
- intros c Hc. destruct Hc as [<-|[]]. unfold usage_cell, cell_mem. cbn [mc_val mc_loc mc_w sval_num loc_addr]. rewrite HC. unfold CTX_usage. rewrite Z2Nat.id by (unfold sc in *; lia).
intros k Hk. replace (CTX + (464 + 8 * sc) + Z.of_nat k) with (CTX + 464 + 8 * sc + Z.of_nat k) by lia. exact (Bu k Hk).
- intros c k Hc _ [q Hq]. destruct Hc as [<-|[]]. discriminate Hq.
- intros d c Hd Hc. destruct Hd as [<-|[]].
pose proof (slot_body_free (g :: X) (Some (g', i')) U s3 L HI3 HL3' g' (am_forget am' i') i' (poff (slot_start am' i')) (poff (slot_start am' i') + 8)
U3 ltac:(rewrite Fl; lia) NF3 ltac:(rewrite Fss; lia) ltac:(rewrite Fss, Fst; unfold IB; unfold ST in ST16; lia) c Hc) as D.
rewrite Fm, <- EGM in D. replace (poff (slot_start am' i') + 8 - poff (slot_start am' i')) with 8 in D by lia. exact D.
- intros d a Hd Ha _. destruct Hd as [<-|[]]. unfold in_range in Ha. cbn [fst snd] in Ha.
replace a with (GM + (a - GM)) by lia. apply writable_off_img_present; [unfold GM, PM in *; lia | | apply Bw; lia].
unfold in_img1. unfold GM, PM in *. lia.
- intros e0 He. cbn [fst]. pose proof (footprint_hi (g :: X) None U1 L s1 md HI1 SO0 HC LG0 e0 He). lia.
- intros a Ha Hno HnoD _. pose proof (frameN a Ha) as F.
assert (NW : ~ in_winN a).
{ intros [W|W].
- apply (Hno (usage_cell (Z.to_nat sc) (usage_of A sc - (am_last am1 + 1)))); [left; reflexivity|].
unfold in_range, cell_range, usage_cell. cbn [fst snd mc_loc mc_w loc_addr]. rewrite HC. unfold CTX_usage. rewrite Z2Nat.id by (unfold sc in *; lia). lia.
- apply (HnoD (GM, 8)); [left; reflexivity|]. unfold in_range. cbn [fst snd]. lia. }
specialize (F NW). split; [exact (proj1 (same_byte_views mem1 mem2 a F))|]. intros [bb Hb]. exists bb. rewrite F. exact Hb.
Qed.
Lemma statics3 : statics_ok B1 mem2.
Proof.
pose proof ST1 as ST0. pose proof lin as LIN. destruct sep as (AG & RLO & RLEN & _ & _ & _ & RPM & GMR & _ & _ & RI & _).
apply (statics_ok_ext B1 mem1 mem2 ST0). intros x Hs.
assert (R : 0x10000 <= x < 0x51000 /\ ~ (CTX <= x < CTX + CTX_SIZE)).
{ unfold static_owned in Hs. cbn [ms_lock ms_libc ms_got_guard ms_guard ms_debruijn ms_size_classes ms_small_cnt ms_med_cnt B1 src0_msyms] in Hs.
unfold src0_D_malloc_lock, src0_D_libc, src0_D_got_stack_chk_guard, src0_D_stack_chk_guard, src0_D_debruijn32, src0_D_size_classes, src0_D_small_cnt_tab, src0_D_med_cnt_tab in Hs.
unfold CTX, src0_D_malloc_context, CTX_SIZE. lia. }
destruct R as [R1 R2]. refine (proj1 (same_byte_views mem1 mem2 x (frameN x ltac:(lia) _))).
intros [W|W]; [apply R2; unfold CTX_SIZE; unfold sc in *; lia | unfold GM, PM in *; lia].
Qed.
Theorem A3_post : ntcall fuel L A g regs regs2 mem mem2 gv /\ nt_pre B1 (g :: X) fuel L s3 regs2 mem2 md g' i'.
Proof.
pose proof NM as NM0. destruct NM0 as [Hso HLo Hcx Hsc0 Hrep Hst Hlg Hmd Ha0 Hs1 Hs2 Hsp Hkeep Hfr Hgd Hret Htp Hspf Hstkw Hunch].
pose proof sp_facts3 as (S16 & Sceil & S63 & WSTK). pose proof lin as LIN. pose proof s3_facts as (_ & Efp & Erg & _ & Ebk & _).
pose proof regs2_facts as (RK & R1 & R8 & R10 & R11 & R18 & R19). pose proof frameN as FN. pose proof win_ownedN as WO.
destruct sep as (AG & RLO & RLEN & _ & _ & _ & RPM & GMR & _ & _ & RI & _).
assert (OUT : forall a, 0 <= a < 2 ^ 64 -> alloc_ceiling <= a \/ ~ alloc_owned L s1 a -> mem2 (Z_to_bv 64 a) = mem1 (Z_to_bv 64 a)).
{ intros a Ha Ho. apply (FN a Ha). intros W. destruct Ho as [Ho|Ho]; [| exact (Ho (WO a W))].
destruct W as [W|W]; [unfold CTX, src0_D_malloc_context in W; unfold sc in *; lia | unfold GM, PM in *; lia]. }
assert (STK : forall a w v, SP0 - 96 <= a -> a + Z.of_nat w <= SP0 -> bytes_are mem1 a w v -> bytes_are mem2 a w v).
{ intros a w v Ha Haw Hb k Hk. rewrite <- (Hb k Hk). apply (proj1 (same_byte_views mem1 mem2 _ (OUT (a + Z.of_nat k) ltac:(unfold SP0 in *; lia) ltac:(left; unfold SP0 in *; lia)))). }
assert (ESP2 : spZ regs2 = SP0 - 96).
{ unfold spZ at 1. change (getr regs2 2) with (getr regs2 (nat_to_reg 2)). rewrite (RK 2%nat ltac:(cbn; tauto)), Hsp. apply lit64_small. unfold SP0 in *. lia. }
unfold NT_FRAME in *. fold SP0 in Hfr, Hstkw, Hunch, Hspf |- *.
split.
- split.
+ exact R1.
+ rewrite R19. exact Ha0.
+ rewrite (RK 9%nat ltac:(cbn; tauto)). exact Hs1.
+ exact R18.
+ rewrite (RK 2%nat ltac:(cbn; tauto)). exact Hsp.
+ intros rr Hr. rewrite (RK rr ltac:(apply in_app_iff; right; exact Hr)). apply Hkeep. exact Hr.
+ destruct Hfr as (F1 & F2 & F3 & F4 & F5 & F6). repeat split; (apply STK; [lia | cbn; lia | assumption]).
+ intros k Hk. rewrite <- (Hgd k Hk).
assert (NW : ~ in_winN (GUARD + Z.of_nat k)) by (intros [W|W]; [unfold GUARD, src0_D_stack_chk_guard, CTX, src0_D_malloc_context in *; lia | unfold GUARD, src0_D_stack_chk_guard, GM, PM in *; lia]).
exact (proj1 (same_byte_views mem1 mem2 _ (FN (GUARD + Z.of_nat k) ltac:(unfold GUARD, src0_D_stack_chk_guard; lia) NW))).
+ exact Hret.
+ exact Htp.
+ exact Hspf.
+ intros a Ha. unfold NT_FRAME in Ha. fold SP0 in Ha. apply (writable_same mem1 mem2 a (OUT a ltac:(lia) ltac:(left; lia))). apply Hstkw. exact Ha.
+ intros a Ha NO NS. unfold NT_FRAME in NS. fold SP0 in NS. rewrite (OUT a Ha (or_intror (fun W => NO (AO1 a W)))). exact (Hunch a Ha NO NS).
- unfold nt_pre. rewrite ESP2. unfold NT_FRAME.
split; [exact Hso|]. split; [apply HL3|]. split; [exact Hcx|]. split; [exact Hsc0|]. split; [apply memrep3|]. split; [apply statics3|].
split; [exact (ledger_ok_same' L s1 s3 md Hlg Erg Ebk)|]. split; [exact (proj1 Hmd)|]. split; [exact (proj1 (proj2 Hmd))|]. split; [exact (proj2 (proj2 Hmd))|].
split; [exact R10|]. split; [exact R11|]. split; [change (getr regs2 1) with (getr regs2 (nat_to_reg 1)); rewrite R1; apply ret_ok_XJ|].
split; [replace (SP0 - 96) with (SP0 + (-6) * 16) by lia; unfold SP0, spZ in *; rewrite Z_mod_plus_full; exact (proj1 Hspf)|].
split; [lia|]. split; [lia|].
split; [intros a Ha; apply (writable_same mem1 mem2 a (OUT a ltac:(lia) ltac:(left; lia))); apply Hstkw; lia|].
change (getr regs2 4) with (getr regs2 (nat_to_reg 4)). rewrite (RK 4%nat ltac:(cbn; tauto)). rewrite <- Htp. apply Hkeep. cbn. tauto.
Qed.
End h.
Theorem A3_SR :
SR src0segs (mkCfg (mkst regs1 (Z_to_bv 64 XU) mem1 (seg_rom src0segs)) md)
(fun c2 => exists regs2 mem2, c2 = mkCfg (mkst regs2 (Z_to_bv 64 src0_A_nontrivial_free) mem2 (seg_rom src0segs)) md /\
ntcall fuel L A g regs regs2 mem mem2 gv /\ nt_pre B1 (g :: X) fuel L s3 regs2 mem2 md g' i').
Proof.
pose proof (nm_md _ _ _ _ _ _ _ _ _ _ _ _ NM) as (Hh & Hlz & Hmat).
eapply SR_bind; [eapply (stage_run src0_A_nontrivial_free (ss_N m) (SSN m) (EV xvN) _ md (N_run_ok m) N_entry_st_ok Hh Hlz)|].
intros c' (ms2 & -> & HS2 & HF2). cbn [ms_mem mkst] in HF2.
apply SR_ret. exists (ms_regs ms2), (ms_mem ms2). split; [rewrite (shapeN ms2 HS2) at 1; reflexivity|].
exact (A3_post ms2 HS2 HF2).
Qed.
End e.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
