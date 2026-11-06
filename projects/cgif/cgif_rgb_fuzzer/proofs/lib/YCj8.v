(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Reals.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YK0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02 YQ07 YQ08 YC03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz YCd2.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfx YCe9.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM00 YM04 YM01 YM02 YM03 YM06 YP14 YI08 YI0c YI0g YI0d YI0f YI09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCji.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition LCU_HEAD : Z := 0x839d4.
Definition LCU_BR : Z := 0x83a14.
Definition LCU_EXIT : Z := 0x83a48.
Definition LCD_HEAD : Z := 0x83a64.
Definition LCD_BR : Z := 0x83a84.
Definition LCD_EXIT : Z := 0x83ab0.
Definition LCU_CLOB : list (bv 5) := [11; 13; 16; 17; 18; 24]%bv.
Definition LCU_KEEP : list (bv 5) := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 12; 14; 15; 19; 20; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LCU_KEEPA : list (bv 5) := [1; 2; 3; 4; 6; 7; 8; 9; 10; 12; 14; 15; 19; 20; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LCD_CLOB : list (bv 5) := [10; 11; 14; 20; 21]%bv.
Definition LCD_KEEP : list (bv 5) := [1; 2; 3; 4; 5; 6; 7; 8; 9; 12; 13; 15; 16; 17; 18; 19; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma lcu_clob_cases : forall r : bv 5, reg_in r LCU_CLOB = false -> r = 0%bv \/ In r LCU_KEEP.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]). destruct Hin.
Qed.
Lemma lcd_clob_cases : forall r : bv 5, reg_in r LCD_CLOB = false -> r = 0%bv \/ In r LCD_KEEP.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]). destruct Hin.
Qed.
Lemma lcu_keep_cases : forall r : bv 5, In r LCU_KEEP -> r = 5%bv \/ In r LCU_KEEPA.
Proof.
intros r Hr. cbv [LCU_KEEP In] in Hr.
repeat (destruct Hr as [<- | Hr]; [first [left; reflexivity | right; cbv; tauto] |]). destruct Hr.
Qed.
Lemma lcr_beq_bool_w : forall t : bool, branch_taken BC_EQ (if t then w1 else w0) (Z_to_bv 64 0) = negb t.
Proof. intros [|]; unfold branch_taken, bv_eqb, w1, w0; rewrite !unsigned_lit_small by lia; reflexivity. Qed.
Lemma lcr_beq_bool_w_neg : forall t : bool, branch_taken BC_EQ (if t then w0 else w1) (Z_to_bv 64 0) = t.
Proof. intros [|]; unfold branch_taken, bv_eqb, w1, w0; rewrite !unsigned_lit_small by lia; reflexivity. Qed.
Section d.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trbsegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trbsegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)) (k : Z).
Variables (lyc : alayout) (Sc : astate) (W : world trbsegs).
Variables (pb pm p : Z) (palc : list Z) (cut mean s m : Z).
Hypothesis HinP : In (pb, pm) (ablocks B lyc Sc). Hypothesis HP0 : pb <= p. Hypothesis HP1 : p + zlen palc <= pb + pm.
Hypothesis Hcut : 0 <= cut <= 2.
Hypothesis Hmean : 0 <= mean < 2 ^ 64. Hypothesis Hq : is_quot mean m s.
Definition lcr_base (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k /\
frm_zero (@fp_csr fy) /\
arr8 trbsegs (mrestrict (w_H W) mem) p palc /\
getr regs 26 = w64 p /\ getr regs 23 = w64 (2 ^ 64 - 1 - p) /\ getr regs 27 = w64 SB.
Lemma lcr_env : forall fy regs mem md, lcr_base fy regs mem md ->
4096 <= pb /\ pb + req_size pm <= alloc_ceiling /\ pm <= req_size pm /\ 140735332483072 <= alloc_ceiling <= 140737479966720.
Proof.
intros fy regs mem md (HJ & _). pose proof HJ as (HAR & _). pose proof asan_consts as (C1 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pb pm HAR HinP) as (_ & Hp4096 & Hpceil & _ & _ & _ & Hpm0).
pose proof (req_size_pos pm ltac:(lia)) as [_ Hrp]. repeat split; try assumption; lia.
Qed.
Lemma arr8_kept : forall (mem mem' : word -> option byte),
arr8 trbsegs (mrestrict (w_H W) mem) p palc ->
(forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) ->
4096 <= p -> p + zlen palc <= 140737479966720 ->
arr8 trbsegs (mrestrict (w_H W) mem') p palc.
Proof.
intros mem mem' Hpa Hk Hp0 Hp1. apply (arr8_frame trbsegs _ _ p palc Hpa). intros a Ha. apply (mbyte_of_aview trbsegs). apply Hk. lia.
Qed.
Local Ltac lcr_sr_get :=
lazymatch goal with |- sv_denot ?Ey (sr_get ?rg ?r) = _ => let v := eval vm_compute in (sr_get rg r) in change (sr_get rg r) with v end.
Section e.
Variables (nb nn ma v25 : Z).
Hypothesis HinN : In (nb, nn) (ablocks B lyc Sc). Hypothesis HN0 : nb <= ma. Hypothesis HN1 : ma + 8 <= nb + nn. Hypothesis HN8 : ma mod 8 = 0.
Hypothesis HPN : (pb, pm) <> (nb, nn).
Hypothesis H25 : 16 <= v25 < 2 ^ 64.
Definition lcu_base (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
lcr_base fy regs mem md /\
val_mem trbsegs (mrestrict (w_H W) mem) ma 8 mean /\
getr regs 10 = w64 ma /\ getr regs 12 = w64 cut /\ getr regs 14 = w64 (8 * cut) /\ getr regs 15 = w64 (cut + 3) /\
getr regs 25 = w64 v25 /\ getr regs 5 = w64 2.
Definition lcu_inv (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (x : Z) : Prop :=
lcu_base fy regs mem md /\ getr regs 11 = w64 (cut + 3 * x) /\ getr regs 13 = w64 (3 * x) /\ getr regs 18 = w64 x /\ getr regs 24 = w64 (3 * x).
Definition lcu_exit (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (x : Z) : Prop :=
lcu_base fy regs mem md /\ reg_get (@fp_regs fy) (15%bv : bv 5) = Z_to_bv 64 mean /\
getr regs 11 = w64 0 /\ getr regs 13 = w64 (3 * x) /\ getr regs 18 = w64 x /\ getr regs 24 = w64 (3 * x).
Lemma lcu_env : forall fy regs mem md, lcu_base fy regs mem md ->
4096 <= nb /\ nb + req_size nn <= alloc_ceiling /\ nn <= req_size nn /\ (pb + req_size pm <= nb \/ nb + req_size nn <= pb).
Proof.
intros fy regs mem md ((HJ & _) & _). pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ nb nn HAR HinN) as (_ & Hn4096 & Hnceil & _ & _ & _ & Hnn0).
pose proof (req_size_pos nn ltac:(lia)) as [_ Hrn].
pose proof (sep_blocks trbsegs _ LAWS lyc Sc _ _ _ pb pm nb nn HAR HinP HinN HPN) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
repeat split; try assumption; lia.
Qed.
Definition lcu_alias : sv := SAlu ALU_ADD (SOff 26 0) (SOff 11 0).
Definition lcu_mem : smem :=
[ YQ0b.mkRegion (Some 33%nat) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SOff 32 0))];
YQ0b.mkRegion (Some 10%nat) 0 8 0 0 [YQ0b.mkChunk 0 (CVal 8 (SOff 34 0))] ].
Definition lcu_regs := sr_set sr_atoms 5%bv (SLit 2).
Definition lcu_facts : facts :=
mkFacts [ (10%nat, mkAF 4096 140737479966720 3); (11%nat, mkAF 0 (3 * 2^29 + 2) 0); (12%nat, mkAF 0 2 0); (14%nat, mkAF 0 16 0); (15%nat, mkAF 3 5 0);
(18%nat, mkAF 0 (2^29) 0); (23%nat, mkAF (2^64 - 1 - 140737479966720) (2^64 - 1 - 4096) 0); (24%nat, mkAF 0 (3 * 2^29) 0);
(25%nat, mkAF 16 (2^64 - 1) 0); (26%nat, mkAF 4096 140737479966720 0); (27%nat, mkAF SB SB 0); (32%nat, mkAF 0 255 0);
(33%nat, mkAF 4096 140737479966720 0) ] [] [ (lcu_alias, SOff 33 0) ].
Definition ss_LCUx : sstate := mkSS LCU_HEAD lcu_regs lcu_mem None lcu_facts.
Definition lcr_Bx : sv := SOff 27 0.
Definition lcu_SH : list shent := [ mkSHE 33 0 1; mkSHE 10 0 8 ].
Definition lcr_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Lemma lcu_rs_ro : forall rr, In rr lcu_mem -> YQ0b.r_whi rr <= YQ0b.r_wlo rr.
Proof. intros rr [<- | [<- | []]]; cbn; lia. Qed.
Lemma LCU_seed : forall (fy : FPState) (regs : bvmap 5 word) mem md (x : Z),
0 <= x < 2 ^ 29 -> 3 * x + cut < zlen palc -> lcu_inv fy regs mem md x ->
let E0 := Ereg regs (map (Z_to_bv 64) [getz palc (3 * x + cut); p + 3 * x + cut; mean] ++ []) in
let E := ew_fregs E0 64 (@fp_regs fy) in
st_okF trbsegs E (mkSST LCU_HEAD lcu_regs (sfr_atoms 64) lcu_mem None lcu_facts)
(restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LCU_HEAD) mem (seg_rom trbsegs))) /\
sh_ok trbsegs lcr_Bx lcu_SH E (mrestrict (w_H W) mem) /\
(forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) /\
ew E 32 = Z_to_bv 64 (getz palc (3 * x + cut)) /\ ew E 34 = Z_to_bv 64 mean /\
bv_unsigned (ew E 15) = cut + 3 /\ bv_unsigned (ew E 18) = x /\ bv_unsigned (ew E 24) = 3 * x.
Proof.
intros fy regs mem md x Hx Hlen HI E0 E.
pose proof HI as (HU & G11 & G13 & G18 & G24).
pose proof HU as (HB & Vmean & G10 & G12 & G14 & G15 & G25 & G5).
pose proof (lcr_env fy regs mem md HB) as (Qpb0 & Qpb1 & Qpm & C1).
pose proof (lcu_env fy regs mem md HU) as (Qnb0 & Qnb1 & Qnn & Qsep).
pose proof HB as (HJ & Hfrm & Hpa & G26 & G23 & G27).
pose proof HJ as (HAR & _).
destruct (arr8_getz trbsegs _ p palc (3 * x + cut) Hpa ltac:(clear - Hx Hcut Hlen; lia)) as [Hbyte Hbr].
assert (HE0 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E0 n = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall i v, nth_error [getz palc (3 * x + cut); p + 3 * x + cut; mean] i = Some v -> ew E0 (32 + i) = Z_to_bv 64 v) by (intros i v Hi; subst E0; apply Ereg_vals; exact Hi).
assert (HEE : forall n, (n < 64)%nat -> ew E n = ew E0 n) by (intros n Hn; subst E; apply ew_fregs_low; exact Hn).
assert (HE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5. rewrite HEE by lia. apply HE0. exact Hn. }
assert (Rp : 4096 <= p /\ p + zlen palc <= 140737479966720) by (clear - HP0 HP1 Qpb0 Qpb1 Qpm C1; lia).
assert (Rm : 4096 <= ma /\ ma + 8 <= 140737479966720) by (clear - HN0 HN1 Qnb0 Qnb1 Qnn C1; lia).
assert (U10 : bv_unsigned (ew E0 10) = ma) by (rewrite (HE0 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; clear - Rm; lia).
assert (U11 : bv_unsigned (ew E0 11) = cut + 3 * x) by (rewrite (HE0 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; clear - Hx Hcut; lia).
assert (U12 : bv_unsigned (ew E0 12) = cut) by (rewrite (HE0 12%nat 12%bv eq_refl), G12; apply unsigned_lit_small; clear - Hcut; lia).
assert (U14 : bv_unsigned (ew E0 14) = 8 * cut) by (rewrite (HE0 14%nat 14%bv eq_refl), G14; apply unsigned_lit_small; clear - Hcut; lia).
assert (U15 : bv_unsigned (ew E0 15) = cut + 3) by (rewrite (HE0 15%nat 15%bv eq_refl), G15; apply unsigned_lit_small; clear - Hcut; lia).
assert (U18 : bv_unsigned (ew E0 18) = x) by (rewrite (HE0 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; clear - Hx; lia).
assert (U23 : bv_unsigned (ew E0 23) = 2 ^ 64 - 1 - p) by (rewrite (HE0 23%nat 23%bv eq_refl), G23; apply unsigned_lit_small; clear - Rp Hx Hcut Hlen; lia).
assert (U24 : bv_unsigned (ew E0 24) = 3 * x) by (rewrite (HE0 24%nat 24%bv eq_refl), G24; apply unsigned_lit_small; clear - Hx; lia).
assert (U25 : bv_unsigned (ew E0 25) = v25) by (rewrite (HE0 25%nat 25%bv eq_refl), G25; apply unsigned_lit_small; clear - H25; lia).
assert (U26 : bv_unsigned (ew E0 26) = p) by (rewrite (HE0 26%nat 26%bv eq_refl), G26; apply unsigned_lit_small; clear - Rp Hx Hcut Hlen; lia).
assert (E27 : ew E0 27 = w64 SB) by (rewrite (HE0 27%nat 27%bv eq_refl); exact G27).
assert (E32 : ew E0 32 = Z_to_bv 64 (getz palc (3 * x + cut))) by (pose proof (HV 0%nat _ eq_refl) as X; cbn [Nat.add] in X; exact X).
assert (A32 : bv_unsigned (ew E0 32) = getz palc (3 * x + cut)) by (rewrite E32; apply unsigned_lit_small; clear - Hbr; lia).
assert (A33 : bv_unsigned (ew E0 33) = p + 3 * x + cut).
{ pose proof (HV 1%nat _ eq_refl) as X. cbn [Nat.add] in X. rewrite X. apply unsigned_lit_small. clear - Rp Hx Hcut Hlen. lia. }
assert (E34 : ew E0 34 = Z_to_bv 64 mean) by (pose proof (HV 2%nat _ eq_refl) as X; cbn [Nat.add] in X; exact X).
assert (A34 : bv_unsigned (ew E0 34) = mean) by (rewrite E34; apply unsigned_lit_small; clear - Hmean; lia).
assert (DN : forall n v, bv_unsigned (ew E0 n) = v -> sv_denot E0 (SOff n 0) = Z_to_bv 64 v).
{ intros n v Hn. cbn [sv_denot]. rewrite Hn, Z.add_0_r. reflexivity. }
assert (HS0 : @st_ok trbsegs fy E0 ss_LCUx (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LCU_HEAD) mem (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LCUx, lcu_regs. apply (entry_st_ok_full trbsegs).
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X |]. rewrite G5. cbn [sv_denot]. reflexivity.
- vm_compute. reflexivity.
- unfold lcu_mem. repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
change (Ereg regs _) with E0. rewrite A33.
split; [clear - Rp Hx Hcut; lia|]. split; [clear - Rp Hx Hcut Hlen; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trbsegs E0 _ (p + 3 * x + cut) 0 1 _ (getz palc (3 * x + cut))); [exact (DN _ _ A32) | zside | zside |].
apply (val_mem_byte trbsegs); [rewrite Z.add_0_r; replace (p + 3 * x + cut) with (p + (3 * x + cut)) by lia; exact Hbyte | exact Hbr].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
change (Ereg regs _) with E0. rewrite U10.
split; [clear - Rm; lia|]. split; [clear - Rm; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trbsegs E0 _ ma 0 8 _ mean); [exact (DN _ _ A34) | zside | zside | rewrite Z.add_0_r; exact Vmean].
- apply pairwise_disjoint_of_extents. unfold lcu_mem, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. change (Ereg regs _) with E0. rewrite A33, U10.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
clear - Hx Hcut Hlen HP0 HP1 HN0 HN1 Qpm Qnn Qsep. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [lcu_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (Ereg regs _) with E0.
rewrite U10, U11, U12, U14, U15, U18, U23, U24, U25, U26, E27, A32, A33. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - Hx Hcut Hlen Rp Rm HN8 H25 Hbr. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
+ cbn [lcu_facts f_alias alias_ok]. change (Ereg regs _) with E0. split; [|exact I].
unfold lcu_alias. apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U11, U26, A33, !Z.add_0_r.
rewrite (zcanon_id (cut + 3 * x)), (zcanon_id p) by (unfold M64; clear - Rp Hx Hcut Hlen; lia).
f_equal. lia. }
assert (SHOK0 : sh_ok trbsegs lcr_Bx lcu_SH E0 (mrestrict (w_H W) mem)).
{ unfold sh_ok, lcu_SH. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range trbsegs (w_H W) mem E0 lcr_Bx 33 (p + 3 * x + cut) 1 (p + 3 * x + cut) 0 1).
+ apply (range_addressable_of_block trbsegs B LAWS lyc Sc W mem md pb pm _ _ HAR HinP); clear - Hx Hcut Hlen HP0 HP1 Qpm; lia.
+ unfold U, lcr_Bx. cbn [sv_denot]. rewrite E27, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A33.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ pb pm HAR HinP) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ pb pm HAR HinP) as Himg.
revert Hy Hia Himg Hx Hcut Hlen HP0 HP1 Qpm Qpb0 Qpb1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia.
- apply (shent_ok_of_range trbsegs (w_H W) mem E0 lcr_Bx 10 ma 8 ma 0 8).
+ apply (range_addressable_of_block trbsegs B LAWS lyc Sc W mem md nb nn _ _ HAR HinN); clear - HN0 HN1 Qnn; lia.
+ unfold U, lcr_Bx. cbn [sv_denot]. rewrite E27, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U10.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ nb nn HAR HinN) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ nb nn HAR HinN) as Himg.
revert Hy Hia Himg HN0 HN1 Qnn Qnb0 Qnb1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia. }
split; [exact (st_ok_enterF trbsegs fy 64 E0 ss_LCUx _ HS0 ltac:(vm_compute; reflexivity) Hfrm)|].
split; [exact (sh_ok_agree trbsegs lcr_Bx lcu_SH 64 E0 E _ (env_agree_ew_fregs E0 64 _) ltac:(vm_compute; reflexivity) SHOK0)|].
split; [exact HE|].
split; [rewrite HEE by lia; exact E32|].
split; [rewrite HEE by lia; exact E34|].
rewrite !HEE by lia. repeat split; assumption.
Qed.
Definition lcu_cond : sv := SF2 (FP2_cmp F_LE FMT_D) (SF1 (FP1_cvt FC_D FC_WU RNE) (SOff 32 0)) (SOff 34 0).
Lemma LCU_step : forall (fy : FPState) (regs : bvmap 5 word) mem md (x : Z),
0 <= x < 2 ^ 29 -> 3 * x + cut < zlen palc -> lcu_inv fy regs mem md x ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LCU_HEAD) mem (seg_rom trbsegs)) md)
(fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 (if ptest palc cut s m x then LCU_HEAD else LCU_EXIT)) mem' (seg_rom trbsegs)) md' /\
(if ptest palc cut s m x then lcu_inv fy' regs' mem' md' (x + 1) else lcu_exit fy' regs' mem' md' x) /\
(forall r : bv 5, In r LCU_KEEP -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros fy regs mem md x Hx Hlen HI.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof HI as (HU & G11 & G13 & G18 & G24).
pose proof HU as (HB & Vmean & G10 & G12 & G14 & G15 & G25 & G5).
pose proof (lcr_env fy regs mem md HB) as (Qpb0 & Qpb1 & Qpm & C1).
pose proof (lcu_env fy regs mem md HU) as (Qnb0 & Qnb1 & Qnn & Qsep).
pose proof HB as (HJ & Hfrm & Hpa & G26 & G23 & G27).
assert (Rp : 4096 <= p /\ p + zlen palc <= 140737479966720) by (clear - HP0 HP1 Qpb0 Qpb1 Qpm C1; lia).
assert (Rm : 4096 <= ma /\ ma + 8 <= 140737479966720) by (clear - HN0 HN1 Qnb0 Qnb1 Qnn C1; lia).
destruct (arr8_getz trbsegs _ p palc (3 * x + cut) Hpa ltac:(clear - Hx Hcut Hlen; lia)) as [_ Hbr].
destruct (LCU_seed fy regs mem md x Hx Hlen HI) as (HS & SHOK & HE & HE32 & HE34 & HU15 & HU18 & HU24).
set (E := ew_fregs _ 64 _) in HS, SHOK, HE, HE32, HE34, HU15, HU18, HU24.
aj_run_to_tokF trbtbl_lib_ok HS HJ SHOK lcr_Bspan LCU_BR.
{ cbn [ss_mem]. unfold lcu_mem. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr1; rename HG into HG1; clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msA := msx) in * end.
assert (KW1 : forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) (ms_mem msA) a = aview trbsegs (w_H W) mem a).
{ exact (lg_kept_ro _ _ _ _ _ HFr1 lcu_rs_ro). }
assert (FIN : forall (fz : FPState) E' ss' ms' md' pc' (v11 v13 v18 v24 : Z), @st_ok trbsegs fz E' ss' (restrict (w_H W) ms') -> env_agree 96 E E' ->
ss_pc ss' = pc' -> ss_resv ss' = None ->
sv_denot E' (sr_get (ss_regs ss') 11) = w64 v11 -> sv_denot E' (sr_get (ss_regs ss') 13) = w64 v13 ->
sv_denot E' (sr_get (ss_regs ss') 18) = w64 v18 -> sv_denot E' (sr_get (ss_regs ss') 24) = w64 v24 ->
sr_get (ss_regs ss') 5 = SLit 2 ->
forallb (fun rr : bv 5 => sv_eqb (sr_get (ss_regs ss') rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) LCU_KEEPA = true ->
frm_zero (@fp_csr fz) -> reg_get (@fp_regs fz) (15%bv : bv 5) = Z_to_bv 64 mean ->
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') md' k ->
(forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) (ms_mem ms') a = aview trbsegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms') a) ->
SRr trbsegs W (mkCfg ms' md')
(fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md'',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 pc') mem' (seg_rom trbsegs)) md'' /\
lcu_base fy' regs' mem' md'' /\ reg_get (@fp_regs fy') (15%bv : bv 5) = Z_to_bv 64 mean /\
getr regs' 11 = w64 v11 /\ getr regs' 13 = w64 v13 /\ getr regs' 18 = w64 v18 /\ getr regs' 24 = w64 v24 /\
(forall r : bv 5, In r LCU_KEEP -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a))).
{ intros fz E' ss' ms' md' pc' v11 v13 v18 v24 HS' [EA ED] Hpc' Hrv' D11 D13 D18 D24 Q5 QK Hfz Hfz5 HJ' Hk' Hp'.
assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) [getz palc (3 * x + cut); p + 3 * x + cut; mean] ++ [])) E').
{ split; [intros n Hn; rewrite EA by lia; subst E; rewrite ew_fregs_low by lia; reflexivity | rewrite ED; reflexivity]. }
pose proof (regs_kept_of_st_ok trbsegs E' ss' _ regs _ LCU_KEEPA HS' HAE' QK) as HKR. cbn [ms_regs restrict] in HKR.
assert (HKR' : forall r : bv 5, In r LCU_KEEP -> getr (ms_regs ms') r = getr regs r).
{ intros r Hr. destruct (lcu_keep_cases r Hr) as [-> | Hin]; [ | exact (HKR r Hin)].
rewrite (st_ok_restrict_reg trbsegs (w_H W) E' ss' ms' (5%bv : bv 5) HS'), Q5, G5. reflexivity. }
rewrite (st_ok_restrict_mkst trbsegs (w_H W) E' ss' ms' HS' Hrv'), Hpc'. apply SRr_ret.
split; [reflexivity|]. exists fz, (ms_regs ms'), (ms_mem ms'), md'. split; [reflexivity|].
split.
{ split.
{ split; [exact HJ'|]. split; [exact Hfz|].
split; [exact (arr8_kept mem (ms_mem ms') Hpa Hk' (proj1 Rp) (proj2 Rp))|].
split; [rewrite (HKR' (26%bv : bv 5) ltac:(cbv; tauto)); exact G26|].
split; [rewrite (HKR' (23%bv : bv 5) ltac:(cbv; tauto)); exact G23|].
rewrite (HKR' (27%bv : bv 5) ltac:(cbv; tauto)). exact G27. }
split; [apply (YCcz.val_mem_kept trbsegs (w_H W) (w_H W) mem (ms_mem ms') ma 8 mean); [intros kk Hkk; apply Hk'; clear - Hkk Rm; lia | exact Vmean]|].
split; [rewrite (HKR' (10%bv : bv 5) ltac:(cbv; tauto)); exact G10|].
split; [rewrite (HKR' (12%bv : bv 5) ltac:(cbv; tauto)); exact G12|].
split; [rewrite (HKR' (14%bv : bv 5) ltac:(cbv; tauto)); exact G14|].
split; [rewrite (HKR' (15%bv : bv 5) ltac:(cbv; tauto)); exact G15|].
split; [rewrite (HKR' (25%bv : bv 5) ltac:(cbv; tauto)); exact G25|].
rewrite (HKR' (5%bv : bv 5) ltac:(cbv; tauto)). exact G5. }
split; [exact Hfz5|].
split; [rewrite (st_ok_restrict_reg trbsegs (w_H W) E' ss' ms' (11%bv : bv 5) HS'); exact D11|].
split; [rewrite (st_ok_restrict_reg trbsegs (w_H W) E' ss' ms' (13%bv : bv 5) HS'); exact D13|].
split; [rewrite (st_ok_restrict_reg trbsegs (w_H W) E' ss' ms' (18%bv : bv 5) HS'); exact D18|].
split; [rewrite (st_ok_restrict_reg trbsegs (w_H W) E' ss' ms' (24%bv : bv 5) HS'); exact D24|].
split; [exact HKR'|]. split; [exact Hk' | exact Hp']. }
assert (HAE96 : env_agree 96 E E) by (apply env_agree_refl).
lg_branchF trbtbl_lib_ok HS.
-
lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
assert (Ht : ptest palc cut s m x = false).
{ cbn [sv_denot] in Hc. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned, !(proj1 HAEx) in Hc by lia.
rewrite (lg_fle_cvt_test RNE _ _ (getz palc (3 * x + cut)) mean s m HE32 HE34 Hbr Hmean Hq) in Hc.
rewrite lcr_beq_bool_w in Hc. apply Bool.negb_true_iff in Hc. exact Hc. }
rewrite Ht.
pose proof (st_okF_frm trbsegs _ _ _ HS) as Hfrm'. pose proof (st_okF_freg trbsegs _ _ _ (15%bv : bv 5) HS) as Hf5'.
lazymatch type of Hf5' with _ = sv_denot ?Ex (sfr_get ?fr ?r) => let v := eval vm_compute in (sfr_get fr r) in change (sfr_get fr r) with v in Hf5' end.
cbn [sv_denot] in Hf5'. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (proj1 HAEx), HE34 in Hf5' by lia.
pose proof (st_okF_to_legacy trbsegs _ _ _ HS) as HSL. clear HS.
aj_run_to_tok trbtbl_lib_ok HSL HJ SHOK lcr_Bspan LCU_EXIT.
{ apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HSL with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 96 E Ey) by (env_agree_chain HAEx) end.
eapply SRr_mono.
{ apply (FIN _ _ _ _ _ LCU_EXIT 0 (3 * x) x (3 * x) HSL HAEy); [reflexivity | reflexivity | | | | | reflexivity | vm_compute; reflexivity | exact Hfrm' | exact Hf5' | exact HJ | | ].
+ lcr_sr_get. cbn [sv_denot]. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned, !(proj1 HAEy) by lia.
rewrite (lg_fle_cvt_test RNE _ _ (getz palc (3 * x + cut)) mean s m HE32 HE34 Hbr Hmean Hq). change (ptest palc cut s m x) with (getz palc (3 * x + cut) * s <=? m) in Ht. rewrite Ht. reflexivity.
+ lcr_sr_get. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (proj1 HAEy), (HE 13%nat 13%bv eq_refl) by lia. exact G13.
+ lcr_sr_get. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (proj1 HAEy), (HE 18%nat 18%bv eq_refl) by lia. exact G18.
+ lcr_sr_get. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (proj1 HAEy), (HE 24%nat 24%bv eq_refl) by lia. exact G24.
+ intros a Ha. rewrite (lg_kept_ro _ _ _ _ _ HFr lcu_rs_ro a Ha). exact (KW1 a Ha).
+ intros a Ha. apply (apresent_grows _ _ _ _ HG). apply (apresent_grows _ _ _ _ HG1). exact Ha. }
cbv beta. intros W' c' _ (HW' & fy' & regs' & mem' & md' & Hc' & HB' & Hf5n & R11 & R13 & R18 & R24 & HK' & Hk' & Hp').
split; [exact HW'|]. exists fy', regs', mem', md'. split; [exact Hc'|].
split; [split; [exact HB'|]; split; [exact Hf5n|]; split; [exact R11|]; split; [exact R13|]; split; [exact R18 | exact R24]|].
split; [exact HK'|]. split; [exact Hk' | exact Hp'].
-
lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
assert (Ht : ptest palc cut s m x = true).
{ cbn [sv_denot] in Hc. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned, !(proj1 HAEx) in Hc by lia.
rewrite (lg_fle_cvt_test RNE _ _ (getz palc (3 * x + cut)) mean s m HE32 HE34 Hbr Hmean Hq) in Hc.
rewrite lcr_beq_bool_w in Hc. apply Bool.negb_false_iff in Hc. exact Hc. }
rewrite Ht.
pose proof (st_okF_frm trbsegs _ _ _ HS) as Hfrm'. pose proof (st_okF_freg trbsegs _ _ _ (15%bv : bv 5) HS) as Hf5'.
lazymatch type of Hf5' with _ = sv_denot ?Ex (sfr_get ?fr ?r) => let v := eval vm_compute in (sfr_get fr r) in change (sfr_get fr r) with v in Hf5' end.
cbn [sv_denot] in Hf5'. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (proj1 HAEx), HE34 in Hf5' by lia.
pose proof (st_okF_to_legacy trbsegs _ _ _ HS) as HSL. clear HS.
aj_run_to_tok trbtbl_lib_ok HSL HJ SHOK lcr_Bspan LCU_HEAD.
{ apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HSL with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 96 E Ey) by (env_agree_chain HAEx) end.
eapply SRr_mono.
{ apply (FIN _ _ _ _ _ LCU_HEAD (cut + 3 * (x + 1)) (3 * (x + 1)) (x + 1) (3 * (x + 1)) HSL HAEy); [reflexivity | reflexivity | | | | | reflexivity | vm_compute; reflexivity | exact Hfrm' | exact Hf5' | exact HJ | | ].
+ lcr_sr_get. unfold w64. apply lg_denot_of_U. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, !(proj1 HAEy), HU15, HU24, !Z.add_0_r by lia.
rewrite (zcanon_id (cut + 3)), (zcanon_id (3 * x)) by (unfold M64; clear - Hx Hcut; lia). rewrite zcanon_id by (unfold M64; clear - Hx Hcut; lia). lia.
+ lcr_sr_get. unfold w64. apply lg_denot_of_U. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite !U_SOff, !U_SLit, !(proj1 HAEy), HU18, !Z.add_0_r by lia.
rewrite (zcanon_id x), (zcanon_id 3) by (unfold M64; clear - Hx; lia). rewrite (zcanon_id (x * 3)) by (unfold M64; clear - Hx; lia).
rewrite zcanon_id by (unfold M64; clear - Hx; lia). lia.
+ lcr_sr_get. cbn [sv_denot]. rewrite (proj1 HAEy), HU18 by lia. reflexivity.
+ lcr_sr_get. cbn [sv_denot]. rewrite (proj1 HAEy), HU24 by lia. unfold w64. f_equal. lia.
+ intros a Ha. rewrite (lg_kept_ro _ _ _ _ _ HFr lcu_rs_ro a Ha). exact (KW1 a Ha).
+ intros a Ha. apply (apresent_grows _ _ _ _ HG). apply (apresent_grows _ _ _ _ HG1). exact Ha. }
cbv beta. intros W' c' _ (HW' & fy' & regs' & mem' & md' & Hc' & HB' & Hf5n & R11 & R13 & R18 & R24 & HK' & Hk' & Hp').
split; [exact HW'|]. exists fy', regs', mem', md'. split; [exact Hc'|].
split; [split; [exact HB'|]; split; [exact R11|]; split; [exact R13|]; split; [exact R18 | exact R24]|].
split; [exact HK'|]. split; [exact Hk' | exact Hp'].
Qed.
Definition LCU_post (regs : bvmap 5 word) (mem : word -> option byte) (i1 : Z) : world trbsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 LCU_EXIT) mem' (seg_rom trbsegs)) md' /\
lcu_exit fy' regs' mem' md' i1 /\
(forall r : bv 5, In r LCU_KEEP -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Lemma LCU_last : forall (fy : FPState) (regs : bvmap 5 word) mem md (i1 : Z),
0 <= i1 < 2 ^ 29 -> 3 * i1 + cut < zlen palc -> ptest palc cut s m i1 = false -> lcu_inv fy regs mem md i1 ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LCU_HEAD) mem (seg_rom trbsegs)) md) (LCU_post regs mem i1).
Proof.
intros fy regs mem md i1 Hi1 Hlen Hbig HI.
eapply SRr_mono; [exact (LCU_step fy regs mem md i1 Hi1 Hlen HI)|].
cbv beta. rewrite Hbig. intros W' c' _ H. exact H.
Qed.
Lemma LCU_loop : forall (n : nat) (fy : FPState) (regs : bvmap 5 word) mem md (x i1 : Z),
i1 - x <= Z.of_nat n -> 0 <= x <= i1 -> i1 < 2 ^ 29 -> 3 * i1 + cut < zlen palc ->
(forall z, x <= z < i1 -> ptest palc cut s m z = true) -> ptest palc cut s m i1 = false ->
lcu_inv fy regs mem md x ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LCU_HEAD) mem (seg_rom trbsegs)) md) (LCU_post regs mem i1).
Proof.
induction n as [|n IH]; intros fy regs mem md x i1 Hn Hx Hi1 Hlen Hsm Hbig HI.
- assert (x = i1) by lia. subst x. exact (LCU_last fy regs mem md i1 ltac:(lia) Hlen Hbig HI).
- destruct (Z.eq_dec x i1) as [-> | Hne]; [exact (LCU_last fy regs mem md i1 ltac:(lia) Hlen Hbig HI)|].
eapply SRr_bind; [exact (LCU_step fy regs mem md x ltac:(lia) ltac:(lia) HI)|].
cbv beta. rewrite (Hsm x ltac:(lia)). intros W' c' _ (-> & fy' & regs' & mem' & md' & -> & HI' & Hk' & Hm' & Hp').
eapply SRr_mono; [exact (IH fy' regs' mem' md' (x + 1) i1 ltac:(lia) ltac:(lia) Hi1 Hlen ltac:(intros z Hz; apply Hsm; lia) Hbig HI')|].
cbv beta. intros W'' c'' _ (HW & fy'' & regs'' & mem'' & md'' & Hc & HX'' & Hk'' & Hm'' & Hp'').
split; [exact HW|]. exists fy'', regs'', mem'', md''. split; [exact Hc|]. split; [exact HX''|].
split; [intros r Hr; rewrite (Hk'' r Hr); apply Hk'; exact Hr|].
split; [intros a Ha; rewrite (Hm'' a Ha); apply Hm'; exact Ha|].
intros a Ha. apply Hp''. apply Hp'. exact Ha.
Qed.
End e.
Definition lcd_inv (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (y : Z) : Prop :=
lcr_base fy regs mem md /\ reg_get (@fp_regs fy) (15%bv : bv 5) = Z_to_bv 64 mean /\
getr regs 12 = Z_to_bv 64 (cut - 3) /\ getr regs 10 = w64 (cut + 3 * y) /\ getr regs 20 = w64 (3 * y) /\ getr regs 21 = w64 y.
Definition lcd_exit (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (y : Z) : Prop :=
lcr_base fy regs mem md /\ reg_get (@fp_regs fy) (15%bv : bv 5) = Z_to_bv 64 mean /\
getr regs 12 = Z_to_bv 64 (cut - 3) /\ getr regs 10 = w64 0 /\ getr regs 20 = w64 (3 * y) /\ getr regs 21 = w64 y.
Definition lcd_off : sv := SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff 12 0) (SLit 32)) (SAlu ALU_SLL (SOff 20 0) (SLit 32))) (SLit 32).
Definition lcd_alias : sv := SAlu ALU_ADD (SOff 26 0) (SOff 10 0).
Definition lcd_mem : smem := [ YQ0b.mkRegion (Some 33%nat) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SOff 32 0))] ].
Definition lcd_facts : facts :=
mkFacts [ (10%nat, mkAF 0 (3 * 2^29 + 2) 0); (12%nat, mkAF (2^64 - 3) (2^64 - 1) 0); (20%nat, mkAF 0 (3 * 2^29) 0); (21%nat, mkAF 0 (2^29) 0);
(23%nat, mkAF (2^64 - 1 - 140737479966720) (2^64 - 1 - 4096) 0); (26%nat, mkAF 4096 140737479966720 0); (27%nat, mkAF SB SB 0);
(32%nat, mkAF 0 255 0); (33%nat, mkAF 4096 140737479966720 0) ]
[ mkAC BC_GEU (SOff 23 0) lcd_off ] [ (lcd_alias, SOff 33 0) ].
Definition ss_LCDx : sstate := mkSS LCD_HEAD sr_atoms lcd_mem None lcd_facts.
Definition lcd_SH : list shent := [ mkSHE 33 0 1 ].
Definition lcd_cond : sv := SF2 (FP2_cmp F_LT FMT_D) (SOff 79 0) (SF1 (FP1_cvt FC_D FC_WU RNE) (SOff 32 0)).
Lemma lcd_rs_ro : forall rr, In rr lcd_mem -> YQ0b.r_whi rr <= YQ0b.r_wlo rr.
Proof. intros rr [<- | []]. cbn. lia. Qed.
Lemma lcd_U_srl32_lt : forall E v, U E (SAlu ALU_SRL v (SLit 32)) < 2 ^ 32.
Proof.
intros E v. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (Z.land (zcanon 32) 63) with 32. rewrite Z.shiftr_div_pow2 by lia.
pose proof (U_range E v) as Hr. unfold M64 in Hr.
assert (Hd : 0 <= U E v / 2 ^ 32 < 2 ^ 32) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma lcd_U_off : forall E a b c y, U E a = 2 ^ 64 + c - 3 -> U E b = 3 * y -> 0 <= c <= 2 -> 1 <= y < 2 ^ 29 ->
U E (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL a (SLit 32)) (SAlu ALU_SLL b (SLit 32))) (SLit 32)) = c + 3 * (y - 1).
Proof.
intros E a b c y Ha Hb Hc Hy. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SAlu. cbn [zalu_raw]. rewrite Ha, Hb, !U_SLit.
change (Z.land (zcanon 32) 63) with 32. rewrite !Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
unfold zcanon, M64. change (2 ^ 64) with 18446744073709551616. change (2 ^ 32) with 4294967296.
assert (E1 : ((18446744073709551616 + c - 3) * 4294967296) mod 18446744073709551616 = (4294967296 + c - 3) * 4294967296).
{ replace ((18446744073709551616 + c - 3) * 4294967296) with ((4294967296 + c - 3) * 4294967296 + 4294967295 * 18446744073709551616) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
assert (E2 : (3 * y * 4294967296) mod 18446744073709551616 = 3 * y * 4294967296) by (apply Z.mod_small; lia).
rewrite E1, E2.
assert (E3 : ((4294967296 + c - 3) * 4294967296 + 3 * y * 4294967296) mod 18446744073709551616 = (c + 3 * (y - 1)) * 4294967296).
{ replace ((4294967296 + c - 3) * 4294967296 + 3 * y * 4294967296) with ((c + 3 * (y - 1)) * 4294967296 + 1 * 18446744073709551616) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
rewrite E3, Z.div_mul by lia. apply Z.mod_small. lia.
Qed.
Lemma LCD_seed : forall (fy : FPState) (regs : bvmap 5 word) mem md (y : Z),
0 <= y < 2 ^ 29 -> 3 * y + cut < zlen palc -> lcd_inv fy regs mem md y ->
let E0 := Ereg regs (map (Z_to_bv 64) [getz palc (3 * y + cut); p + 3 * y + cut] ++ []) in
let E := ew_fregs E0 64 (@fp_regs fy) in
st_okF trbsegs E (mkSST LCD_HEAD sr_atoms (sfr_atoms 64) lcd_mem None lcd_facts)
(restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LCD_HEAD) mem (seg_rom trbsegs))) /\
sh_ok trbsegs lcr_Bx lcd_SH E (mrestrict (w_H W) mem) /\
(forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) /\
ew E 32 = Z_to_bv 64 (getz palc (3 * y + cut)) /\ ew E 79 = Z_to_bv 64 mean /\
bv_unsigned (ew E 12) = 2 ^ 64 + cut - 3 /\ bv_unsigned (ew E 20) = 3 * y /\ bv_unsigned (ew E 21) = y.
Proof.
intros fy regs mem md y Hy Hlen HI E0 E.
pose proof HI as (HB & Hfa5 & G12 & G10 & G20 & G21).
pose proof (lcr_env fy regs mem md HB) as (Qpb0 & Qpb1 & Qpm & C1).
pose proof HB as (HJ & Hfrm & Hpa & G26 & G23 & G27).
pose proof HJ as (HAR & _).
destruct (arr8_getz trbsegs _ p palc (3 * y + cut) Hpa ltac:(clear - Hy Hcut Hlen; lia)) as [Hbyte Hbr].
assert (HE0 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E0 n = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall i v, nth_error [getz palc (3 * y + cut); p + 3 * y + cut] i = Some v -> ew E0 (32 + i) = Z_to_bv 64 v) by (intros i v Hi; subst E0; apply Ereg_vals; exact Hi).
assert (HEE : forall n, (n < 64)%nat -> ew E n = ew E0 n) by (intros n Hn; subst E; apply ew_fregs_low; exact Hn).
assert (HE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5. rewrite HEE by lia. apply HE0. exact Hn. }
assert (Rp : 4096 <= p /\ p + zlen palc <= 140737479966720) by (clear - HP0 HP1 Qpb0 Qpb1 Qpm C1; lia).
assert (U10 : bv_unsigned (ew E0 10) = cut + 3 * y) by (rewrite (HE0 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; clear - Hy Hcut; lia).
assert (U12 : bv_unsigned (ew E0 12) = 2 ^ 64 + cut - 3).
{ rewrite (HE0 12%nat 12%bv eq_refl), G12, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
replace (cut - 3) with (2 ^ 64 + cut - 3 + (-1) * 2 ^ 64) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. clear - Hcut. lia. }
assert (U20 : bv_unsigned (ew E0 20) = 3 * y) by (rewrite (HE0 20%nat 20%bv eq_refl), G20; apply unsigned_lit_small; clear - Hy; lia).
assert (U21 : bv_unsigned (ew E0 21) = y) by (rewrite (HE0 21%nat 21%bv eq_refl), G21; apply unsigned_lit_small; clear - Hy; lia).
assert (U23 : bv_unsigned (ew E0 23) = 2 ^ 64 - 1 - p) by (rewrite (HE0 23%nat 23%bv eq_refl), G23; apply unsigned_lit_small; clear - Rp Hy Hcut Hlen; lia).
assert (U26 : bv_unsigned (ew E0 26) = p) by (rewrite (HE0 26%nat 26%bv eq_refl), G26; apply unsigned_lit_small; clear - Rp Hy Hcut Hlen; lia).
assert (E27 : ew E0 27 = w64 SB) by (rewrite (HE0 27%nat 27%bv eq_refl); exact G27).
assert (E32 : ew E0 32 = Z_to_bv 64 (getz palc (3 * y + cut))) by (pose proof (HV 0%nat _ eq_refl) as X; cbn [Nat.add] in X; exact X).
assert (A32 : bv_unsigned (ew E0 32) = getz palc (3 * y + cut)) by (rewrite E32; apply unsigned_lit_small; clear - Hbr; lia).
assert (A33 : bv_unsigned (ew E0 33) = p + 3 * y + cut).
{ pose proof (HV 1%nat _ eq_refl) as X. cbn [Nat.add] in X. rewrite X. apply unsigned_lit_small. clear - Rp Hy Hcut Hlen. lia. }
assert (DN : forall n v, bv_unsigned (ew E0 n) = v -> sv_denot E0 (SOff n 0) = Z_to_bv 64 v).
{ intros n v Hn. cbn [sv_denot]. rewrite Hn, Z.add_0_r. reflexivity. }
assert (HS0 : @st_ok trbsegs fy E0 ss_LCDx (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LCD_HEAD) mem (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LCDx. apply (entry_st_ok_full trbsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold lcd_mem. apply Forall_cons; [|apply Forall_nil].
unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
change (Ereg regs _) with E0. rewrite A33.
split; [clear - Rp Hy Hcut; lia|]. split; [clear - Rp Hy Hcut Hlen; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trbsegs E0 _ (p + 3 * y + cut) 0 1 _ (getz palc (3 * y + cut))); [exact (DN _ _ A32) | zside | zside |].
apply (val_mem_byte trbsegs); [rewrite Z.add_0_r; replace (p + 3 * y + cut) with (p + (3 * y + cut)) by lia; exact Hbyte | exact Hbr].
- apply pairwise_disjoint_of_extents. unfold lcd_mem, extent_of_region. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; [split; [|exact I] | split; [|exact I]]].
+ cbn [lcd_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (Ereg regs _) with E0.
rewrite U10, U12, U20, U21, U23, U26, E27, A32, A33. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - Hy Hcut Hlen Rp Hbr. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
+
unfold acond_ok. cbn [ac_c ac_a ac_b]. change (Ereg regs _) with E0. rewrite YO3v.branch_geu_U, U_SOff, U23, Z.add_0_r.
rewrite zcanon_id by (unfold M64; clear - Rp Hy Hcut Hlen; lia).
apply Bool.negb_true_iff, Z.ltb_ge. pose proof (lcd_U_srl32_lt E0 (SAlu ALU_ADD (SAlu ALU_SLL (SOff 12 0) (SLit 32)) (SAlu ALU_SLL (SOff 20 0) (SLit 32)))) as Hlt.
unfold lcd_off. clear - Hlt Rp Hy Hcut Hlen. lia.
+ change (Ereg regs _) with E0.
unfold lcd_alias. apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U10, U26, A33, !Z.add_0_r.
rewrite (zcanon_id (cut + 3 * y)), (zcanon_id p) by (unfold M64; clear - Rp Hy Hcut Hlen; lia).
f_equal. lia. }
assert (SHOK0 : sh_ok trbsegs lcr_Bx lcd_SH E0 (mrestrict (w_H W) mem)).
{ unfold sh_ok, lcd_SH. constructor; [|constructor].
apply (shent_ok_of_range trbsegs (w_H W) mem E0 lcr_Bx 33 (p + 3 * y + cut) 1 (p + 3 * y + cut) 0 1).
+ apply (range_addressable_of_block trbsegs B LAWS lyc Sc W mem md pb pm _ _ HAR HinP); clear - Hy Hcut Hlen HP0 HP1 Qpm; lia.
+ unfold U, lcr_Bx. cbn [sv_denot]. rewrite E27, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A33.
+ lia.
+ lia.
+ intros z Hz. destruct (al_blocks _ _ LAWS _ _ _ _ _ pb pm HAR HinP) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ pb pm HAR HinP) as Himg.
revert Hz Hia Himg Hy Hcut Hlen HP0 HP1 Qpm Qpb0 Qpb1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia. }
split; [exact (st_ok_enterF trbsegs fy 64 E0 ss_LCDx _ HS0 ltac:(vm_compute; reflexivity) Hfrm)|].
split; [exact (sh_ok_agree trbsegs lcr_Bx lcd_SH 64 E0 E _ (env_agree_ew_fregs E0 64 _) ltac:(vm_compute; reflexivity) SHOK0)|].
split; [exact HE|].
split; [rewrite HEE by lia; exact E32|].
split; [subst E; rewrite <- Hfa5; exact (ew_fregs_at E0 64 (@fp_regs fy) (15%bv : bv 5))|].
rewrite !HEE by lia. repeat split; assumption.
Qed.
Lemma LCD_step : forall (fy : FPState) (regs : bvmap 5 word) mem md (y : Z),
0 <= y < 2 ^ 29 -> 3 * y + cut < zlen palc -> (ptest palc cut s m y = false -> 1 <= y) -> lcd_inv fy regs mem md y ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LCD_HEAD) mem (seg_rom trbsegs)) md)
(fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 (if ptest palc cut s m y then LCD_EXIT else LCD_HEAD)) mem' (seg_rom trbsegs)) md' /\
(if ptest palc cut s m y then lcd_exit fy' regs' mem' md' y else lcd_inv fy' regs' mem' md' (y - 1)) /\
(forall r : bv 5, In r LCD_KEEP -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros fy regs mem md y Hy Hlen Hy1 HI.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof HI as (HB & Hfa5 & G12 & G10 & G20 & G21).
pose proof (lcr_env fy regs mem md HB) as (Qpb0 & Qpb1 & Qpm & C1).
pose proof HB as (HJ & Hfrm & Hpa & G26 & G23 & G27).
assert (Rp : 4096 <= p /\ p + zlen palc <= 140737479966720) by (clear - HP0 HP1 Qpb0 Qpb1 Qpm C1; lia).
destruct (arr8_getz trbsegs _ p palc (3 * y + cut) Hpa ltac:(clear - Hy Hcut Hlen; lia)) as [_ Hbr].
destruct (LCD_seed fy regs mem md y Hy Hlen HI) as (HS & SHOK & HE & HE32 & HE79 & HU12 & HU20 & HU21).
set (E := ew_fregs _ 64 _) in HS, SHOK, HE, HE32, HE79, HU12, HU20, HU21.
aj_run_to_tokF trbtbl_lib_ok HS HJ SHOK lcr_Bspan LCD_BR.
{ cbn [ss_mem]. unfold lcd_mem. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr1; rename HG into HG1; clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msA := msx) in * end.
assert (KW1 : forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) (ms_mem msA) a = aview trbsegs (w_H W) mem a).
{ exact (lg_kept_ro _ _ _ _ _ HFr1 lcd_rs_ro). }
assert (FIN : forall (fz : FPState) E' ss' ms' md' pc' (v10 v20 v21 : Z), @st_ok trbsegs fz E' ss' (restrict (w_H W) ms') -> env_agree 96 E E' ->
ss_pc ss' = pc' -> ss_resv ss' = None ->
sv_denot E' (sr_get (ss_regs ss') 10) = w64 v10 -> sv_denot E' (sr_get (ss_regs ss') 20) = w64 v20 -> sv_denot E' (sr_get (ss_regs ss') 21) = w64 v21 ->
forallb (fun rr : bv 5 => sv_eqb (sr_get (ss_regs ss') rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) LCD_KEEP = true ->
frm_zero (@fp_csr fz) -> reg_get (@fp_regs fz) (15%bv : bv 5) = Z_to_bv 64 mean ->
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') md' k ->
(forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) (ms_mem ms') a = aview trbsegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms') a) ->
SRr trbsegs W (mkCfg ms' md')
(fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md'',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 pc') mem' (seg_rom trbsegs)) md'' /\
lcr_base fy' regs' mem' md'' /\ reg_get (@fp_regs fy') (15%bv : bv 5) = Z_to_bv 64 mean /\
getr regs' 12 = Z_to_bv 64 (cut - 3) /\ getr regs' 10 = w64 v10 /\ getr regs' 20 = w64 v20 /\ getr regs' 21 = w64 v21 /\
(forall r : bv 5, In r LCD_KEEP -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a))).
{ intros fz E' ss' ms' md' pc' v10 v20 v21 HS' [EA ED] Hpc' Hrv' D10 D20 D21 QK Hfz Hfz5 HJ' Hk' Hp'.
assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) [getz palc (3 * y + cut); p + 3 * y + cut] ++ [])) E').
{ split; [intros n Hn; rewrite EA by lia; subst E; rewrite ew_fregs_low by lia; reflexivity | rewrite ED; reflexivity]. }
pose proof (regs_kept_of_st_ok trbsegs E' ss' _ regs _ LCD_KEEP HS' HAE' QK) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trbsegs (w_H W) E' ss' ms' HS' Hrv'), Hpc'. apply SRr_ret.
split; [reflexivity|]. exists fz, (ms_regs ms'), (ms_mem ms'), md'. split; [reflexivity|].
split.
{ split; [exact HJ'|]. split; [exact Hfz|].
split; [exact (arr8_kept mem (ms_mem ms') Hpa Hk' (proj1 Rp) (proj2 Rp))|].
split; [rewrite (HKR (26%bv : bv 5) ltac:(cbv; tauto)); exact G26|].
split; [rewrite (HKR (23%bv : bv 5) ltac:(cbv; tauto)); exact G23|].
rewrite (HKR (27%bv : bv 5) ltac:(cbv; tauto)). exact G27. }
split; [exact Hfz5|].
split; [rewrite (HKR (12%bv : bv 5) ltac:(cbv; tauto)); exact G12|].
split; [rewrite (st_ok_restrict_reg trbsegs (w_H W) E' ss' ms' (10%bv : bv 5) HS'); exact D10|].
split; [rewrite (st_ok_restrict_reg trbsegs (w_H W) E' ss' ms' (20%bv : bv 5) HS'); exact D20|].
split; [rewrite (st_ok_restrict_reg trbsegs (w_H W) E' ss' ms' (21%bv : bv 5) HS'); exact D21|].
split; [exact HKR|]. split; [exact Hk' | exact Hp']. }
assert (HAE96 : env_agree 96 E E) by (apply env_agree_refl).
lg_branchF trbtbl_lib_ok HS.
-
lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
assert (Ht : ptest palc cut s m y = true).
{ cbn [sv_denot] in Hc. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned, !(proj1 HAEx) in Hc by lia.
rewrite (lg_flt_cvt_test RNE _ _ (getz palc (3 * y + cut)) mean s m HE32 HE79 Hbr Hmean Hq) in Hc.
rewrite lcr_beq_bool_w_neg in Hc. exact Hc. }
rewrite Ht.
pose proof (st_okF_frm trbsegs _ _ _ HS) as Hfrm'. pose proof (st_okF_freg trbsegs _ _ _ (15%bv : bv 5) HS) as Hf5'.
lazymatch type of Hf5' with _ = sv_denot ?Ex (sfr_get ?fr ?r) => let v := eval vm_compute in (sfr_get fr r) in change (sfr_get fr r) with v in Hf5' end.
cbn [sv_denot] in Hf5'. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (proj1 HAEx), HE79 in Hf5' by lia.
pose proof (st_okF_to_legacy trbsegs _ _ _ HS) as HSL. clear HS.
aj_run_to_tok trbtbl_lib_ok HSL HJ SHOK lcr_Bspan LCD_EXIT.
{ apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HSL with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 96 E Ey) by (env_agree_chain HAEx) end.
eapply SRr_mono.
{ apply (FIN _ _ _ _ _ LCD_EXIT 0 (3 * y) y HSL HAEy); [reflexivity | reflexivity | | | | vm_compute; reflexivity | exact Hfrm' | exact Hf5' | exact HJ | | ].
+ lcr_sr_get. cbn [sv_denot]. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned, !(proj1 HAEy) by lia.
rewrite (lg_flt_cvt_test RNE _ _ (getz palc (3 * y + cut)) mean s m HE32 HE79 Hbr Hmean Hq). change (ptest palc cut s m y) with (getz palc (3 * y + cut) * s <=? m) in Ht. rewrite Ht. reflexivity.
+ lcr_sr_get. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (proj1 HAEy), (HE 20%nat 20%bv eq_refl) by lia. exact G20.
+ lcr_sr_get. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (proj1 HAEy), (HE 21%nat 21%bv eq_refl) by lia. exact G21.
+ intros a Ha. rewrite (lg_kept_ro _ _ _ _ _ HFr lcd_rs_ro a Ha). exact (KW1 a Ha).
+ intros a Ha. apply (apresent_grows _ _ _ _ HG). apply (apresent_grows _ _ _ _ HG1). exact Ha. }
cbv beta. intros W' c' _ (HW' & fy' & regs' & mem' & md' & Hc' & HB' & Hf5n & R12 & R10 & R20 & R21 & HK' & Hk' & Hp').
split; [exact HW'|]. exists fy', regs', mem', md'. split; [exact Hc'|].
split; [split; [exact HB'|]; split; [exact Hf5n|]; split; [exact R12|]; split; [exact R10|]; split; [exact R20 | exact R21]|].
split; [exact HK'|]. split; [exact Hk' | exact Hp'].
-
lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
assert (Ht : ptest palc cut s m y = false).
{ cbn [sv_denot] in Hc. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned, !(proj1 HAEx) in Hc by lia.
rewrite (lg_flt_cvt_test RNE _ _ (getz palc (3 * y + cut)) mean s m HE32 HE79 Hbr Hmean Hq) in Hc.
rewrite lcr_beq_bool_w_neg in Hc. exact Hc. }
rewrite Ht. pose proof (Hy1 Ht) as Hy1'.
pose proof (st_okF_frm trbsegs _ _ _ HS) as Hfrm'. pose proof (st_okF_freg trbsegs _ _ _ (15%bv : bv 5) HS) as Hf5'.
lazymatch type of Hf5' with _ = sv_denot ?Ex (sfr_get ?fr ?r) => let v := eval vm_compute in (sfr_get fr r) in change (sfr_get fr r) with v in Hf5' end.
cbn [sv_denot] in Hf5'. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (proj1 HAEx), HE79 in Hf5' by lia.
pose proof (st_okF_to_legacy trbsegs _ _ _ HS) as HSL. clear HS.
aj_run_to_tok trbtbl_lib_ok HSL HJ SHOK lcr_Bspan LCD_HEAD.
{ apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HSL with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 96 E Ey) by (env_agree_chain HAEx) end.
eapply SRr_mono.
{ apply (FIN _ _ _ _ _ LCD_HEAD (cut + 3 * (y - 1)) (3 * (y - 1)) (y - 1) HSL HAEy); [reflexivity | reflexivity | | | | vm_compute; reflexivity | exact Hfrm' | exact Hf5' | exact HJ | | ].
+ lcr_sr_get. unfold w64. apply lg_denot_of_U. apply lcd_U_off; [rewrite U_SOff, (proj1 HAEy), HU12, Z.add_0_r by lia; apply zcanon_id; unfold M64; clear - Hcut; lia
| rewrite U_SOff, (proj1 HAEy), HU20, Z.add_0_r by lia; apply zcanon_id; unfold M64; clear - Hy; lia
| exact Hcut | clear - Hy Hy1'; lia].
+ lcr_sr_get. cbn [sv_denot]. rewrite (proj1 HAEy), HU20 by lia. unfold w64. f_equal. lia.
+ lcr_sr_get. cbn [sv_denot]. rewrite (proj1 HAEy), HU21 by lia. reflexivity.
+ intros a Ha. rewrite (lg_kept_ro _ _ _ _ _ HFr lcd_rs_ro a Ha). exact (KW1 a Ha).
+ intros a Ha. apply (apresent_grows _ _ _ _ HG). apply (apresent_grows _ _ _ _ HG1). exact Ha. }
cbv beta. intros W' c' _ (HW' & fy' & regs' & mem' & md' & Hc' & HB' & Hf5n & R12 & R10 & R20 & R21 & HK' & Hk' & Hp').
split; [exact HW'|]. exists fy', regs', mem', md'. split; [exact Hc'|].
split; [split; [exact HB'|]; split; [exact Hf5n|]; split; [exact R12|]; split; [exact R10|]; split; [exact R20 | exact R21]|].
split; [exact HK'|]. split; [exact Hk' | exact Hp'].
Qed.
Definition LCD_post (regs : bvmap 5 word) (mem : word -> option byte) (k1 : Z) : world trbsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 LCD_EXIT) mem' (seg_rom trbsegs)) md' /\
lcd_exit fy' regs' mem' md' k1 /\
(forall r : bv 5, In r LCD_KEEP -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Lemma LCD_last : forall (fy : FPState) (regs : bvmap 5 word) mem md (k1 : Z),
0 <= k1 < 2 ^ 29 -> 3 * k1 + cut < zlen palc -> ptest palc cut s m k1 = true -> lcd_inv fy regs mem md k1 ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LCD_HEAD) mem (seg_rom trbsegs)) md) (LCD_post regs mem k1).
Proof.
intros fy regs mem md k1 Hk1 Hlen Hbig HI.
eapply SRr_mono; [exact (LCD_step fy regs mem md k1 Hk1 Hlen ltac:(intros Hf; rewrite Hbig in Hf; discriminate Hf) HI)|].
cbv beta. rewrite Hbig. intros W' c' _ H. exact H.
Qed.
Lemma LCD_loop : forall (n : nat) (fy : FPState) (regs : bvmap 5 word) mem md (y k1 : Z),
y - k1 <= Z.of_nat n -> 0 <= k1 <= y -> y < 2 ^ 29 -> 3 * y + cut < zlen palc ->
(forall z, k1 < z <= y -> ptest palc cut s m z = false) -> ptest palc cut s m k1 = true ->
lcd_inv fy regs mem md y ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LCD_HEAD) mem (seg_rom trbsegs)) md) (LCD_post regs mem k1).
Proof.
induction n as [|n IH]; intros fy regs mem md y k1 Hn Hy Hy1 Hlen Hsm Hbig HI.
- assert (y = k1) by lia. subst y. exact (LCD_last fy regs mem md k1 ltac:(lia) Hlen Hbig HI).
- destruct (Z.eq_dec y k1) as [-> | Hne]; [exact (LCD_last fy regs mem md k1 ltac:(lia) Hlen Hbig HI)|].
eapply SRr_bind; [exact (LCD_step fy regs mem md y ltac:(lia) Hlen ltac:(intros _; lia) HI)|].
cbv beta. rewrite (Hsm y ltac:(lia)). intros W' c' _ (-> & fy' & regs' & mem' & md' & -> & HI' & Hk' & Hm' & Hp').
eapply SRr_mono; [exact (IH fy' regs' mem' md' (y - 1) k1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros z Hz; apply Hsm; lia) Hbig HI')|].
cbv beta. intros W'' c'' _ (HW & fy'' & regs'' & mem'' & md'' & Hc & HX'' & Hk'' & Hm'' & Hp'').
split; [exact HW|]. exists fy'', regs'', mem'', md''. split; [exact Hc|]. split; [exact HX''|].
split; [intros r Hr; rewrite (Hk'' r Hr); apply Hk'; exact Hr|].
split; [intros a Ha; rewrite (Hm'' a Ha); apply Hm'; exact Ha|].
intros a Ha. apply Hp''. apply Hp'. exact Ha.
Qed.
End d.
Lemma rga_lcr_up {rc : YN05.RunCeil} : forall (B : asyms), AR_laws trbsegs B ->
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W pb pm p palc cut mean s m nb nn ma v25 x i1 (fy : FPState) (regs : bvmap 5 word) memc mdc,
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
frm_zero (@fp_csr fy) -> 0 <= mean < 2 ^ 64 -> is_quot mean m s ->
In (pb, pm) (ablocks B lyc Sc) -> pb <= p -> p + zlen palc <= pb + pm ->
arr8 trbsegs (mrestrict (w_H W) memc) p palc ->
In (nb, nn) (ablocks B lyc Sc) -> nb <= ma -> ma + 8 <= nb + nn -> ma mod 8 = 0 -> (pb, pm) <> (nb, nn) ->
val_mem trbsegs (mrestrict (w_H W) memc) ma 8 mean ->
0 <= cut <= 2 -> 0 <= x <= i1 -> i1 < 2 ^ 29 -> 3 * i1 + cut < zlen palc ->
(forall z, x <= z < i1 -> ptest palc cut s m z = true) -> ptest palc cut s m i1 = false ->
getr regs 11 = w64 (cut + 3 * x) -> getr regs 13 = w64 (3 * x) -> getr regs 18 = w64 x -> getr regs 24 = w64 (3 * x) ->
getr regs 10 = w64 ma -> getr regs 12 = w64 cut -> getr regs 14 = w64 (8 * cut) -> getr regs 15 = w64 (cut + 3) ->
getr regs 25 = w64 v25 -> 16 <= v25 < 2 ^ 64 -> getr regs 5 = w64 2 ->
getr regs 26 = w64 p -> getr regs 23 = w64 (2 ^ 64 - 1 - p) -> getr regs 27 = w64 SB ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LCU_HEAD) memc (seg_rom trbsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists (fy' : FPState) regs2 mem2 md2,
c2 = mkCfg (@mkst fy' regs2 (Z_to_bv 64 LCU_EXIT) mem2 (seg_rom trbsegs)) md2 /\
frm_zero (@fp_csr fy') /\ reg_get (@fp_regs fy') (15%bv : bv 5) = Z_to_bv 64 mean /\
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
(forall r : bv 5, reg_in r LCU_CLOB = false -> getr regs2 r = getr regs r) /\
getr regs2 18 = w64 i1 /\ getr regs2 13 = w64 (3 * i1) /\ getr regs2 24 = w64 (3 * i1) /\ getr regs2 11 = w64 0 /\
(forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) mem2 a = aview trbsegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a)).
Proof.
intros B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W pb pm p palc cut mean s m nb nn ma v25 x i1 fy regs memc mdc
HJ Hfrm Hmean Hq HinP HP0 HP1 Hpa HinN HN0 HN1 HN8 HPN Vmean Hcut Hx Hi1 Hlen Hsm Hbig G11 G13 G18 G24 G10 G12 G14 G15 G25 H25 G5 G26 G23 G27.
eapply SRr_mono.
{ apply (LCU_loop B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W pb pm p palc cut mean s m HinP HP0 HP1 Hcut Hmean Hq nb nn ma v25 HinN HN0 HN1 HN8 HPN H25
(Z.to_nat (i1 - x)) fy regs memc mdc x i1 ltac:(lia) Hx Hi1 Hlen Hsm Hbig).
unfold lcu_inv, lcu_base, lcr_base. repeat match goal with |- _ /\ _ => split end; assumption. }
cbv beta. intros W2 c2 _ (HW & fy' & regs2 & mem2 & md2 & Hc & (((HJ2 & Hfrm2 & _) & _) & Hfa52 & R11 & R13 & R18 & R24) & Hk & Hm & Hp).
split; [exact HW|]. exists fy', regs2, mem2, md2. split; [exact Hc|]. split; [exact Hfrm2|]. split; [exact Hfa52|]. split; [exact HJ2|].
split.
{ intros r Hr. destruct (lcu_clob_cases r Hr) as [-> | Hin]; [|exact (Hk r Hin)]. rewrite !getr_zero. reflexivity. }
split; [exact R18|]. split; [exact R13|]. split; [exact R24|]. split; [exact R11|]. split; [exact Hm | exact Hp].
Qed.
Lemma rga_lcr_down {rc : YN05.RunCeil} : forall (B : asyms), AR_laws trbsegs B ->
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W pb pm p palc cut mean s m y k1 (fy : FPState) (regs : bvmap 5 word) memc mdc,
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
frm_zero (@fp_csr fy) -> reg_get (@fp_regs fy) (15%bv : bv 5) = Z_to_bv 64 mean -> 0 <= mean < 2 ^ 64 -> is_quot mean m s ->
In (pb, pm) (ablocks B lyc Sc) -> pb <= p -> p + zlen palc <= pb + pm ->
arr8 trbsegs (mrestrict (w_H W) memc) p palc ->
0 <= cut <= 2 -> 0 <= k1 <= y -> y < 2 ^ 29 -> 3 * y + cut < zlen palc ->
(forall z, k1 < z <= y -> ptest palc cut s m z = false) -> ptest palc cut s m k1 = true ->
getr regs 12 = Z_to_bv 64 (cut - 3) -> getr regs 10 = w64 (cut + 3 * y) -> getr regs 20 = w64 (3 * y) -> getr regs 21 = w64 y ->
getr regs 26 = w64 p -> getr regs 23 = w64 (2 ^ 64 - 1 - p) -> getr regs 27 = w64 SB ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LCD_HEAD) memc (seg_rom trbsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists (fy' : FPState) regs2 mem2 md2,
c2 = mkCfg (@mkst fy' regs2 (Z_to_bv 64 LCD_EXIT) mem2 (seg_rom trbsegs)) md2 /\
frm_zero (@fp_csr fy') /\ reg_get (@fp_regs fy') (15%bv : bv 5) = Z_to_bv 64 mean /\
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
(forall r : bv 5, reg_in r LCD_CLOB = false -> getr regs2 r = getr regs r) /\
getr regs2 21 = w64 k1 /\ getr regs2 20 = w64 (3 * k1) /\ getr regs2 10 = w64 0 /\
(forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) mem2 a = aview trbsegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a)).
Proof.
intros B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W pb pm p palc cut mean s m y k1 fy regs memc mdc
HJ Hfrm Hfa5 Hmean Hq HinP HP0 HP1 Hpa Hcut Hy Hy1 Hlen Hsm Hbig G12 G10 G20 G21 G26 G23 G27.
eapply SRr_mono.
{ apply (LCD_loop B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W pb pm p palc cut mean s m HinP HP0 HP1 Hcut Hmean Hq
(Z.to_nat (y - k1)) fy regs memc mdc y k1 ltac:(lia) Hy Hy1 Hlen Hsm Hbig).
unfold lcd_inv, lcr_base. repeat match goal with |- _ /\ _ => split end; assumption. }
cbv beta. intros W2 c2 _ (HW & fy' & regs2 & mem2 & md2 & Hc & ((HJ2 & Hfrm2 & _) & Hfa52 & R12 & R10 & R20 & R21) & Hk & Hm & Hp).
split; [exact HW|]. exists fy', regs2, mem2, md2. split; [exact Hc|]. split; [exact Hfrm2|]. split; [exact Hfa52|]. split; [exact HJ2|].
split.
{ intros r Hr. destruct (lcd_clob_cases r Hr) as [-> | Hin]; [|exact (Hk r Hin)]. rewrite !getr_zero. reflexivity. }
split; [exact R21|]. split; [exact R20|]. split; [exact R10|]. split; [exact Hm | exact Hp].
Qed.
