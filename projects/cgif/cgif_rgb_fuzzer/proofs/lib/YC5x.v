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
YG00 YG0a YG01 YG0h YG0u YG0d YC04 YC06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2u YC1b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM00 YM04 YM01 YM02 YM03 YM06 YP14 YI08 YI0c YI0g YI0d YI0f YI09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC68.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition LCU_HEAD : Z := 0x836a8.
Definition LCU_BR : Z := 0x836dc.
Definition LCU_EXIT : Z := 0x836f0.
Definition LCD_HEAD : Z := 0x83700.
Definition LCD_BR : Z := 0x83734.
Definition LCD_EXIT : Z := 0x83748.
Definition LCU_CLOB : list (bv 5) := [10; 12; 13; 14; 23]%bv.
Definition LCU_KEEP : list (bv 5) := [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 15; 16; 17; 18; 19; 20; 21; 22; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LCD_CLOB : list (bv 5) := [10; 13; 14; 15; 21]%bv.
Definition LCD_KEEP : list (bv 5) := [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 16; 17; 18; 19; 20; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
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
Section b.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)) (k : Z).
Variables (lyc : alayout) (Sc : astate) (W : world trasegs).
Variables (pb pm p : Z) (palc : list Z) (cut mean s m : Z).
Hypothesis HinP : In (pb, pm) (ablocks B lyc Sc). Hypothesis HP0 : pb <= p. Hypothesis HP1 : p + zlen palc <= pb + pm.
Hypothesis Hcut : 0 <= cut <= 2.
Hypothesis Hmean : 0 <= mean < 2 ^ 64. Hypothesis Hq : is_quot mean m s.
Definition lcr_base (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k /\
frm_zero (@fp_csr fy) /\ reg_get (@fp_regs fy) (15%bv : bv 5) = Z_to_bv 64 mean /\
arr8 trasegs (mrestrict (w_H W) mem) p palc /\
getr regs 11 = w64 cut /\ getr regs 26 = w64 p /\ getr regs 25 = w64 SB.
Definition lcu_inv (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (x : Z) : Prop :=
lcr_base fy regs mem md /\ getr regs 12 = w64 (3 * x) /\ getr regs 23 = Z_to_bv 64 (x - 1).
Definition lcu_exit (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (x : Z) : Prop :=
lcr_base fy regs mem md /\ getr regs 12 = w64 (3 * x + 3) /\ getr regs 23 = w64 x /\ getr regs 10 = w64 0.
Lemma lcr_env : forall fy regs mem md, lcr_base fy regs mem md ->
4096 <= pb /\ pb + req_size pm <= alloc_ceiling /\ pm <= req_size pm /\ 140735332483072 <= alloc_ceiling <= 140737479966720.
Proof.
intros fy regs mem md (HJ & _). pose proof HJ as (HAR & _). pose proof asan_consts as (C1 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pb pm HAR HinP) as (_ & Hp4096 & Hpceil & _ & _ & _ & Hpm0).
pose proof (req_size_pos pm ltac:(lia)) as [_ Hrp]. repeat split; try assumption; lia.
Qed.
Definition lcu_alias : sv := SAlu ALU_ADD (SAlu ALU_ADD (SOff 11 0) (SOff 12 0)) (SOff 26 0).
Definition lcr_mem : smem := [ YQ0b.mkRegion (Some 33%nat) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SOff 32 0))] ].
Definition lcu_facts : facts :=
mkFacts [ (11%nat, mkAF 0 2 0); (12%nat, mkAF 0 (3 * 2^29) 0); (26%nat, mkAF 4096 140737479966720 0);
(25%nat, mkAF SB SB 0); (32%nat, mkAF 0 255 0); (33%nat, mkAF 4096 140737479966720 0) ] [] [ (lcu_alias, SOff 33 0) ].
Definition ss_LCUx : sstate := mkSS LCU_HEAD sr_atoms lcr_mem None lcu_facts.
Definition lcr_Bx : sv := SOff 25 0.
Definition lcr_SH : list shent := [ mkSHE 33 0 1 ].
Definition lcr_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Lemma lcr_rs_ro : forall rr, In rr lcr_mem -> YQ0b.r_whi rr <= YQ0b.r_wlo rr.
Proof. intros rr [<- | []]. cbn. lia. Qed.
Lemma LCU_seed : forall (fy : FPState) (regs : bvmap 5 word) mem md (x : Z),
0 <= x < 2 ^ 29 -> 3 * x + cut < zlen palc -> lcu_inv fy regs mem md x ->
let E0 := Ereg regs (map (Z_to_bv 64) [getz palc (3 * x + cut); p + 3 * x + cut] ++ []) in
let E := ew_fregs E0 64 (@fp_regs fy) in
st_okF trasegs E (mkSST LCU_HEAD sr_atoms (sfr_atoms 64) lcr_mem None lcu_facts)
(restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LCU_HEAD) mem (seg_rom trasegs))) /\
sh_ok trasegs lcr_Bx lcr_SH E (mrestrict (w_H W) mem) /\
(forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) /\
ew E 32 = Z_to_bv 64 (getz palc (3 * x + cut)) /\ ew E 79 = Z_to_bv 64 mean /\
bv_unsigned (ew E 12) = 3 * x.
Proof.
intros fy regs mem md x Hx Hlen HI E0 E.
pose proof HI as (HB & G12 & G23).
pose proof (lcr_env fy regs mem md HB) as (Qpb0 & Qpb1 & Qpm & C1).
pose proof HB as (HJ & Hfrm & Hfa5 & Hpa & G11 & G26 & G25).
pose proof HJ as (HAR & _).
destruct (arr8_getz trasegs _ p palc (3 * x + cut) Hpa ltac:(clear - Hx Hcut Hlen; lia)) as [Hbyte Hbr].
assert (HE0 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E0 n = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall i v, nth_error [getz palc (3 * x + cut); p + 3 * x + cut] i = Some v -> ew E0 (32 + i) = Z_to_bv 64 v) by (intros i v Hi; subst E0; apply Ereg_vals; exact Hi).
assert (HEE : forall n, (n < 64)%nat -> ew E n = ew E0 n) by (intros n Hn; subst E; apply ew_fregs_low; exact Hn).
assert (HE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5. rewrite HEE by lia. apply HE0. exact Hn. }
assert (Rp : 4096 <= p /\ p + zlen palc <= 140737479966720) by (clear - HP0 HP1 Qpb0 Qpb1 Qpm C1; lia).
assert (U11 : bv_unsigned (ew E0 11) = cut) by (rewrite (HE0 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; clear - Hcut; lia).
assert (U12 : bv_unsigned (ew E0 12) = 3 * x) by (rewrite (HE0 12%nat 12%bv eq_refl), G12; apply unsigned_lit_small; clear - Hx; lia).
assert (U26 : bv_unsigned (ew E0 26) = p) by (rewrite (HE0 26%nat 26%bv eq_refl), G26; apply unsigned_lit_small; clear - Rp Hx Hcut Hlen; lia).
assert (E25 : ew E0 25 = w64 SB) by (rewrite (HE0 25%nat 25%bv eq_refl); exact G25).
assert (E32 : ew E0 32 = Z_to_bv 64 (getz palc (3 * x + cut))) by (pose proof (HV 0%nat _ eq_refl) as X; cbn [Nat.add] in X; exact X).
assert (A32 : bv_unsigned (ew E0 32) = getz palc (3 * x + cut)) by (rewrite E32; apply unsigned_lit_small; clear - Hbr; lia).
assert (A33 : bv_unsigned (ew E0 33) = p + 3 * x + cut).
{ pose proof (HV 1%nat _ eq_refl) as X. cbn [Nat.add] in X. rewrite X. apply unsigned_lit_small. clear - Rp Hx Hcut Hlen. lia. }
assert (DN : forall n v, bv_unsigned (ew E0 n) = v -> sv_denot E0 (SOff n 0) = Z_to_bv 64 v).
{ intros n v Hn. cbn [sv_denot]. rewrite Hn, Z.add_0_r. reflexivity. }
assert (HS0 : @st_ok trasegs fy E0 ss_LCUx (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LCU_HEAD) mem (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LCUx. apply (entry_st_ok_full trasegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold lcr_mem. apply Forall_cons; [|apply Forall_nil].
unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
change (Ereg regs _) with E0. rewrite A33.
split; [clear - Rp Hx Hcut; lia|]. split; [clear - Rp Hx Hcut Hlen; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trasegs E0 _ (p + 3 * x + cut) 0 1 _ (getz palc (3 * x + cut))); [exact (DN _ _ A32) | zside | zside |].
apply (val_mem_byte trasegs); [rewrite Z.add_0_r; replace (p + 3 * x + cut) with (p + (3 * x + cut)) by lia; exact Hbyte | exact Hbr].
- apply pairwise_disjoint_of_extents. unfold lcr_mem, extent_of_region. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; [exact I|]].
+ cbn [lcu_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (Ereg regs _) with E0.
rewrite U11, U12, U26, E25, A32, A33. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - Hx Hcut Hlen Rp Hbr. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
+ cbn [lcu_facts f_alias alias_ok]. change (Ereg regs _) with E0. split; [|exact I].
unfold lcu_alias. apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U11, U12, U26, A33, !Z.add_0_r.
rewrite (zcanon_id cut), (zcanon_id (3 * x)), (zcanon_id p) by (unfold M64; clear - Rp Hx Hcut Hlen; lia).
rewrite (zcanon_id (cut + 3 * x)) by (unfold M64; clear - Hx Hcut; lia). f_equal. lia. }
assert (SHOK0 : sh_ok trasegs lcr_Bx lcr_SH E0 (mrestrict (w_H W) mem)).
{ unfold sh_ok, lcr_SH. constructor; [|constructor].
apply (shent_ok_of_range trasegs (w_H W) mem E0 lcr_Bx 33 (p + 3 * x + cut) 1 (p + 3 * x + cut) 0 1).
+ apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md pb pm _ _ HAR HinP); clear - Hx Hcut Hlen HP0 HP1 Qpm; lia.
+ unfold U, lcr_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A33.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ pb pm HAR HinP) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ pb pm HAR HinP) as Himg.
revert Hy Hia Himg Hx Hcut Hlen HP0 HP1 Qpm Qpb0 Qpb1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia. }
split; [exact (st_ok_enterF trasegs fy 64 E0 ss_LCUx _ HS0 ltac:(vm_compute; reflexivity) Hfrm)|].
split; [exact (sh_ok_agree trasegs lcr_Bx lcr_SH 64 E0 E _ (env_agree_ew_fregs E0 64 _) ltac:(vm_compute; reflexivity) SHOK0)|].
split; [exact HE|].
split; [rewrite HEE by lia; exact E32|].
split; [|rewrite HEE by lia; exact U12].
subst E. rewrite <- Hfa5. exact (ew_fregs_at E0 64 (@fp_regs fy) (15%bv : bv 5)).
Qed.
Definition lcu_cond : sv := SF2 (FP2_cmp F_LE FMT_D) (SF1 (FP1_cvt FC_D FC_WU RNE) (SOff 32 0)) (SOff 79 0).
Lemma arr8_kept : forall (mem mem' : word -> option byte),
arr8 trasegs (mrestrict (w_H W) mem) p palc ->
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) ->
4096 <= p -> p + zlen palc <= 140737479966720 ->
arr8 trasegs (mrestrict (w_H W) mem') p palc.
Proof.
intros mem mem' Hpa Hk Hp0 Hp1. apply (arr8_frame trasegs _ _ p palc Hpa). intros a Ha. apply (mbyte_of_aview trasegs). apply Hk. lia.
Qed.
Lemma LCU_step : forall (fy : FPState) (regs : bvmap 5 word) mem md (x : Z),
0 <= x < 2 ^ 29 -> 3 * x + cut < zlen palc -> lcu_inv fy regs mem md x ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LCU_HEAD) mem (seg_rom trasegs)) md)
(fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 (if ptest palc cut s m x then LCU_HEAD else LCU_EXIT)) mem' (seg_rom trasegs)) md' /\
(if ptest palc cut s m x then lcu_inv fy' regs' mem' md' (x + 1) else lcu_exit fy' regs' mem' md' x) /\
(forall r : bv 5, In r LCU_KEEP -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros fy regs mem md x Hx Hlen HI.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HI as (HB & G12 & G23).
pose proof (lcr_env fy regs mem md HB) as (Qpb0 & Qpb1 & Qpm & C1).
pose proof HB as (HJ & Hfrm & Hfa5 & Hpa & G11 & G26 & G25).
assert (Rp : 4096 <= p /\ p + zlen palc <= 140737479966720) by (clear - HP0 HP1 Qpb0 Qpb1 Qpm C1; lia).
destruct (arr8_getz trasegs _ p palc (3 * x + cut) Hpa ltac:(clear - Hx Hcut Hlen; lia)) as [_ Hbr].
destruct (LCU_seed fy regs mem md x Hx Hlen HI) as (HS & SHOK & HE & HE32 & HE79 & HU12).
set (E := ew_fregs _ 64 _) in HS, SHOK, HE, HE32, HE79, HU12.
aj_run_to_tokF tratbl_lib_ok HS HJ SHOK lcr_Bspan LCU_BR.
{ cbn [ss_mem]. unfold lcr_mem. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr1; rename HG into HG1; clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msA := msx) in * end.
assert (KW1 : forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) (ms_mem msA) a = aview trasegs (w_H W) mem a).
{ exact (lg_kept_ro _ _ _ _ _ HFr1 lcr_rs_ro). }
assert (FIN : forall (fz : FPState) E' ss' ms' md' pc', @st_ok trasegs fz E' ss' (restrict (w_H W) ms') -> env_agree 96 E E' ->
ss_pc ss' = pc' -> ss_resv ss' = None ->
sr_get (ss_regs ss') 12 = SOff 12 3 -> sr_get (ss_regs ss') 23 = SAluw ALU_ADD (SOff 23 0) (SLit 1) -> sr_get (ss_regs ss') 10 = lcu_cond ->
forallb (fun rr : bv 5 => sv_eqb (sr_get (ss_regs ss') rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) LCU_KEEP = true ->
frm_zero (@fp_csr fz) -> reg_get (@fp_regs fz) (15%bv : bv 5) = Z_to_bv 64 mean ->
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') md' k ->
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) (ms_mem ms') a = aview trasegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms') a) ->
SRr trasegs W (mkCfg ms' md')
(fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md'',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 pc') mem' (seg_rom trasegs)) md'' /\
lcr_base fy' regs' mem' md'' /\ getr regs' 12 = w64 (3 * x + 3) /\ getr regs' 23 = w64 x /\
getr regs' 10 = (if ptest palc cut s m x then Sem.w1 else Sem.w0) /\
(forall r : bv 5, In r LCU_KEEP -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a))).
{ intros fz E' ss' ms' md' pc' HS' [EA ED] Hpc' Hrv' Q12 Q23 Q10 QK Hfz Hfz5 HJ' Hk' Hp'.
assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) [getz palc (3 * x + cut); p + 3 * x + cut] ++ [])) E').
{ split; [intros n Hn; rewrite EA by lia; subst E; rewrite ew_fregs_low by lia; reflexivity | rewrite ED; reflexivity]. }
pose proof (regs_kept_of_st_ok trasegs E' ss' _ regs _ LCU_KEEP HS' HAE' QK) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trasegs (w_H W) E' ss' ms' HS' Hrv'), Hpc'. apply SRr_ret.
split; [reflexivity|]. exists fz, (ms_regs ms'), (ms_mem ms'), md'. split; [reflexivity|].
split.
{ split; [exact HJ'|]. split; [exact Hfz|]. split; [exact Hfz5|].
split; [exact (arr8_kept mem (ms_mem ms') Hpa Hk' (proj1 Rp) (proj2 Rp))|].
split; [rewrite (HKR (11%bv : bv 5) ltac:(cbv; tauto)); exact G11|].
split; [rewrite (HKR (26%bv : bv 5) ltac:(cbv; tauto)); exact G26|].
rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)). exact G25. }
split; [rewrite (st_ok_restrict_reg trasegs (w_H W) E' ss' ms' (12%bv : bv 5) HS'), Q12; cbn [sv_denot]; rewrite EA, HU12 by lia; reflexivity|].
split.
{ rewrite (st_ok_restrict_reg trasegs (w_H W) E' ss' ms' (23%bv : bv 5) HS'), Q23.
apply lg_addw1_pred; [cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, EA by lia; rewrite (HE 23%nat 23%bv eq_refl); exact G23 | clear - Hx; lia]. }
split.
{ rewrite (st_ok_restrict_reg trasegs (w_H W) E' ss' ms' (10%bv : bv 5) HS'), Q10. unfold lcu_cond. cbn [sv_denot].
rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned, !EA by lia.
rewrite (lg_fle_cvt_test RNE _ _ (getz palc (3 * x + cut)) mean s m HE32 HE79 Hbr Hmean Hq). reflexivity. }
split; [exact HKR|]. split; [exact Hk' | exact Hp']. }
assert (HAE96 : env_agree 96 E E) by (apply env_agree_refl).
lg_branchF tratbl_lib_ok HS.
-
lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
assert (Ht : ptest palc cut s m x = true).
{ cbn [sv_denot] in Hc. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned, !(proj1 HAEx) in Hc by lia.
rewrite (lg_fle_cvt_test RNE _ _ (getz palc (3 * x + cut)) mean s m HE32 HE79 Hbr Hmean Hq) in Hc.
rewrite lg_bne_bool_w in Hc. exact Hc. }
rewrite Ht.
pose proof (st_okF_frm trasegs _ _ _ HS) as Hfrm'. pose proof (st_okF_freg trasegs _ _ _ (15%bv : bv 5) HS) as Hf5'.
lazymatch type of Hf5' with _ = sv_denot ?Ex (sfr_get ?fr ?r) => let v := eval vm_compute in (sfr_get fr r) in change (sfr_get fr r) with v in Hf5' end.
cbn [sv_denot] in Hf5'. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (proj1 HAEx), HE79 in Hf5' by lia.
pose proof (st_okF_to_legacy trasegs _ _ _ HS) as HSL. clear HS.
aj_run_to_tok tratbl_lib_ok HSL HJ SHOK lcr_Bspan LCU_HEAD.
{ apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HSL with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 96 E Ey) by (env_agree_chain HAEx) end.
eapply SRr_mono.
{ apply (FIN _ _ _ _ _ LCU_HEAD HSL HAEy); [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | exact Hfrm' | | exact HJ | | ].
+ exact Hf5'.
+ intros a Ha. rewrite (lg_kept_ro _ _ _ _ _ HFr lcr_rs_ro a Ha). exact (KW1 a Ha).
+ intros a Ha. apply (apresent_grows _ _ _ _ HG). apply (apresent_grows _ _ _ _ HG1). exact Ha. }
cbv beta. intros W' c' _ (HW' & fy' & regs' & mem' & md' & Hc' & HB' & R12 & R23 & R10 & HK' & Hk' & Hp').
split; [exact HW'|]. exists fy', regs', mem', md'. split; [exact Hc'|].
split; [split; [exact HB'|]; split; [rewrite R12; unfold w64; f_equal; lia | rewrite R23; unfold w64; f_equal; lia]|].
split; [exact HK'|]. split; [exact Hk' | exact Hp'].
-
lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
assert (Ht : ptest palc cut s m x = false).
{ cbn [sv_denot] in Hc. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned, !(proj1 HAEx) in Hc by lia.
rewrite (lg_fle_cvt_test RNE _ _ (getz palc (3 * x + cut)) mean s m HE32 HE79 Hbr Hmean Hq) in Hc.
rewrite lg_bne_bool_w in Hc. exact Hc. }
rewrite Ht.
pose proof (st_okF_frm trasegs _ _ _ HS) as Hfrm'. pose proof (st_okF_freg trasegs _ _ _ (15%bv : bv 5) HS) as Hf5'.
lazymatch type of Hf5' with _ = sv_denot ?Ex (sfr_get ?fr ?r) => let v := eval vm_compute in (sfr_get fr r) in change (sfr_get fr r) with v in Hf5' end.
cbn [sv_denot] in Hf5'. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (proj1 HAEx), HE79 in Hf5' by lia.
pose proof (st_okF_to_legacy trasegs _ _ _ HS) as HSL. clear HS.
aj_run_to_tok tratbl_lib_ok HSL HJ SHOK lcr_Bspan LCU_EXIT.
{ apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HSL with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 96 E Ey) by (env_agree_chain HAEx) end.
eapply SRr_mono.
{ apply (FIN _ _ _ _ _ LCU_EXIT HSL HAEy); [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | exact Hfrm' | | exact HJ | | ].
+ exact Hf5'.
+ intros a Ha. rewrite (lg_kept_ro _ _ _ _ _ HFr lcr_rs_ro a Ha). exact (KW1 a Ha).
+ intros a Ha. apply (apresent_grows _ _ _ _ HG). apply (apresent_grows _ _ _ _ HG1). exact Ha. }
cbv beta. intros W' c' _ (HW' & fy' & regs' & mem' & md' & Hc' & HB' & R12 & R23 & R10 & HK' & Hk' & Hp').
split; [exact HW'|]. exists fy', regs', mem', md'. split; [exact Hc'|].
split; [split; [exact HB'|]; split; [exact R12|]; split; [exact R23 | rewrite R10, Ht; reflexivity]|].
split; [exact HK'|]. split; [exact Hk' | exact Hp'].
Qed.
Definition LCU_post (regs : bvmap 5 word) (mem : word -> option byte) (i1 : Z) : world trasegs -> config -> Prop :=
fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 LCU_EXIT) mem' (seg_rom trasegs)) md' /\
lcu_exit fy' regs' mem' md' i1 /\
(forall r : bv 5, In r LCU_KEEP -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Lemma LCU_last : forall (fy : FPState) (regs : bvmap 5 word) mem md (i1 : Z),
0 <= i1 < 2 ^ 29 -> 3 * i1 + cut < zlen palc -> ptest palc cut s m i1 = false -> lcu_inv fy regs mem md i1 ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LCU_HEAD) mem (seg_rom trasegs)) md) (LCU_post regs mem i1).
Proof.
intros fy regs mem md i1 Hi1 Hlen Hbig HI.
eapply SRr_mono; [exact (LCU_step fy regs mem md i1 Hi1 Hlen HI)|].
cbv beta. rewrite Hbig. intros W' c' _ H. exact H.
Qed.
Lemma LCU_loop : forall (n : nat) (fy : FPState) (regs : bvmap 5 word) mem md (x i1 : Z),
i1 - x <= Z.of_nat n -> 0 <= x <= i1 -> i1 < 2 ^ 29 -> 3 * i1 + cut < zlen palc ->
(forall z, x <= z < i1 -> ptest palc cut s m z = true) -> ptest palc cut s m i1 = false ->
lcu_inv fy regs mem md x ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LCU_HEAD) mem (seg_rom trasegs)) md) (LCU_post regs mem i1).
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
Definition lcd_inv (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (y : Z) : Prop :=
lcr_base fy regs mem md /\ getr regs 13 = w64 (3 * y) /\ getr regs 21 = w64 (y + 1).
Definition lcd_exit (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (y : Z) : Prop :=
lcr_base fy regs mem md /\ getr regs 13 = Z_to_bv 64 (3 * y - 3) /\ getr regs 21 = w64 y /\ getr regs 10 = w64 0.
Definition lcd_alias : sv := SAlu ALU_ADD (SAlu ALU_ADD (SOff 11 0) (SOff 13 0)) (SOff 26 0).
Definition lcd_facts : facts :=
mkFacts [ (11%nat, mkAF 0 2 0); (13%nat, mkAF 0 (3 * 2^29) 0); (26%nat, mkAF 4096 140737479966720 0);
(25%nat, mkAF SB SB 0); (32%nat, mkAF 0 255 0); (33%nat, mkAF 4096 140737479966720 0) ] [] [ (lcd_alias, SOff 33 0) ].
Definition ss_LCDx : sstate := mkSS LCD_HEAD sr_atoms lcr_mem None lcd_facts.
Definition lcd_cond : sv := SF2 (FP2_cmp F_LT FMT_D) (SOff 79 0) (SF1 (FP1_cvt FC_D FC_WU RNE) (SOff 32 0)).
Lemma LCD_seed : forall (fy : FPState) (regs : bvmap 5 word) mem md (y : Z),
0 <= y < 2 ^ 29 -> 3 * y + cut < zlen palc -> lcd_inv fy regs mem md y ->
let E0 := Ereg regs (map (Z_to_bv 64) [getz palc (3 * y + cut); p + 3 * y + cut] ++ []) in
let E := ew_fregs E0 64 (@fp_regs fy) in
st_okF trasegs E (mkSST LCD_HEAD sr_atoms (sfr_atoms 64) lcr_mem None lcd_facts)
(restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LCD_HEAD) mem (seg_rom trasegs))) /\
sh_ok trasegs lcr_Bx lcr_SH E (mrestrict (w_H W) mem) /\
(forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) /\
ew E 32 = Z_to_bv 64 (getz palc (3 * y + cut)) /\ ew E 79 = Z_to_bv 64 mean /\
bv_unsigned (ew E 13) = 3 * y.
Proof.
intros fy regs mem md x Hx Hlen HI E0 E.
pose proof HI as (HB & G13 & G21).
pose proof (lcr_env fy regs mem md HB) as (Qpb0 & Qpb1 & Qpm & C1).
pose proof HB as (HJ & Hfrm & Hfa5 & Hpa & G11 & G26 & G25).
pose proof HJ as (HAR & _).
destruct (arr8_getz trasegs _ p palc (3 * x + cut) Hpa ltac:(clear - Hx Hcut Hlen; lia)) as [Hbyte Hbr].
assert (HE0 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E0 n = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall i v, nth_error [getz palc (3 * x + cut); p + 3 * x + cut] i = Some v -> ew E0 (32 + i) = Z_to_bv 64 v) by (intros i v Hi; subst E0; apply Ereg_vals; exact Hi).
assert (HEE : forall n, (n < 64)%nat -> ew E n = ew E0 n) by (intros n Hn; subst E; apply ew_fregs_low; exact Hn).
assert (HE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5. rewrite HEE by lia. apply HE0. exact Hn. }
assert (Rp : 4096 <= p /\ p + zlen palc <= 140737479966720) by (clear - HP0 HP1 Qpb0 Qpb1 Qpm C1; lia).
assert (U11 : bv_unsigned (ew E0 11) = cut) by (rewrite (HE0 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; clear - Hcut; lia).
assert (U13 : bv_unsigned (ew E0 13) = 3 * x) by (rewrite (HE0 13%nat 13%bv eq_refl), G13; apply unsigned_lit_small; clear - Hx; lia).
assert (U26 : bv_unsigned (ew E0 26) = p) by (rewrite (HE0 26%nat 26%bv eq_refl), G26; apply unsigned_lit_small; clear - Rp Hx Hcut Hlen; lia).
assert (E25 : ew E0 25 = w64 SB) by (rewrite (HE0 25%nat 25%bv eq_refl); exact G25).
assert (E32 : ew E0 32 = Z_to_bv 64 (getz palc (3 * x + cut))) by (pose proof (HV 0%nat _ eq_refl) as X; cbn [Nat.add] in X; exact X).
assert (A32 : bv_unsigned (ew E0 32) = getz palc (3 * x + cut)) by (rewrite E32; apply unsigned_lit_small; clear - Hbr; lia).
assert (A33 : bv_unsigned (ew E0 33) = p + 3 * x + cut).
{ pose proof (HV 1%nat _ eq_refl) as X. cbn [Nat.add] in X. rewrite X. apply unsigned_lit_small. clear - Rp Hx Hcut Hlen. lia. }
assert (DN : forall n v, bv_unsigned (ew E0 n) = v -> sv_denot E0 (SOff n 0) = Z_to_bv 64 v).
{ intros n v Hn. cbn [sv_denot]. rewrite Hn, Z.add_0_r. reflexivity. }
assert (HS0 : @st_ok trasegs fy E0 ss_LCDx (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LCD_HEAD) mem (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LCDx. apply (entry_st_ok_full trasegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold lcr_mem. apply Forall_cons; [|apply Forall_nil].
unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
change (Ereg regs _) with E0. rewrite A33.
split; [clear - Rp Hx Hcut; lia|]. split; [clear - Rp Hx Hcut Hlen; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trasegs E0 _ (p + 3 * x + cut) 0 1 _ (getz palc (3 * x + cut))); [exact (DN _ _ A32) | zside | zside |].
apply (val_mem_byte trasegs); [rewrite Z.add_0_r; replace (p + 3 * x + cut) with (p + (3 * x + cut)) by lia; exact Hbyte | exact Hbr].
- apply pairwise_disjoint_of_extents. unfold lcr_mem, extent_of_region. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; [exact I|]].
+ cbn [lcd_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (Ereg regs _) with E0.
rewrite U11, U13, U26, E25, A32, A33. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - Hx Hcut Hlen Rp Hbr. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
+ cbn [lcd_facts f_alias alias_ok]. change (Ereg regs _) with E0. split; [|exact I].
unfold lcd_alias. apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U11, U13, U26, A33, !Z.add_0_r.
rewrite (zcanon_id cut), (zcanon_id (3 * x)), (zcanon_id p) by (unfold M64; clear - Rp Hx Hcut Hlen; lia).
rewrite (zcanon_id (cut + 3 * x)) by (unfold M64; clear - Hx Hcut; lia). f_equal. lia. }
assert (SHOK0 : sh_ok trasegs lcr_Bx lcr_SH E0 (mrestrict (w_H W) mem)).
{ unfold sh_ok, lcr_SH. constructor; [|constructor].
apply (shent_ok_of_range trasegs (w_H W) mem E0 lcr_Bx 33 (p + 3 * x + cut) 1 (p + 3 * x + cut) 0 1).
+ apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md pb pm _ _ HAR HinP); clear - Hx Hcut Hlen HP0 HP1 Qpm; lia.
+ unfold U, lcr_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A33.
+ lia.
+ lia.
+ intros z Hz. destruct (al_blocks _ _ LAWS _ _ _ _ _ pb pm HAR HinP) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ pb pm HAR HinP) as Himg.
revert Hz Hia Himg Hx Hcut Hlen HP0 HP1 Qpm Qpb0 Qpb1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia. }
split; [exact (st_ok_enterF trasegs fy 64 E0 ss_LCDx _ HS0 ltac:(vm_compute; reflexivity) Hfrm)|].
split; [exact (sh_ok_agree trasegs lcr_Bx lcr_SH 64 E0 E _ (env_agree_ew_fregs E0 64 _) ltac:(vm_compute; reflexivity) SHOK0)|].
split; [exact HE|].
split; [rewrite HEE by lia; exact E32|].
split; [|rewrite HEE by lia; exact U13].
subst E. rewrite <- Hfa5. exact (ew_fregs_at E0 64 (@fp_regs fy) (15%bv : bv 5)).
Qed.
Lemma LCD_step : forall (fy : FPState) (regs : bvmap 5 word) mem md (y : Z),
0 <= y < 2 ^ 29 -> 3 * y + cut < zlen palc -> lcd_inv fy regs mem md y ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LCD_HEAD) mem (seg_rom trasegs)) md)
(fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 (if ptest palc cut s m y then LCD_EXIT else LCD_HEAD)) mem' (seg_rom trasegs)) md' /\
(if ptest palc cut s m y then lcd_exit fy' regs' mem' md' y else lcd_inv fy' regs' mem' md' (y - 1)) /\
(forall r : bv 5, In r LCD_KEEP -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros fy regs mem md x Hx Hlen HI.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HI as (HB & G13 & G21).
pose proof (lcr_env fy regs mem md HB) as (Qpb0 & Qpb1 & Qpm & C1).
pose proof HB as (HJ & Hfrm & Hfa5 & Hpa & G11 & G26 & G25).
assert (Rp : 4096 <= p /\ p + zlen palc <= 140737479966720) by (clear - HP0 HP1 Qpb0 Qpb1 Qpm C1; lia).
destruct (arr8_getz trasegs _ p palc (3 * x + cut) Hpa ltac:(clear - Hx Hcut Hlen; lia)) as [_ Hbr].
destruct (LCD_seed fy regs mem md x Hx Hlen HI) as (HS & SHOK & HE & HE32 & HE79 & HU13).
set (E := ew_fregs _ 64 _) in HS, SHOK, HE, HE32, HE79, HU13.
aj_run_to_tokF tratbl_lib_ok HS HJ SHOK lcr_Bspan LCD_BR.
{ cbn [ss_mem]. unfold lcr_mem. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr1; rename HG into HG1; clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msA := msx) in * end.
assert (KW1 : forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) (ms_mem msA) a = aview trasegs (w_H W) mem a).
{ exact (lg_kept_ro _ _ _ _ _ HFr1 lcr_rs_ro). }
assert (FIN : forall (fz : FPState) E' ss' ms' md' pc', @st_ok trasegs fz E' ss' (restrict (w_H W) ms') -> env_agree 96 E E' ->
ss_pc ss' = pc' -> ss_resv ss' = None ->
sr_get (ss_regs ss') 13 = SOff 13 (-3) -> sr_get (ss_regs ss') 21 = SAluw ALU_ADD (SOff 21 0) (SLit (-1)) -> sr_get (ss_regs ss') 10 = lcd_cond ->
forallb (fun rr : bv 5 => sv_eqb (sr_get (ss_regs ss') rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) LCD_KEEP = true ->
frm_zero (@fp_csr fz) -> reg_get (@fp_regs fz) (15%bv : bv 5) = Z_to_bv 64 mean ->
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') md' k ->
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) (ms_mem ms') a = aview trasegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms') a) ->
SRr trasegs W (mkCfg ms' md')
(fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md'',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 pc') mem' (seg_rom trasegs)) md'' /\
lcr_base fy' regs' mem' md'' /\ getr regs' 13 = Z_to_bv 64 (3 * x - 3) /\ getr regs' 21 = w64 x /\
getr regs' 10 = (if ptest palc cut s m x then Sem.w0 else Sem.w1) /\
(forall r : bv 5, In r LCD_KEEP -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a))).
{ intros fz E' ss' ms' md' pc' HS' [EA ED] Hpc' Hrv' Q13 Q21 Q10 QK Hfz Hfz5 HJ' Hk' Hp'.
assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) [getz palc (3 * x + cut); p + 3 * x + cut] ++ [])) E').
{ split; [intros n Hn; rewrite EA by lia; subst E; rewrite ew_fregs_low by lia; reflexivity | rewrite ED; reflexivity]. }
pose proof (regs_kept_of_st_ok trasegs E' ss' _ regs _ LCD_KEEP HS' HAE' QK) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trasegs (w_H W) E' ss' ms' HS' Hrv'), Hpc'. apply SRr_ret.
split; [reflexivity|]. exists fz, (ms_regs ms'), (ms_mem ms'), md'. split; [reflexivity|].
split.
{ split; [exact HJ'|]. split; [exact Hfz|]. split; [exact Hfz5|].
split; [exact (arr8_kept mem (ms_mem ms') Hpa Hk' (proj1 Rp) (proj2 Rp))|].
split; [rewrite (HKR (11%bv : bv 5) ltac:(cbv; tauto)); exact G11|].
split; [rewrite (HKR (26%bv : bv 5) ltac:(cbv; tauto)); exact G26|].
rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)). exact G25. }
split; [rewrite (st_ok_restrict_reg trasegs (w_H W) E' ss' ms' (13%bv : bv 5) HS'), Q13; cbn [sv_denot]; rewrite EA, HU13 by lia; f_equal; lia|].
split.
{ rewrite (st_ok_restrict_reg trasegs (w_H W) E' ss' ms' (21%bv : bv 5) HS'), Q21.
apply lg_subw1_succ; [cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, EA by lia; rewrite (HE 21%nat 21%bv eq_refl); exact G21 | clear - Hx; lia]. }
split.
{ rewrite (st_ok_restrict_reg trasegs (w_H W) E' ss' ms' (10%bv : bv 5) HS'), Q10. unfold lcd_cond. cbn [sv_denot].
rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned, !EA by lia.
rewrite (lg_flt_cvt_test RNE _ _ (getz palc (3 * x + cut)) mean s m HE32 HE79 Hbr Hmean Hq). reflexivity. }
split; [exact HKR|]. split; [exact Hk' | exact Hp']. }
assert (HAE96 : env_agree 96 E E) by (apply env_agree_refl).
lg_branchF tratbl_lib_ok HS.
-
lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
assert (Ht : ptest palc cut s m x = false).
{ cbn [sv_denot] in Hc. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned, !(proj1 HAEx) in Hc by lia.
rewrite (lg_flt_cvt_test RNE _ _ (getz palc (3 * x + cut)) mean s m HE32 HE79 Hbr Hmean Hq) in Hc.
rewrite lg_bne_bool_w_neg in Hc. apply Bool.negb_true_iff in Hc. exact Hc. }
rewrite Ht.
pose proof (st_okF_frm trasegs _ _ _ HS) as Hfrm'. pose proof (st_okF_freg trasegs _ _ _ (15%bv : bv 5) HS) as Hf5'.
lazymatch type of Hf5' with _ = sv_denot ?Ex (sfr_get ?fr ?r) => let v := eval vm_compute in (sfr_get fr r) in change (sfr_get fr r) with v in Hf5' end.
cbn [sv_denot] in Hf5'. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (proj1 HAEx), HE79 in Hf5' by lia.
pose proof (st_okF_to_legacy trasegs _ _ _ HS) as HSL. clear HS.
aj_run_to_tok tratbl_lib_ok HSL HJ SHOK lcr_Bspan LCD_HEAD.
{ apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HSL with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 96 E Ey) by (env_agree_chain HAEx) end.
eapply SRr_mono.
{ apply (FIN _ _ _ _ _ LCD_HEAD HSL HAEy); [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | exact Hfrm' | | exact HJ | | ].
+ exact Hf5'.
+ intros a Ha. rewrite (lg_kept_ro _ _ _ _ _ HFr lcr_rs_ro a Ha). exact (KW1 a Ha).
+ intros a Ha. apply (apresent_grows _ _ _ _ HG). apply (apresent_grows _ _ _ _ HG1). exact Ha. }
cbv beta. intros W' c' _ (HW' & fy' & regs' & mem' & md' & Hc' & HB' & R13 & R21 & R10 & HK' & Hk' & Hp').
split; [exact HW'|]. exists fy', regs', mem', md'. split; [exact Hc'|].
split; [split; [exact HB'|]; split; [rewrite R13; unfold w64; f_equal; lia | rewrite R21; unfold w64; f_equal; lia]|].
split; [exact HK'|]. split; [exact Hk' | exact Hp'].
-
lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
assert (Ht : ptest palc cut s m x = true).
{ cbn [sv_denot] in Hc. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned, !(proj1 HAEx) in Hc by lia.
rewrite (lg_flt_cvt_test RNE _ _ (getz palc (3 * x + cut)) mean s m HE32 HE79 Hbr Hmean Hq) in Hc.
rewrite lg_bne_bool_w_neg in Hc. apply Bool.negb_false_iff in Hc. exact Hc. }
rewrite Ht.
pose proof (st_okF_frm trasegs _ _ _ HS) as Hfrm'. pose proof (st_okF_freg trasegs _ _ _ (15%bv : bv 5) HS) as Hf5'.
lazymatch type of Hf5' with _ = sv_denot ?Ex (sfr_get ?fr ?r) => let v := eval vm_compute in (sfr_get fr r) in change (sfr_get fr r) with v in Hf5' end.
cbn [sv_denot] in Hf5'. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (proj1 HAEx), HE79 in Hf5' by lia.
pose proof (st_okF_to_legacy trasegs _ _ _ HS) as HSL. clear HS.
aj_run_to_tok tratbl_lib_ok HSL HJ SHOK lcr_Bspan LCD_EXIT.
{ apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HSL with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 96 E Ey) by (env_agree_chain HAEx) end.
eapply SRr_mono.
{ apply (FIN _ _ _ _ _ LCD_EXIT HSL HAEy); [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | exact Hfrm' | | exact HJ | | ].
+ exact Hf5'.
+ intros a Ha. rewrite (lg_kept_ro _ _ _ _ _ HFr lcr_rs_ro a Ha). exact (KW1 a Ha).
+ intros a Ha. apply (apresent_grows _ _ _ _ HG). apply (apresent_grows _ _ _ _ HG1). exact Ha. }
cbv beta. intros W' c' _ (HW' & fy' & regs' & mem' & md' & Hc' & HB' & R13 & R21 & R10 & HK' & Hk' & Hp').
split; [exact HW'|]. exists fy', regs', mem', md'. split; [exact Hc'|].
split; [split; [exact HB'|]; split; [exact R13|]; split; [exact R21 | rewrite R10, Ht; reflexivity]|].
split; [exact HK'|]. split; [exact Hk' | exact Hp'].
Qed.
Definition LCD_post (regs : bvmap 5 word) (mem : word -> option byte) (k1 : Z) : world trasegs -> config -> Prop :=
fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 LCD_EXIT) mem' (seg_rom trasegs)) md' /\
lcd_exit fy' regs' mem' md' k1 /\
(forall r : bv 5, In r LCD_KEEP -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Lemma LCD_last : forall (fy : FPState) (regs : bvmap 5 word) mem md (k1 : Z),
0 <= k1 < 2 ^ 29 -> 3 * k1 + cut < zlen palc -> ptest palc cut s m k1 = true -> lcd_inv fy regs mem md k1 ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LCD_HEAD) mem (seg_rom trasegs)) md) (LCD_post regs mem k1).
Proof.
intros fy regs mem md k1 Hk1 Hlen Hbig HI.
eapply SRr_mono; [exact (LCD_step fy regs mem md k1 Hk1 Hlen HI)|].
cbv beta. rewrite Hbig. intros W' c' _ H. exact H.
Qed.
Lemma LCD_loop : forall (n : nat) (fy : FPState) (regs : bvmap 5 word) mem md (y k1 : Z),
y - k1 <= Z.of_nat n -> 0 <= k1 <= y -> y < 2 ^ 29 -> 3 * y + cut < zlen palc ->
(forall z, k1 < z <= y -> ptest palc cut s m z = false) -> ptest palc cut s m k1 = true ->
lcd_inv fy regs mem md y ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LCD_HEAD) mem (seg_rom trasegs)) md) (LCD_post regs mem k1).
Proof.
induction n as [|n IH]; intros fy regs mem md y k1 Hn Hy Hy1 Hlen Hsm Hbig HI.
- assert (y = k1) by lia. subst y. exact (LCD_last fy regs mem md k1 ltac:(lia) Hlen Hbig HI).
- destruct (Z.eq_dec y k1) as [-> | Hne]; [exact (LCD_last fy regs mem md k1 ltac:(lia) Hlen Hbig HI)|].
eapply SRr_bind; [exact (LCD_step fy regs mem md y ltac:(lia) Hlen HI)|].
cbv beta. rewrite (Hsm y ltac:(lia)). intros W' c' _ (-> & fy' & regs' & mem' & md' & -> & HI' & Hk' & Hm' & Hp').
eapply SRr_mono; [exact (IH fy' regs' mem' md' (y - 1) k1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros z Hz; apply Hsm; lia) Hbig HI')|].
cbv beta. intros W'' c'' _ (HW & fy'' & regs'' & mem'' & md'' & Hc & HX'' & Hk'' & Hm'' & Hp'').
split; [exact HW|]. exists fy'', regs'', mem'', md''. split; [exact Hc|]. split; [exact HX''|].
split; [intros r Hr; rewrite (Hk'' r Hr); apply Hk'; exact Hr|].
split; [intros a Ha; rewrite (Hm'' a Ha); apply Hm'; exact Ha|].
intros a Ha. apply Hp''. apply Hp'. exact Ha.
Qed.
End b.
Lemma rga_lcr_up {rc : YN05.RunCeil} : forall (B : asyms), AR_laws trasegs B ->
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W pb pm p palc cut mean s m x i1 (fy : FPState) (regs : bvmap 5 word) memc mdc,
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
frm_zero (@fp_csr fy) -> reg_get (@fp_regs fy) (15%bv : bv 5) = Z_to_bv 64 mean -> 0 <= mean < 2 ^ 64 -> is_quot mean m s ->
In (pb, pm) (ablocks B lyc Sc) -> pb <= p -> p + zlen palc <= pb + pm ->
arr8 trasegs (mrestrict (w_H W) memc) p palc ->
0 <= cut <= 2 -> 0 <= x <= i1 -> i1 < 2 ^ 29 -> 3 * i1 + cut < zlen palc ->
(forall z, x <= z < i1 -> ptest palc cut s m z = true) -> ptest palc cut s m i1 = false ->
getr regs 11 = w64 cut -> getr regs 12 = w64 (3 * x) -> getr regs 23 = Z_to_bv 64 (x - 1) -> getr regs 26 = w64 p -> getr regs 25 = w64 SB ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LCU_HEAD) memc (seg_rom trasegs)) mdc)
(fun W2 c2 => W2 = W /\ exists (fy' : FPState) regs2 mem2 md2,
c2 = mkCfg (@mkst fy' regs2 (Z_to_bv 64 LCU_EXIT) mem2 (seg_rom trasegs)) md2 /\
frm_zero (@fp_csr fy') /\ reg_get (@fp_regs fy') (15%bv : bv 5) = Z_to_bv 64 mean /\
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
(forall r : bv 5, reg_in r LCU_CLOB = false -> getr regs2 r = getr regs r) /\
getr regs2 12 = w64 (3 * i1 + 3) /\ getr regs2 23 = w64 i1 /\ getr regs2 10 = w64 0 /\
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) mem2 a = aview trasegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a)).
Proof.
intros B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W pb pm p palc cut mean s m x i1 fy regs memc mdc
HJ Hfrm Hfa5 Hmean Hq HinP HP0 HP1 Hpa Hcut Hx Hi1 Hlen Hsm Hbig G11 G12 G23 G26 G25.
assert (HI : lcu_inv B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W p palc cut mean fy regs memc mdc x).
{ split; [|split; assumption]. repeat (split; [assumption|]). assumption. }
eapply SRr_mono; [exact (LCU_loop B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W pb pm p palc cut mean s m HinP HP0 HP1 Hcut Hmean Hq
(Z.to_nat (i1 - x)) fy regs memc mdc x i1 ltac:(lia) Hx Hi1 Hlen Hsm Hbig HI)|].
cbv beta. intros W2 c2 _ (HW & fy' & regs2 & mem2 & md2 & Hc & ((HJ2 & Hfrm2 & Hfa52 & _ & _ & _ & _) & R12 & R23 & R10) & Hk & Hm & Hp).
split; [exact HW|]. exists fy', regs2, mem2, md2. split; [exact Hc|]. split; [exact Hfrm2|]. split; [exact Hfa52|]. split; [exact HJ2|].
split.
{ intros r Hr. destruct (lcu_clob_cases r Hr) as [-> | Hin]; [|exact (Hk r Hin)]. rewrite !getr_zero. reflexivity. }
split; [exact R12|]. split; [exact R23|]. split; [exact R10|]. split; [exact Hm | exact Hp].
Qed.
Lemma rga_lcr_down {rc : YN05.RunCeil} : forall (B : asyms), AR_laws trasegs B ->
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W pb pm p palc cut mean s m y k1 (fy : FPState) (regs : bvmap 5 word) memc mdc,
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
frm_zero (@fp_csr fy) -> reg_get (@fp_regs fy) (15%bv : bv 5) = Z_to_bv 64 mean -> 0 <= mean < 2 ^ 64 -> is_quot mean m s ->
In (pb, pm) (ablocks B lyc Sc) -> pb <= p -> p + zlen palc <= pb + pm ->
arr8 trasegs (mrestrict (w_H W) memc) p palc ->
0 <= cut <= 2 -> 0 <= k1 <= y -> y < 2 ^ 29 -> 3 * y + cut < zlen palc ->
(forall z, k1 < z <= y -> ptest palc cut s m z = false) -> ptest palc cut s m k1 = true ->
getr regs 11 = w64 cut -> getr regs 13 = w64 (3 * y) -> getr regs 21 = w64 (y + 1) -> getr regs 26 = w64 p -> getr regs 25 = w64 SB ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LCD_HEAD) memc (seg_rom trasegs)) mdc)
(fun W2 c2 => W2 = W /\ exists (fy' : FPState) regs2 mem2 md2,
c2 = mkCfg (@mkst fy' regs2 (Z_to_bv 64 LCD_EXIT) mem2 (seg_rom trasegs)) md2 /\
frm_zero (@fp_csr fy') /\ reg_get (@fp_regs fy') (15%bv : bv 5) = Z_to_bv 64 mean /\
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
(forall r : bv 5, reg_in r LCD_CLOB = false -> getr regs2 r = getr regs r) /\
getr regs2 13 = Z_to_bv 64 (3 * k1 - 3) /\ getr regs2 21 = w64 k1 /\ getr regs2 10 = w64 0 /\
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) mem2 a = aview trasegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a)).
Proof.
intros B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W pb pm p palc cut mean s m y k1 fy regs memc mdc
HJ Hfrm Hfa5 Hmean Hq HinP HP0 HP1 Hpa Hcut Hy Hy1 Hlen Hsm Hbig G11 G13 G21 G26 G25.
assert (HI : lcd_inv B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W p palc cut mean fy regs memc mdc y).
{ split; [|split; assumption]. repeat (split; [assumption|]). assumption. }
eapply SRr_mono; [exact (LCD_loop B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W pb pm p palc cut mean s m HinP HP0 HP1 Hcut Hmean Hq
(Z.to_nat (y - k1)) fy regs memc mdc y k1 ltac:(lia) Hy Hy1 Hlen Hsm Hbig HI)|].
cbv beta. intros W2 c2 _ (HW & fy' & regs2 & mem2 & md2 & Hc & ((HJ2 & Hfrm2 & Hfa52 & _ & _ & _ & _) & R13 & R21 & R10) & Hk & Hm & Hp).
split; [exact HW|]. exists fy', regs2, mem2, md2. split; [exact Hc|]. split; [exact Hfrm2|]. split; [exact Hfa52|]. split; [exact HJ2|].
split.
{ intros r Hr. destruct (lcd_clob_cases r Hr) as [-> | Hin]; [|exact (Hk r Hin)]. rewrite !getr_zero. reflexivity. }
split; [exact R13|]. split; [exact R21|]. split; [exact R10|]. split; [exact Hm | exact Hp].
Qed.
