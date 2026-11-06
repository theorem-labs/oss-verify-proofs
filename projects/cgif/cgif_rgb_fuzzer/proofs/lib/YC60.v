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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2u YC1b YC20.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI0g YI0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC68.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition LDC_HEAD : Z := 0x83c80.
Definition LDC_BR : Z := 0x83cd4.
Definition LDC_EXIT : Z := 0x83cec.
Definition LDC_CLOB : list (bv 5) := [6; 12; 20; 21; 22; 23]%bv.
Definition LDC_KEEP : list (bv 5) := [1; 2; 3; 4; 5; 7; 8; 9; 10; 11; 13; 14; 15; 16; 17; 18; 19; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LDC_FKEEP : list (bv 5) := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma ldc_clob_cases : forall r : bv 5, reg_in r LDC_CLOB = false -> r = 0%bv \/ In r LDC_KEEP.
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
Variables (flt nF : Z).
Hypothesis HinF : In (flt, nF) (ablocks B lyc Sc).
Hypothesis HFW : forall blc lyq ownq i, In (flt, nF) blc -> 0 <= i < req_size nF ->
awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (flt + i).
Definition ldc_inv (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (c idx : Z) : Prop :=
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k /\
frm_zero (@fp_csr fy) /\
getr regs 20 = w64 c /\ getr regs 21 = w64 idx /\ getr regs 31 = w64 flt /\ getr regs 25 = w64 SB.
Lemma ldc_env : forall fy regs mem md c idx, ldc_inv fy regs mem md c idx ->
4096 <= flt /\ flt + req_size nF <= alloc_ceiling /\ flt mod 16 = 0 /\ nF <= req_size nF /\
140735332483072 <= alloc_ceiling <= 140737479966720.
Proof.
intros fy regs mem md c idx (HJ & _). pose proof HJ as (HAR & _). pose proof asan_consts as (C1 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (Hf16 & Hf4096 & Hfceil & _ & _ & _ & Hnf0).
pose proof (req_size_pos nF ltac:(lia)) as [_ HrF]. repeat split; try assumption; lia.
Qed.
Definition ldc_alias : sv := SAlu ALU_ADD (SAlu ALU_SLL (SOff 21 0) (SLit 2)) (SOff 31 0).
Definition ldc_mem : smem := [ YQ0b.mkRegion (Some 33%nat) 0 4 0 4 [YQ0b.mkChunk 0 (CVal 4 (SOff 32 0))] ].
Definition ldc_facts : facts :=
mkFacts [ (20%nat, mkAF 1 3 0); (21%nat, mkAF 0 (2^30) 0); (31%nat, mkAF 4096 140737479966720 4);
(25%nat, mkAF SB SB 0); (32%nat, mkAF 0 (2^32 - 1) 0); (33%nat, mkAF 4096 140737479966720 2) ] [] [ (ldc_alias, SOff 33 0) ].
Definition ss_LDCx : sstate := mkSS LDC_HEAD sr_atoms ldc_mem None ldc_facts.
Definition ldc_Bx : sv := SOff 25 0.
Definition ldc_SH : list shent := [ mkSHE 33 0 4 ].
Definition ldc_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition ldc_le (n : nat) : sv := SF2 (FP2_cmp F_LE FMT_S) (SF1 FP1_nanbox (SOff 32 0)) (SOff n 0).
Definition ldc_c1 : sv := SAlu ALU_AND (ldc_le 79) (ldc_le 78).
Definition ldc_c2 : sv := SAlu ALU_OR (ldc_le 79) (SAlu ALU_XOR (ldc_le 78) (SLit 1)).
Lemma LDC_seed : forall (fy : FPState) (regs : bvmap 5 word) mem md (c idx v : Z),
1 <= c <= 3 -> 0 <= idx < 2 ^ 30 -> 4 * idx + 4 <= nF -> ldc_inv fy regs mem md c idx ->
val_mem trasegs (mrestrict (w_H W) mem) (flt + 4 * idx) 4 v -> 0 <= v < 2 ^ 32 ->
let E0 := Ereg regs (map (Z_to_bv 64) [v; flt + 4 * idx] ++ []) in
let E := ew_fregs E0 64 (@fp_regs fy) in
st_okF trasegs E (mkSST LDC_HEAD sr_atoms (sfr_atoms 64) ldc_mem None ldc_facts)
(restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LDC_HEAD) mem (seg_rom trasegs))) /\
sh_ok trasegs ldc_Bx ldc_SH E (mrestrict (w_H W) mem) /\
(forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) /\
(forall r : bv 5, ew E (64 + ridx r)%nat = reg_get (@fp_regs fy) r) /\
bv_unsigned (ew E 20) = c /\ bv_unsigned (ew E 21) = idx /\ bv_unsigned (ew E 33) = flt + 4 * idx.
Proof.
intros fy regs mem md c idx v Hc Hidx Hlen HI Vcell Hv E0 E.
pose proof (ldc_env fy regs mem md c idx HI) as (Qf0 & Qf1 & Qf16 & QnF & C1).
pose proof HI as (HJ & Hfrm & G20 & G21 & G31 & G25).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (_ & _ & _ & _ & Hfpres & _).
assert (HE0 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E0 n = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall i x, nth_error [v; flt + 4 * idx] i = Some x -> ew E0 (32 + i) = Z_to_bv 64 x) by (intros i x Hi; subst E0; apply Ereg_vals; exact Hi).
assert (HEE : forall n, (n < 64)%nat -> ew E n = ew E0 n) by (intros n Hn; subst E; apply ew_fregs_low; exact Hn).
assert (HE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5. rewrite HEE by lia. apply HE0. exact Hn. }
assert (U20 : bv_unsigned (ew E0 20) = c) by (rewrite (HE0 20%nat 20%bv eq_refl), G20; apply unsigned_lit_small; clear - Hc; lia).
assert (U21 : bv_unsigned (ew E0 21) = idx) by (rewrite (HE0 21%nat 21%bv eq_refl), G21; apply unsigned_lit_small; clear - Hidx; lia).
assert (U31 : bv_unsigned (ew E0 31) = flt) by (rewrite (HE0 31%nat 31%bv eq_refl), G31; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Hidx Hlen; lia).
assert (E25 : ew E0 25 = w64 SB) by (rewrite (HE0 25%nat 25%bv eq_refl); exact G25).
assert (A32 : bv_unsigned (ew E0 32) = v).
{ pose proof (HV 0%nat _ eq_refl) as X. cbn [Nat.add] in X. rewrite X. apply unsigned_lit_small. clear - Hv. lia. }
assert (A33 : bv_unsigned (ew E0 33) = flt + 4 * idx).
{ pose proof (HV 1%nat _ eq_refl) as X. cbn [Nat.add] in X. rewrite X. apply unsigned_lit_small. clear - Qf0 Qf1 QnF C1 Hidx Hlen. lia. }
assert (DN : forall n x, bv_unsigned (ew E0 n) = x -> sv_denot E0 (SOff n 0) = Z_to_bv 64 x).
{ intros n x Hn. cbn [sv_denot]. rewrite Hn, Z.add_0_r. reflexivity. }
assert (Hf4 : (flt + 4 * idx) mod 4 = 0).
{ replace (flt + 4 * idx) with (flt + idx * 4) by lia. rewrite Z.mod_add by lia.
clear - Qf16. pose proof (Z.mod_pos_bound flt 16 ltac:(lia)). pose proof (Z.div_mod flt 16 ltac:(lia)).
replace flt with (4 * (4 * (flt / 16))) by lia. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
assert (HS0 : @st_ok trasegs fy E0 ss_LDCx (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LDC_HEAD) mem (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LDCx. apply (entry_st_ok_full trasegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold ldc_mem. apply Forall_cons; [|apply Forall_nil].
unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
change (Ereg regs _) with E0. rewrite A33.
split; [clear - Qf0 Hidx; lia|]. split; [clear - Qf1 QnF C1 Hidx Hlen; lia|]. split.
{ intros o Ho. apply (apresent_writable trasegs). apply (proj1 (Hfpres (flt + 4 * idx + o) ltac:(clear - Ho Hidx Hlen QnF; lia))). }
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trasegs E0 _ (flt + 4 * idx) 0 4 _ v); [exact (DN _ _ A32) | zside | zside | rewrite Z.add_0_r; exact Vcell].
- apply pairwise_disjoint_of_extents. unfold ldc_mem, extent_of_region. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; [exact I|]].
+ cbn [ldc_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (Ereg regs _) with E0.
rewrite U20, U21, U31, E25, A32, A33. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - Hc Hidx Hlen Qf0 Qf1 Qf16 QnF C1 Hv Hf4. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
+ cbn [ldc_facts f_alias alias_ok]. change (Ereg regs _) with E0. split; [|exact I].
unfold ldc_alias. apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, U21, U31, A33, !Z.add_0_r.
rewrite (zcanon_id flt), (zcanon_id idx) by (unfold M64; clear - Qf0 Qf1 QnF C1 Hidx Hlen; lia). change (Z.land (zcanon 2) 63) with 2.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite (zcanon_id (idx * 4)) by (unfold M64; clear - Hidx; lia).
f_equal. lia. }
assert (SHOK0 : sh_ok trasegs ldc_Bx ldc_SH E0 (mrestrict (w_H W) mem)).
{ unfold sh_ok, ldc_SH. constructor; [|constructor].
apply (shent_ok_of_range trasegs (w_H W) mem E0 ldc_Bx 33 (flt + 4 * idx) 4 (flt + 4 * idx) 0 4).
+ apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md flt nF _ _ HAR HinF); clear - Hidx Hlen QnF; lia.
+ unfold U, ldc_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A33.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ flt nF HAR HinF) as Himg.
revert Hy Hia Himg Hidx Hlen QnF Qf0 Qf1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia. }
split; [exact (st_ok_enterF trasegs fy 64 E0 ss_LDCx _ HS0 ltac:(vm_compute; reflexivity) Hfrm)|].
split; [exact (sh_ok_agree trasegs ldc_Bx ldc_SH 64 E0 E _ (env_agree_ew_fregs E0 64 _) ltac:(vm_compute; reflexivity) SHOK0)|].
split; [exact HE|].
split; [intros r; subst E; apply ew_fregs_at|].
rewrite !HEE by lia. repeat split; assumption.
Qed.

Local Ltac ldc_rs_tac :=
let rr := fresh "rr" in let Hin := fresh "Hin" in
intros rr Hin; cbn [ss_mem add_cond In] in Hin;
repeat (destruct Hin as [<- | Hin]); try contradiction;
first [ left; cbn [YQ0b.r_wlo YQ0b.r_whi]; lia
| right; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; repeat split; first [reflexivity | lia] ].
Definition LDC_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (pc c idx lo : Z) : world trasegs -> config -> Prop :=
fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 pc) mem' (seg_rom trasegs)) md' /\
ldc_inv fy' regs' mem' md' c idx /\
(forall r : bv 5, In r LDC_KEEP -> getr regs' r = getr regs r) /\
(forall r : bv 5, In r LDC_FKEEP -> reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (flt + 4 * lo <= a < flt + 4 * idx) -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Lemma LDC_step : forall (fy : FPState) (regs : bvmap 5 word) mem md (c idx : Z),
1 <= c <= 3 -> 0 <= idx < 2 ^ 30 -> 4 * idx + 4 <= nF -> ldc_inv fy regs mem md c idx ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDC_HEAD) mem (seg_rom trasegs)) md)
(LDC_post fy regs mem (if c =? 1 then LDC_EXIT else LDC_HEAD) (c - 1) (idx + 1) idx).
Proof.
intros fy regs mem md c idx Hc0 Hidx Hlen HI.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof (ldc_env fy regs mem md c idx HI) as (Qf0 & Qf1 & Qf16 & QnF & C1).
pose proof HI as (HJ & Hfrm & G20 & G21 & G31 & G25).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (_ & _ & _ & _ & Hfpres & _).
destruct (val_mem_of_present4 trasegs (mrestrict (w_H W) mem) (flt + 4 * idx)) as (v & Hv & Vcell).
{ intros i Hi. destruct (proj1 (Hfpres (flt + 4 * idx + i) ltac:(clear - Hi Hidx Hlen QnF; lia))) as (Hhid & bb & Hbb).
exists bb. unfold mbyte, mrestrict. rewrite Hhid, Hbb. reflexivity. }
destruct (LDC_seed fy regs mem md c idx v Hc0 Hidx Hlen HI Vcell Hv) as (HS & SHOK & HE & HEF & HU20 & HU21 & HU33).
set (E := ew_fregs _ 64 _) in HS, SHOK, HE, HEF, HU20, HU21, HU33.
assert (FIN : forall (fz : FPState) E' ss' ms' md' pc', @st_ok trasegs fz E' ss' (restrict (w_H W) ms') -> env_agree 96 E E' ->
ss_pc ss' = pc' -> ss_resv ss' = None ->
sr_get (ss_regs ss') 20 = SOff 20 (-1) -> sr_get (ss_regs ss') 21 = SOff 21 1 ->
forallb (fun rr : bv 5 => sv_eqb (sr_get (ss_regs ss') rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) LDC_KEEP = true ->
frm_zero (@fp_csr fz) -> (forall r : bv 5, In r LDC_FKEEP -> reg_get (@fp_regs fz) r = reg_get (@fp_regs fy) r) ->
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') md' k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (flt + 4 * idx <= a < flt + 4 * idx + 4) -> aview trasegs (w_H W) (ms_mem ms') a = aview trasegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms') a) ->
SRr trasegs W (mkCfg ms' md') (LDC_post fy regs mem pc' (c - 1) (idx + 1) idx)).
{ intros fz E' ss' ms' md' pc' HS' [EA ED] Hpc' Hrv' Q20 Q21 QK Hfz HfzK HJ' Hk' Hp'.
assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) [v; flt + 4 * idx] ++ [])) E').
{ split; [intros n Hn; rewrite EA by lia; subst E; rewrite ew_fregs_low by lia; reflexivity | rewrite ED; reflexivity]. }
pose proof (regs_kept_of_st_ok trasegs E' ss' _ regs _ LDC_KEEP HS' HAE' QK) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trasegs (w_H W) E' ss' ms' HS' Hrv'), Hpc'. apply SRr_ret.
split; [reflexivity|]. exists fz, (ms_regs ms'), (ms_mem ms'), md'. split; [reflexivity|].
split.
{ split; [exact HJ'|]. split; [exact Hfz|].
split; [rewrite (st_ok_restrict_reg trasegs (w_H W) E' ss' ms' (20%bv : bv 5) HS'), Q20; cbn [sv_denot]; rewrite EA, HU20 by lia; unfold w64; f_equal; lia|].
split; [rewrite (st_ok_restrict_reg trasegs (w_H W) E' ss' ms' (21%bv : bv 5) HS'), Q21; cbn [sv_denot]; rewrite EA, HU21 by lia; reflexivity|].
split; [rewrite (HKR (31%bv : bv 5) ltac:(cbv; tauto)); exact G31|].
rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)). exact G25. }
split; [exact HKR|]. split; [exact HfzK|].
split; [intros a Ha Hna; apply Hk'; [exact Ha | clear - Hna; lia] | exact Hp']. }
assert (HAE96 : env_agree 96 E E) by (apply env_agree_refl).
apply (st_okF_branch trasegs E _ _ _ BC_NE ldc_c1 (SLit 0) HS); clear HS; intros Hc1 HS;
(apply (st_okF_branch trasegs E _ _ _ BC_NE ldc_c2 (SLit 0) HS); clear HS; intros Hc2 HS).
all: unfold ldc_c1, ldc_c2, ldc_le in HS; cbn [neg_bc] in HS.
all: aj_run_to_tokF tratbl_lib_ok HS HJ SHOK ldc_Bspan LDC_BR;
[ cbn [ss_mem add_cond]; unfold ldc_mem; eapply awr_ok_cons_gen; [reflexivity | exact HU33 | | apply awr_ok_nil];
cbn [YQ0b.r_wlo YQ0b.r_whi]; intros a Ha; replace a with (flt + (a - flt)) by lia; apply HFW; [exact HinF | clear - Ha Hidx Hlen QnF; lia] | ].
all: rename HFr into HFr1; rename HG into HG1; clear HF.
all: lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msA := msx) in * end.
all: assert (KW1 : forall a, 0 <= a < 2 ^ 64 -> ~ (flt + 4 * idx <= a < flt + 4 * idx + 4) -> aview trasegs (w_H W) (ms_mem msA) a = aview trasegs (w_H W) mem a)
by (intros a Ha Hnw; apply (lg_kept_win _ _ _ _ _ 33%nat (flt + 4 * idx) 0 4 HFr1); [ldc_rs_tac | exact HU33 | exact Ha | clear - Hnw; lia]).
all: lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
all: lazymatch type of HS with st_okF _ ?Ex ?ssx ?msx =>
assert (HFK : forall r : bv 5, In r LDC_FKEEP -> reg_get (ms_fregs msx) r = reg_get (@fp_regs fy) r)
by (apply (st_okF_fregs_kept trasegs Ex ssx msx 64 (@fp_regs fy) LDC_FKEEP HS);
[ intros r; rewrite (proj1 HAEx) by (pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5; unfold ridx; lia); apply HEF
| vm_compute; reflexivity ]) end.
all: lg_branchF tratbl_lib_ok HS;
(rewrite branch_ne_U, U_SOff, U_SLit in Hc; rewrite !(proj1 HAEx) in Hc by lia; rewrite HU20, !zcanon_id in Hc by (unfold M64; clear - Hc0; lia));
[ apply Bool.negb_true_iff, Z.eqb_neq in Hc; replace (c =? 1) with false by (symmetry; apply Z.eqb_neq; clear - Hc; lia)
| apply Bool.negb_false_iff, Z.eqb_eq in Hc; replace (c =? 1) with true by (symmetry; apply Z.eqb_eq; clear - Hc; lia) ].
all: pose proof (st_okF_frm trasegs _ _ _ HS) as Hfrm'; pose proof (st_okF_to_legacy trasegs _ _ _ HS) as HSL; clear HS.
all: lazymatch type of HSL with st_ok _ ?Ex _ _ => assert (U33X : bv_unsigned (ew Ex 33) = flt + 4 * idx) by (rewrite (proj1 HAEx) by lia; exact HU33) end.
all: lazymatch goal with
| |- SRr _ _ _ (LDC_post _ _ _ LDC_HEAD _ _ _) => aj_run_to_tok tratbl_lib_ok HSL HJ SHOK ldc_Bspan LDC_HEAD
| |- SRr _ _ _ (LDC_post _ _ _ LDC_EXIT _ _ _) => aj_run_to_tok tratbl_lib_ok HSL HJ SHOK ldc_Bspan LDC_EXIT
end;
[ eapply awr_ok_cons_gen; [reflexivity | exact U33X | | apply awr_ok_nil];
cbn [YQ0b.r_wlo YQ0b.r_whi]; intros a Ha; replace a with (flt + (a - flt)) by lia; apply HFW; [exact HinF | clear - Ha Hidx Hlen QnF; lia] | ].
all: lazymatch type of HSL with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 96 E Ey) by (env_agree_chain HAEx) end.
all: apply (FIN _ _ _ _ _ _ HSL HAEy); [reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | exact Hfrm' | exact HFK | exact HJ | | ];
[ intros a Ha Hnw; rewrite (lg_kept_win _ _ _ _ _ 33%nat (flt + 4 * idx) 0 4 HFr ltac:(ldc_rs_tac) U33X a Ha ltac:(clear - Hnw; lia)); exact (KW1 a Ha Hnw)
| intros a Ha; apply (apresent_grows _ _ _ _ HG); apply (apresent_grows _ _ _ _ HG1); exact Ha ].
Qed.
Lemma LDC_loop : forall (n : nat) (fy : FPState) (regs : bvmap 5 word) mem md (c idx : Z),
Z.of_nat n = c - 1 -> 1 <= c <= 3 -> 0 <= idx -> idx + c <= 2 ^ 30 -> 4 * (idx + c) <= nF -> ldc_inv fy regs mem md c idx ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDC_HEAD) mem (seg_rom trasegs)) md) (LDC_post fy regs mem LDC_EXIT 0 (idx + c) idx).
Proof.
induction n as [|n IH]; intros fy regs mem md c idx Hn Hc Hidx Hmax Hlen HI.
- assert (c = 1) by lia. subst c.
eapply SRr_mono; [exact (LDC_step fy regs mem md 1 idx ltac:(lia) ltac:(lia) ltac:(lia) HI)|].
cbv beta. intros W' c' _ H. exact H.
- eapply SRr_bind; [exact (LDC_step fy regs mem md c idx Hc ltac:(lia) ltac:(lia) HI)|].
replace (c =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
intros W' c' _ (-> & fy' & regs' & mem' & md' & -> & HI' & Hk' & Hf' & Hm' & Hp').
eapply SRr_mono; [exact (IH fy' regs' mem' md' (c - 1) (idx + 1) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HI')|].
intros W'' c'' _ (HW & fy'' & regs'' & mem'' & md'' & Hc'' & HI'' & Hk'' & Hf'' & Hm'' & Hp'').
split; [exact HW|]. exists fy'', regs'', mem'', md''. split; [exact Hc''|].
split; [replace (idx + c) with (idx + 1 + (c - 1)) by lia; exact HI''|].
split; [intros r Hr; rewrite (Hk'' r Hr); apply Hk'; exact Hr|].
split; [intros r Hr; rewrite (Hf'' r Hr); apply Hf'; exact Hr|].
split; [intros a Ha Hna; rewrite (Hm'' a Ha ltac:(lia)); apply Hm'; [exact Ha | lia]|].
intros a Ha. apply Hp''. apply Hp'. exact Ha.
Qed.
End b.
Lemma rga_ldi_clamp {rc : YN05.RunCeil} : forall (B : asyms), AR_laws trasegs B ->
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF c idx (fy : FPState) (regs : bvmap 5 word) memc mdc,
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
frm_zero (@fp_csr fy) ->
In (flt, nF) (ablocks B lyc Sc) ->
(forall blc lyq ownq i, In (flt, nF) blc -> 0 <= i < req_size nF -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (flt + i)) ->
1 <= c <= 3 -> 0 <= idx -> idx + c <= 2 ^ 30 -> 4 * (idx + c) <= nF ->
getr regs 20 = w64 c -> getr regs 21 = w64 idx -> getr regs 31 = w64 flt -> getr regs 25 = w64 SB ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDC_HEAD) memc (seg_rom trasegs)) mdc)
(fun W2 c2 => W2 = W /\ exists (fy' : FPState) regs2 mem2 md2,
c2 = mkCfg (@mkst fy' regs2 (Z_to_bv 64 LDC_EXIT) mem2 (seg_rom trasegs)) md2 /\
frm_zero (@fp_csr fy') /\
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
(forall r : bv 5, reg_in r LDC_CLOB = false -> getr regs2 r = getr regs r) /\
(forall r : bv 5, In r LDC_FKEEP -> reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
getr regs2 20 = w64 0 /\ getr regs2 21 = w64 (idx + c) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (flt + 4 * idx <= a < flt + 4 * (idx + c)) -> aview trasegs (w_H W) mem2 a = aview trasegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a)).
Proof.
intros B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF c idx fy regs memc mdc
HJ Hfrm HinF HFW Hc Hidx Hmax Hlen G20 G21 G31 G25.
assert (HI : ldc_inv B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt fy regs memc mdc c idx).
{ repeat (split; [assumption|]). assumption. }
eapply SRr_mono; [exact (LDC_loop B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF HinF HFW
(Z.to_nat (c - 1)) fy regs memc mdc c idx ltac:(lia) Hc Hidx Hmax Hlen HI)|].
intros W2 c2 _ (HW & fy' & regs2 & mem2 & md2 & Hc2 & (HJ2 & Hfrm2 & R20 & R21 & _ & _) & Hk & Hf & Hm & Hp).
split; [exact HW|]. exists fy', regs2, mem2, md2. split; [exact Hc2|]. split; [exact Hfrm2|]. split; [exact HJ2|].
split.
{ intros r Hr. destruct (ldc_clob_cases r Hr) as [-> | Hin]; [|exact (Hk r Hin)]. rewrite !getr_zero. reflexivity. }
split; [exact Hf|]. split; [exact R20|]. split; [exact R21|]. split; [exact Hm | exact Hp].
Qed.
