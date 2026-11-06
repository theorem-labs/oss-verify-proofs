(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Reals.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YK0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02 YQ07 YQ08 YC03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG0u YG0d YCcz YCd2.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfx YCe9 YCey.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM00 YM04 YM01 YM02 YM03 YM06 YP14 YI08 YI0c YI0g YI0d YI0f YI09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCji YCj8.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCjo YCqj.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition LCP_HEAD : Z := 0x839b8.
Definition LCP_GLUE : Z := 0x83a48.
Lemma lcpg_U_off : forall E a b c y, U E a = c -> U E b = y -> 0 <= c <= 2 -> 0 <= y < 2 ^ 29 ->
U E (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL a (SLit 32)) (SMd M_MUL b (SLit 12884901888))) (SLit 32)) = c + 3 * y.
Proof.
intros E a b c y Ha Hb Hc Hy.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite Ha, Hb, !U_SLit.
change (Z.land (zcanon 32) 63) with 32. change (zcanon 12884901888) with (3 * 2 ^ 32). rewrite Z.shiftl_mul_pow2 by lia.
change (2 ^ 29) with 536870912 in Hy. change (2 ^ 32) with 4294967296.
rewrite (zcanon_id (c * 4294967296)) by (unfold M64; lia). rewrite (zcanon_id (y * (3 * 4294967296))) by (unfold M64; lia).
rewrite (zcanon_id (c * 4294967296 + y * (3 * 4294967296))) by (unfold M64; lia).
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 32) with 4294967296.
replace (c * 4294967296 + y * (3 * 4294967296)) with ((c + 3 * y) * 4294967296) by lia. rewrite Z.div_mul by lia.
apply zcanon_id. unfold M64. lia.
Qed.
Definition LCPG_KEEP : list (bv 5) := [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 13; 14; 15; 16; 17; 18; 19; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Section d.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trbsegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trbsegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)) (k : Z).
Variables (lyc : alayout) (Sc : astate) (W : world trbsegs).
Variables (kv cut p : Z).
Hypothesis Hkv : 0 <= kv < 2 ^ 29. Hypothesis Hcut : 0 <= cut <= 2. Hypothesis Hp : 0 <= p. Hypothesis Hroom : p + 3 * kv + cut < 2 ^ 64.
Definition lcpg_off : sv := SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff 12 0) (SLit 32)) (SMd M_MUL (SOff 21 0) (SLit 12884901888))) (SLit 32).
Definition ss_LCPG : sstate := mkSS LCP_GLUE sr_atoms [] None (mkFacts [] [ mkAC BC_GEU (SOff 23 0) lcpg_off ] []).
Definition lcpg_Bx : sv := SOff 27 0.
Definition lcpg_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Lemma LCPG_run : forall (fy : FPState) (regs : bvmap 5 word) mem md,
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
getr regs 21 = w64 kv -> getr regs 12 = w64 cut -> getr regs 23 = w64 (2 ^ 64 - 1 - p) ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LCP_GLUE) mem (seg_rom trbsegs)) md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (@mkst fy regs' (Z_to_bv 64 LCD_HEAD) mem' (seg_rom trbsegs)) md' /\
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k /\
getr regs' 20 = w64 (3 * kv) /\ getr regs' 10 = w64 (cut + 3 * kv) /\ getr regs' 12 = Z_to_bv 64 (cut - 3) /\
(forall r : bv 5, In r LCPG_KEEP -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros fy regs mem md HJ G21 G12 G23.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
set (E := Ereg regs (map (Z_to_bv 64) [] ++ [])).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (U12 : bv_unsigned (ew E 12) = cut) by (rewrite (HE0 12%nat 12%bv eq_refl), G12; apply unsigned_lit_small; clear - Hcut; lia).
assert (U21 : bv_unsigned (ew E 21) = kv) by (rewrite (HE0 21%nat 21%bv eq_refl), G21; apply unsigned_lit_small; clear - Hkv; lia).
assert (U23 : bv_unsigned (ew E 23) = 2 ^ 64 - 1 - p) by (rewrite (HE0 23%nat 23%bv eq_refl), G23; apply unsigned_lit_small; clear - Hp Hroom Hkv Hcut; lia).
assert (HS : @st_ok trbsegs fy E ss_LCPG (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LCP_GLUE) mem (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LCPG. apply (entry_st_ok_full trbsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
- split; [exact I | split; [split; [|exact I] | exact I]].
unfold acond_ok. cbn [ac_c ac_a ac_b]. change (Ereg regs _) with E. rewrite YO3v.branch_geu_U, U_SOff, U23, Z.add_0_r.
rewrite zcanon_id by (unfold M64; clear - Hp Hroom Hkv Hcut; lia).
unfold lcpg_off. rewrite (lcpg_U_off E (SOff 12 0) (SOff 21 0) cut kv) by first [rewrite U_SOff, ?U12, ?U21, Z.add_0_r; apply zcanon_id; unfold M64; clear - Hkv Hcut; lia | exact Hcut | exact Hkv].
apply Bool.negb_true_iff, Z.ltb_ge. clear - Hp Hroom Hkv Hcut. lia. }
assert (SHOK : sh_ok trbsegs lcpg_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
assert (HAE : env_agree 32 E E) by (apply env_agree_refl).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 LCP_GLUE) mem (seg_rom trbsegs))) in HJ, SHOK.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK lcpg_Bspan LCD_HEAD.
{ unfold ss_LCPG. cbn [ss_mem]. apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 32 E Ey) by (env_agree_chain HAE) end.
pose proof HAEy as [EA ED].
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regs _ LCPG_KEEP HS HAEy ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
assert (GR : forall (r : bv 5), getr (ms_regs ms) r = sv_denot _ (sr_get (ss_regs _) r)) by (intros r; exact (st_ok_restrict_reg trbsegs (w_H W) _ _ ms r HS)).
rewrite (st_ok_restrict_mkst trbsegs (w_H W) _ _ ms HS eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. exists (ms_regs ms), (ms_mem ms). eexists. split; [reflexivity|].
split; [exact HJ|].
split; [rewrite (GR (20%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
apply lg_denot_of_U; rewrite U_SMd; cbn [zmd_raw]; rewrite U_SOff, U_SLit; try rewrite EA by lia; rewrite U21, Z.add_0_r;
rewrite (zcanon_id kv) by (unfold M64; clear - Hkv; lia); change (zcanon 3) with 3; rewrite zcanon_id by (unfold M64; clear - Hkv; lia); clear; lia|].
split; [rewrite (GR (10%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
apply lg_denot_of_U;
apply (lcpg_U_off _ (SOff 12 0) (SOff 21 0) cut kv);
[ rewrite U_SOff; try rewrite EA by lia; rewrite U12, Z.add_0_r; apply zcanon_id; unfold M64; clear - Hcut; lia
| rewrite U_SOff; try rewrite EA by lia; rewrite U21, Z.add_0_r; apply zcanon_id; unfold M64; clear - Hkv; lia
| exact Hcut | exact Hkv ]|].
split; [rewrite (GR (12%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
cbn [sv_denot]; try rewrite EA by lia; rewrite U12; f_equal; clear; lia|].
split; [exact HKR|].
split; [exact (lg_kept_ro _ _ _ _ _ HFr ltac:(intros rr []))|].
intros a Ha. exact (apresent_grows _ _ _ _ HG Ha).
Qed.
End d.
Definition LCPH_KEEP : list (bv 5) := [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 16; 17; 18; 19; 20; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31]%bv.
Section e.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trbsegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trbsegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)) (k : Z).
Variables (lyc : alayout) (Sc : astate) (W : world trbsegs).
Variables (s1v node cut xv : Z).
Hypothesis Hs1lo : sp0 - STK <= s1v. Hypothesis Hs1hi : s1v + 416 <= sp0.
Hypothesis HinN : In (node, NODE_SIZE) (ablocks B lyc Sc).
Hypothesis Hcut : 0 <= cut <= 2. Hypothesis Hxv : 0 <= xv < 2 ^ 29.
Definition lcph_mem : smem := [ YQ0b.mkRegion (Some 9%nat) 408 416 0 0 [YQ0b.mkChunk 408 (CVal 8 (SOff 32 16))] ].
Definition lcph_facts : facts := mkFacts [ (9%nat, mkAF (2^46) (2^47) 0); (32%nat, mkAF 4096 140737479966720 4) ] [] [].
Definition ss_LCPH : sstate := mkSS LCP_HEAD sr_atoms lcph_mem None lcph_facts.
Definition lcph_Bx : sv := SOff 27 0.
Definition lcph_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Lemma lcph_rs_ro : forall rr, In rr lcph_mem -> YQ0b.r_whi rr <= YQ0b.r_wlo rr.
Proof. intros rr [<- | []]; cbn; lia. Qed.
Lemma LCPH_run : forall (fy : FPState) (regs : bvmap 5 word) mem md,
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
getr regs 9 = w64 s1v -> getr regs 12 = w64 cut -> getr regs 18 = w64 xv -> getr regs 24 = w64 (3 * xv) ->
val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 408) 8 (node + 16) ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LCP_HEAD) mem (seg_rom trbsegs)) md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (@mkst fy regs' (Z_to_bv 64 LCU_HEAD) mem' (seg_rom trbsegs)) md' /\
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k /\
getr regs' 13 = w64 (3 * xv) /\ getr regs' 14 = w64 (8 * cut) /\ getr regs' 24 = w64 (3 * xv) /\
getr regs' 10 = w64 (node + 16 + 8 * cut) /\ getr regs' 15 = w64 (cut + 3) /\
(forall r : bv 5, In r LCPH_KEEP -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros fy regs mem md HJ G9 G12 G18 G24 V408.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs. pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ node NODE_SIZE HAR HinN) as (Hn16 & Hn4096 & Hnceil & _). change (req_size NODE_SIZE) with 56 in Hnceil.
assert (Rs : 2 ^ 46 <= s1v /\ s1v + 416 <= 2 ^ 47 /\ alloc_ceiling <= s1v) by (clear - Hs1lo Hs1hi Hstk0 Hceil Hslo Hshi H47 C1; lia).
set (E := Ereg regs (map (Z_to_bv 64) [node] ++ [])).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j x, nth_error [node] j = Some x -> ew E (32 + j) = Z_to_bv 64 x) by (intros j x Hj; subst E; apply Ereg_vals; exact Hj).
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Rs; lia).
assert (U12 : bv_unsigned (ew E 12) = cut) by (rewrite (HE0 12%nat 12%bv eq_refl), G12; apply unsigned_lit_small; clear - Hcut; lia).
assert (U18 : bv_unsigned (ew E 18) = xv) by (rewrite (HE0 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; clear - Hxv; lia).
assert (U24 : bv_unsigned (ew E 24) = 3 * xv) by (rewrite (HE0 24%nat 24%bv eq_refl), G24; apply unsigned_lit_small; clear - Hxv; lia).
assert (A32 : bv_unsigned (ew E 32) = node) by (pose proof (HV 0%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hn4096 Hnceil C1; lia).
assert (HS : @st_ok trbsegs fy E ss_LCPH (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LCP_HEAD) mem (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LCPH. apply (entry_st_ok_full trbsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold lcph_mem. repeat apply Forall_cons; try apply Forall_nil.
unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E. rewrite U9.
split; [clear - Rs; lia|]. split; [clear - Rs; lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
apply (chunk_ok_val trbsegs E _ s1v 408 8 _ (node + 16)); [cbn [sv_denot]; rewrite A32; reflexivity | clear - Hn4096 Hnceil C1; lia | zside | exact V408].
- apply pairwise_disjoint_of_extents. unfold lcph_mem, extent_of_region. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; exact I].
cbn [lcph_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (Ereg regs _) with E.
rewrite U9, A32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - Rs C1 Hn16 Hn4096 Hnceil. repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok trbsegs lcph_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
assert (HAE : env_agree 33 E E) by (apply env_agree_refl).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 LCP_HEAD) mem (seg_rom trbsegs))) in HJ, SHOK.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK lcph_Bspan LCU_HEAD.
{ unfold ss_LCPH. cbn [ss_mem]. unfold lcph_mem. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 33 E Ey) by (env_agree_chain HAE) end.
pose proof HAEy as [EA ED].
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) [node] ++ [])) _) by (split; [intros j Hj; apply EA; lia | exact ED]).
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regs _ LCPH_KEEP HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
assert (GR : forall (r : bv 5), getr (ms_regs ms) r = sv_denot _ (sr_get (ss_regs _) r)) by (intros r; exact (st_ok_restrict_reg trbsegs (w_H W) _ _ ms r HS)).
assert (Hsll : forall Ex, bv_unsigned (ew Ex 12) = cut -> U Ex (SAlu ALU_SLL (SOff 12 0) (SLit 3)) = 8 * cut).
{ intros Ex HU. replace (8 * cut) with (cut * 2 ^ 3) by (clear; lia).
apply U_sll_small_q; [rewrite U_SOff, HU, Z.add_0_r; apply zcanon_id; unfold M64; clear - Hcut; lia | clear - Hcut; lia | clear; lia | clear - Hcut; lia]. }
rewrite (st_ok_restrict_mkst trbsegs (w_H W) _ _ ms HS eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. exists (ms_regs ms), (ms_mem ms). eexists. split; [reflexivity|].
split; [exact HJ|].
split; [rewrite (GR (13%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
cbn [sv_denot]; try rewrite EA by lia; rewrite U24, Z.add_0_r; reflexivity|].
split; [rewrite (GR (14%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
apply lg_denot_of_U; apply Hsll; try rewrite EA by lia; exact U12|].
split; [rewrite (GR (24%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
apply lg_denot_of_U; rewrite U_SMd; cbn [zmd_raw]; rewrite U_SOff, U_SLit; try rewrite EA by lia; rewrite U18, Z.add_0_r;
rewrite (zcanon_id xv) by (unfold M64; clear - Hxv; lia); change (zcanon 3) with 3; rewrite zcanon_id by (unfold M64; clear - Hxv; lia); clear; lia|].
split; [rewrite (GR (10%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
apply lg_denot_of_U; replace (node + 16 + 8 * cut) with ((8 * cut + 16) + node) by (clear; lia);
apply U_add_small_q;
[ apply U_add_small_q; [apply Hsll; try rewrite EA by lia; exact U12 | reflexivity | clear - Hcut; lia | clear; lia | clear - Hcut; lia]
| rewrite U_SOff; try rewrite EA by lia; rewrite A32, Z.add_0_r; apply zcanon_id; unfold M64; clear - Hn4096 Hnceil C1; lia
| clear - Hcut; lia | clear - Hn4096; lia | clear - Hcut Hnceil C1; lia ]|].
split; [rewrite (GR (15%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
cbn [sv_denot]; try rewrite EA by lia; rewrite U12; reflexivity|].
split; [exact HKR|].
split; [exact (lg_kept_ro _ _ _ _ _ HFr lcph_rs_ro)|].
intros a Ha. exact (apresent_grows _ _ _ _ HG Ha).
Qed.
End e.
Definition LCP_CLOB : list (bv 5) := [10; 11; 12; 13; 14; 15; 16; 17; 18; 20; 21; 24]%bv.
Definition LCP_KEEP : list (bv 5) := [1; 2; 3; 4; 5; 6; 7; 8; 9; 19; 22; 23; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma lcp_clob_cases : forall r : bv 5, reg_in r LCP_CLOB = false -> r = 0%bv \/ In r LCP_KEEP.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]). destruct Hin.
Qed.
Lemma rga_lcr_part {rc : YN05.RunCeil} : forall (B : asyms), AR_laws trbsegs B ->
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W pb pm p palc s1v node cut mean s m iv kv i1 k1 v25 (fy : FPState) (regs : bvmap 5 word) memc mdc,
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> frm_zero (@fp_csr fy) ->
sp0 - STK <= s1v -> s1v + 416 <= sp0 ->
In (node, NODE_SIZE) (ablocks B lyc Sc) -> In (pb, pm) (ablocks B lyc Sc) -> pb <= p -> p + zlen palc <= pb + pm -> (pb, pm) <> (node, NODE_SIZE) ->
0 <= cut <= 2 -> 0 <= mean < 2 ^ 64 -> is_quot mean m s ->
val_mem trbsegs (mrestrict (w_H W) memc) (s1v + 408) 8 (node + 16) ->
val_mem trbsegs (mrestrict (w_H W) memc) (node + 16 + 8 * cut) 8 mean ->
arr8 trbsegs (mrestrict (w_H W) memc) p palc ->
0 <= iv <= i1 -> i1 < 2 ^ 29 -> 3 * i1 + cut < zlen palc ->
(forall z, iv <= z < i1 -> ptest palc cut s m z = true) -> ptest palc cut s m i1 = false ->
0 <= k1 <= kv -> kv < 2 ^ 29 -> 3 * kv + cut < zlen palc ->
(forall z, k1 < z <= kv -> ptest palc cut s m z = false) -> ptest palc cut s m k1 = true ->
getr regs 9 = w64 s1v -> getr regs 11 = w64 (cut + 3 * iv) -> getr regs 12 = w64 cut -> getr regs 18 = w64 iv -> getr regs 24 = w64 (3 * iv) ->
getr regs 21 = w64 kv -> getr regs 25 = w64 v25 -> 16 <= v25 < 2 ^ 64 -> getr regs 5 = w64 2 ->
getr regs 26 = w64 p -> getr regs 23 = w64 (2 ^ 64 - 1 - p) -> getr regs 27 = w64 SB ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LCP_HEAD) memc (seg_rom trbsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists (fy' : FPState) regs2 mem2 md2,
c2 = mkCfg (@mkst fy' regs2 (Z_to_bv 64 LCD_EXIT) mem2 (seg_rom trbsegs)) md2 /\
frm_zero (@fp_csr fy') /\
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
(forall r : bv 5, reg_in r LCP_CLOB = false -> getr regs2 r = getr regs r) /\
getr regs2 18 = w64 i1 /\ getr regs2 21 = w64 k1 /\ getr regs2 13 = w64 (3 * i1) /\ getr regs2 24 = w64 (3 * i1) /\
getr regs2 20 = w64 (3 * k1) /\ getr regs2 12 = Z_to_bv 64 (cut - 3) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) mem2 a = aview trbsegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a)).
Proof.
intros B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W pb pm p palc s1v node cut mean s m iv kv i1 k1 v25 fy regs memc mdc
HJ Hfrm Hs1lo Hs1hi HinN HinP HP0 HP1 HPN Hcut Hmean Hq V408 Vmean Hpa Hiv Hi1 Hlen1 Hsm1 Hbig1 Hk1 Hkv Hlen2 Hsm2 Hbig2
G9 G11 G12 G18 G24 G21 G25 H25 G5 G26 G23 G27.
pose proof asan_consts as (C1 & _). pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pb pm HAR HinP) as (_ & Hp4096 & Hpceil & _ & _ & _ & Hpm0).
destruct (al_blocks _ _ LAWS _ _ _ _ _ node NODE_SIZE HAR HinN) as (Hn16 & Hn4096 & Hnceil & _). change (req_size NODE_SIZE) with 56 in Hnceil.
pose proof (req_size_pos pm ltac:(lia)) as [_ Hrp].
assert (Rp : 4096 <= p /\ p + zlen palc <= 140737479966720) by (clear - HP0 HP1 Hp4096 Hpceil Hrp C1; lia).
assert (KA : forall (mem1 : word -> option byte), (forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) mem1 a = aview trbsegs (w_H W) memc a) ->
arr8 trbsegs (mrestrict (w_H W) mem1) p palc).
{ intros mem1 Hk1m. apply (arr8_frame trbsegs _ _ p palc Hpa). intros a Ha. apply (mbyte_of_aview trbsegs). apply Hk1m. clear - Ha Rp. lia. }
assert (KV : forall (mem1 : word -> option byte), (forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) mem1 a = aview trbsegs (w_H W) memc a) ->
val_mem trbsegs (mrestrict (w_H W) mem1) (node + 16 + 8 * cut) 8 mean).
{ intros mem1 Hk1m. apply (val_mem_kept trbsegs _ _ _ _ _ Vmean). intros a Ha. apply (mbyte_of_aview trbsegs). apply Hk1m. clear - Ha Hcut Hn4096 Hnceil C1. lia. }
eapply SRr_bind.
{ exact (LCPH_run B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W s1v node cut iv Hs1lo Hs1hi HinN Hcut ltac:(clear - Hiv Hi1; lia)
fy regs memc mdc HJ G9 G12 G18 G24 V408). }
cbv beta. intros W1 c1' _ (-> & regs1 & mem1 & md1 & -> & HJ1 & R13a & R14a & R24a & R10a & R15a & HK1 & Hm1 & Hp1).
eapply SRr_bind.
{ exact (rga_lcr_up B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W pb pm p palc cut mean s m node NODE_SIZE (node + 16 + 8 * cut) v25 iv i1 fy regs1 mem1 md1
HJ1 Hfrm Hmean Hq HinP HP0 HP1 (KA mem1 Hm1) HinN ltac:(clear - Hcut; lia) ltac:(unfold NODE_SIZE; clear - Hcut; lia)
ltac:(clear - Hn16 Hcut; replace (node + 16 + 8 * cut) with (node + (2 + cut) * 8) by lia; rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by lia;
pose proof (Z.div_mod node 16 ltac:(lia)) as D; rewrite Hn16, Z.add_0_r in D; rewrite D; replace (16 * (node / 16)) with ((2 * (node / 16)) * 8) by lia; apply Z_mod_mult)
HPN (KV mem1 Hm1) Hcut Hiv Hi1 Hlen1 Hsm1 Hbig1
ltac:(rewrite (HK1 (11%bv : bv 5) ltac:(cbv; tauto)); exact G11) R13a
ltac:(rewrite (HK1 (18%bv : bv 5) ltac:(cbv; tauto)); exact G18) R24a R10a
ltac:(rewrite (HK1 (12%bv : bv 5) ltac:(cbv; tauto)); exact G12) R14a R15a
ltac:(rewrite (HK1 (25%bv : bv 5) ltac:(cbv; tauto)); exact G25) H25
ltac:(rewrite (HK1 (5%bv : bv 5) ltac:(cbv; tauto)); exact G5)
ltac:(rewrite (HK1 (26%bv : bv 5) ltac:(cbv; tauto)); exact G26)
ltac:(rewrite (HK1 (23%bv : bv 5) ltac:(cbv; tauto)); exact G23)
ltac:(rewrite (HK1 (27%bv : bv 5) ltac:(cbv; tauto)); exact G27)). }
cbv beta. intros W2 c2' _ (-> & fy2 & regs2 & mem2 & md2 & -> & Hfrm2 & Hf5b & HJ2 & HK2 & R18b & R13b & R24b & R11b & Hm2 & Hp2).
eapply SRr_bind.
{ exact (LCPG_run B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W kv cut p ltac:(clear - Hk1 Hkv; lia) Hcut ltac:(clear - Rp; lia) ltac:(clear - Rp Hlen2; lia)
fy2 regs2 mem2 md2 HJ2
ltac:(rewrite (HK2 (21%bv : bv 5) ltac:(vm_compute; reflexivity)), (HK1 (21%bv : bv 5) ltac:(cbv; tauto)); exact G21)
ltac:(rewrite (HK2 (12%bv : bv 5) ltac:(vm_compute; reflexivity)), (HK1 (12%bv : bv 5) ltac:(cbv; tauto)); exact G12)
ltac:(rewrite (HK2 (23%bv : bv 5) ltac:(vm_compute; reflexivity)), (HK1 (23%bv : bv 5) ltac:(cbv; tauto)); exact G23)). }
cbv beta. intros W3 c3' _ (-> & regs3 & mem3 & md3 & -> & HJ3 & R20c & R10c & R12c & HK3 & Hm3 & Hp3).
assert (Hm13 : forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) mem3 a = aview trbsegs (w_H W) memc a)
by (intros a Ha; rewrite (Hm3 a Ha), (Hm2 a Ha); exact (Hm1 a Ha)).
eapply SRr_mono.
{ exact (rga_lcr_down B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W pb pm p palc cut mean s m kv k1 fy2 regs3 mem3 md3
HJ3 Hfrm2 Hf5b Hmean Hq HinP HP0 HP1 (KA mem3 Hm13) Hcut Hk1 Hkv Hlen2 Hsm2 Hbig2 R12c R10c R20c
ltac:(rewrite (HK3 (21%bv : bv 5) ltac:(cbv; tauto)), (HK2 (21%bv : bv 5) ltac:(vm_compute; reflexivity)), (HK1 (21%bv : bv 5) ltac:(cbv; tauto)); exact G21)
ltac:(rewrite (HK3 (26%bv : bv 5) ltac:(cbv; tauto)), (HK2 (26%bv : bv 5) ltac:(vm_compute; reflexivity)), (HK1 (26%bv : bv 5) ltac:(cbv; tauto)); exact G26)
ltac:(rewrite (HK3 (23%bv : bv 5) ltac:(cbv; tauto)), (HK2 (23%bv : bv 5) ltac:(vm_compute; reflexivity)), (HK1 (23%bv : bv 5) ltac:(cbv; tauto)); exact G23)
ltac:(rewrite (HK3 (27%bv : bv 5) ltac:(cbv; tauto)), (HK2 (27%bv : bv 5) ltac:(vm_compute; reflexivity)), (HK1 (27%bv : bv 5) ltac:(cbv; tauto)); exact G27)). }
cbv beta. intros W4 c4' _ (-> & fy4 & regs4 & mem4 & md4 & -> & Hfrm4 & Hf5d & HJ4 & HK4 & R21d & R20d & R10d & Hm4 & Hp4).
split; [reflexivity|]. exists fy4, regs4, mem4, md4. split; [reflexivity|]. split; [exact Hfrm4|]. split; [exact HJ4|].
split.
{ intros r Hr. destruct (lcp_clob_cases r Hr) as [-> | Hin]; [rewrite !getr_zero; reflexivity|].
cbv [LCP_KEEP In] in Hin.
repeat (destruct Hin as [<- | Hin];
[ match goal with |- getr regs4 ?x = _ =>
rewrite (HK4 x ltac:(vm_compute; reflexivity)), (HK3 x ltac:(cbv; tauto)), (HK2 x ltac:(vm_compute; reflexivity)); apply HK1; cbv; tauto end |]).
destruct Hin. }
split; [rewrite (HK4 (18%bv : bv 5) ltac:(vm_compute; reflexivity)), (HK3 (18%bv : bv 5) ltac:(cbv; tauto)); exact R18b|].
split; [exact R21d|].
split; [rewrite (HK4 (13%bv : bv 5) ltac:(vm_compute; reflexivity)), (HK3 (13%bv : bv 5) ltac:(cbv; tauto)); exact R13b|].
split; [rewrite (HK4 (24%bv : bv 5) ltac:(vm_compute; reflexivity)), (HK3 (24%bv : bv 5) ltac:(cbv; tauto)); exact R24b|].
split; [exact R20d|].
split; [rewrite (HK4 (12%bv : bv 5) ltac:(vm_compute; reflexivity)); exact R12c|].
split; [intros a Ha; rewrite (Hm4 a Ha); exact (Hm13 a Ha)|].
intros a Ha. apply Hp4. apply Hp3. apply Hp2. apply Hp1. exact Ha.
Qed.
