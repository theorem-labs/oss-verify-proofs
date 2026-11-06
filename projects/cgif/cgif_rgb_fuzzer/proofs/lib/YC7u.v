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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM00 YM04 YM01 YM02 YM03 YM06 YP14 YI08 YI0c YI0g YI0d YI0f YI09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC68 YC5x.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition LCP_HEAD : Z := 0x83668.
Definition LCP_FLD : Z := 0x83698.
Definition LCP_GLUE : Z := 0x836f0.
Definition LCPH_KEEP : list (bv 5) := [1; 2; 3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 18; 19; 21; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LCPH_KEEPP : list (bv 5) := (20%bv : bv 5) :: (22%bv : bv 5) :: LCPH_KEEP.
Section b.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)) (k : Z).
Variables (lyc : alayout) (Sc : astate) (W : world trasegs).
Variables (s1v node iv : Z).
Hypothesis Hs1lo : sp0 - STK <= s1v. Hypothesis Hs1hi : s1v + 376 <= sp0.
Hypothesis HinN : In (node, NODE_SIZE) (ablocks B lyc Sc).
Hypothesis Hiv : 0 <= iv < 2 ^ 29.
Definition lcph_lits (cut : Z) : list (option Z) := [None; None; None; None; None; None; None; Some cut; None; None].
Definition lcph_s6 : sv := SOff 32 48.
Definition lcph_s4 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 48) (SLit 3)) (SOff 25 0).
Definition lcph_regs := sr_set (sr_set sr_atoms 22%bv lcph_s6) 20%bv lcph_s4.
Definition lcph_mem (cut : Z) : smem :=
[ YQ0b.mkRegion (Some 9%nat) 368 376 0 0 [YQ0b.mkChunk 368 (CVal 8 (SOff 32 16))];
YQ0b.mkRegion (Some 32%nat) 0 NODE_SIZE 0 0 (obj_chunks_gen LAY_Node 37 (lcph_lits cut)) ].
Definition lcph_facts : facts :=
mkFacts [ (9%nat, mkAF (2^46) (2^47) 0); (25%nat, mkAF SB SB 0); (32%nat, mkAF 4096 140737479966720 4) ] [] [].
Definition ss_LCPH (cut : Z) : sstate := mkSS LCP_HEAD lcph_regs (lcph_mem cut) None lcph_facts.
Definition lcph_Bx : sv := SOff 25 0.
Definition lcph_SH : list shent := [ mkSHE 32 0 NODE_SIZE ].
Definition lcph_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition lcph_vals (c0 c1 : Z) (n : tnode) (leafv : Z) : list Z := [node; 0; 0; 0; 0] ++ node_vals c0 c1 n leafv.
Definition lcph_base (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k /\
frm_zero (@fp_csr fy) /\ getr regs 25 = w64 SB /\ getr regs 9 = w64 s1v.
Lemma LCPH_seed : forall (fy : FPState) (regs : bvmap 5 word) mem md (n : tnode) (c0 c1 leafv : Z),
lcph_base fy regs mem md -> getr regs 23 = w64 iv ->
getr regs 22 = w64 (node + 48) -> getr regs 20 = Z_to_bv 64 (SB + (node + 48) / 8) ->
val_mem trasegs (mrestrict (w_H W) mem) (s1v + 368) 8 (node + 16) ->
obj_at trasegs (mrestrict (w_H W) mem) node LAY_Node (node_vals c0 c1 n leafv) -> length (tn_mean n) = 3%nat ->
let E0 := Ereg regs (map (Z_to_bv 64) (lcph_vals c0 c1 n leafv) ++ []) in
let E := ew_fregs E0 64 (@fp_regs fy) in
st_okF trasegs E (mkSST LCP_HEAD lcph_regs (sfr_atoms 64) (lcph_mem (tn_cut n)) None lcph_facts)
(restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LCP_HEAD) mem (seg_rom trasegs))) /\
sh_ok trasegs lcph_Bx lcph_SH E (mrestrict (w_H W) mem) /\
(forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) /\
(forall j x, nth_error (node_vals c0 c1 n leafv) j = Some x -> ew E (37 + j) = Z_to_bv 64 x) /\
bv_unsigned (ew E 32) = node /\ bv_unsigned (ew E 23) = iv.
Proof.
intros fy regs mem md n c0 c1 leafv HB G23 G22 G20 V368 Ond Hlen3 E0 E.
pose proof HB as (HJ & Hfrm & G25 & G9). pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ node NODE_SIZE HAR HinN) as (Hn16 & Hn4096 & Hnceil & _). change (req_size NODE_SIZE) with 56 in Hnceil.
assert (Rs : 2 ^ 46 <= s1v /\ s1v + 376 <= 2 ^ 47 /\ alloc_ceiling <= s1v) by (clear - Hs1lo Hs1hi Hstk0 Hceil Hslo Hshi H47 C1; lia).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E0 j = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall j x, nth_error (lcph_vals c0 c1 n leafv) j = Some x -> ew E0 (32 + j) = Z_to_bv 64 x) by (intros j x Hj; subst E0; apply Ereg_vals; exact Hj).
assert (HVN : forall j x, nth_error (node_vals c0 c1 n leafv) j = Some x -> ew E0 (37 + j) = Z_to_bv 64 x).
{ intros j x Hj. change (37 + j)%nat with (32 + (5 + j))%nat. apply HV. unfold lcph_vals. exact Hj. }
assert (HEE : forall j, (j < 64)%nat -> ew E j = ew E0 j) by (intros j Hj; subst E; apply ew_fregs_low; exact Hj).
assert (U9 : bv_unsigned (ew E0 9) = s1v) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Rs; lia).
assert (U23 : bv_unsigned (ew E0 23) = iv) by (rewrite (HE0 23%nat 23%bv eq_refl), G23; apply unsigned_lit_small; clear - Hiv; lia).
assert (E25 : ew E0 25 = w64 SB) by (rewrite (HE0 25%nat 25%bv eq_refl); exact G25).
assert (U25 : bv_unsigned (ew E0 25) = SB) by (rewrite E25; apply unsigned_lit_small; unfold SB; lia).
assert (A32 : bv_unsigned (ew E0 32) = node) by (pose proof (HV 0%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hn4096 Hnceil C1; lia).
assert (Hq : 0 <= (node + 48) / 8 <= node + 48) by (split; [apply Z.div_pos; clear - Hn4096; lia | apply Z.div_le_upper_bound; clear - Hn4096; lia]).
assert (HS0 : @st_ok trasegs fy E0 (ss_LCPH (tn_cut n)) (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LCP_HEAD) mem (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LCPH, lcph_regs. apply (entry_st_ok_full trasegs).
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X |] | intros X; discriminate X |].
+ rewrite G22. unfold lcph_s6. cbn [sv_denot]. change (Ereg regs _) with E0. rewrite A32. reflexivity.
+ rewrite G20. symmetry. apply lg_denot_of_U. unfold lcph_s4. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite !U_SOff, U_SLit. change (Ereg regs _) with E0. rewrite A32, U25, !Z.add_0_r.
rewrite (zcanon_id (node + 48)), (zcanon_id SB) by (unfold M64, SB; clear - Hn4096 Hnceil C1; lia).
change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_id ((node + 48) / 8)) by (unfold M64; clear - Hq Hn4096 Hnceil C1; lia).
rewrite zcanon_id by (unfold M64, SB; clear - Hq Hn4096 Hnceil C1; lia). lia.
- vm_compute. reflexivity.
- unfold lcph_mem. repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite U9.
split; [clear - Rs; lia|]. split; [clear - Rs; lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
apply (chunk_ok_val trasegs E0 _ s1v 368 8 _ (node + 16)); [cbn [sv_denot]; rewrite A32; reflexivity | clear - Hn4096 Hnceil C1; lia | zside | exact V368].
+ eapply (region_ok_obj_gen trasegs _ _ 32 node); [exact A32 | clear - Hn4096; lia | unfold NODE_SIZE; clear - Hnceil C1; lia | exact Ond | reflexivity | exact HVN | | intros j Hj; lia].
intros j z Hj. unfold node_vals. destruct (tn_mean n) as [|m0 [|m1 [|m2 [|m3 l0]]]]; try discriminate Hlen3.
do 7 (destruct j as [|j]; [cbn in Hj; congruence|]). destruct j as [|j]; cbn in Hj |- *; [congruence|].
do 2 (destruct j as [|j]; [cbn in Hj; congruence|]). destruct j; discriminate Hj.
- apply pairwise_disjoint_of_extents. unfold lcph_mem, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. change (Ereg regs _) with E0. rewrite U9, A32. unfold NODE_SIZE.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. clear - Rs Hnceil. repeat split; lia.
- split; [|split; exact I].
cbn [lcph_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (Ereg regs _) with E0.
rewrite U9, E25, A32. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - Rs C1 Hn16 Hn4096 Hnceil. unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK0 : sh_ok trasegs lcph_Bx lcph_SH E0 (mrestrict (w_H W) mem)).
{ unfold sh_ok, lcph_SH. constructor; [|constructor].
apply (shent_ok_of_block trasegs B LAWS lyc Sc W mem md E0 lcph_Bx 32 node NODE_SIZE 0 NODE_SIZE HAR HinN).
+ unfold U, lcph_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A32.
+ lia.
+ change (req_size NODE_SIZE) with 56. unfold NODE_SIZE. lia. }
split; [exact (st_ok_enterF trasegs fy 64 E0 (ss_LCPH (tn_cut n)) _ HS0 ltac:(vm_compute; reflexivity) Hfrm)|].
split; [exact (sh_ok_agree trasegs lcph_Bx lcph_SH 64 E0 E _ (env_agree_ew_fregs E0 64 _) ltac:(vm_compute; reflexivity) SHOK0)|].
split; [intros j rr Hj; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5; rewrite HEE by lia; apply HE0; exact Hj|].
split.
{ intros j x Hj. assert (Hj10 : (j < 10)%nat).
{ pose proof (proj1 (nth_error_Some (node_vals c0 c1 n leafv) j) ltac:(rewrite Hj; discriminate)) as Hl. unfold node_vals in Hl. rewrite !length_app, Hlen3 in Hl. cbn [length] in Hl. lia. }
rewrite HEE by lia. apply HVN. exact Hj. }
split; [rewrite HEE by lia; exact A32 | rewrite HEE by lia; exact U23].
Qed.
Definition LCPH_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (cut mean : Z) : world trasegs -> config -> Prop :=
fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 LCU_HEAD) mem' (seg_rom trasegs)) md' /\
lcph_base fy' regs' mem' md' /\ reg_get (@fp_regs fy') (15%bv : bv 5) = Z_to_bv 64 mean /\
getr regs' 11 = w64 cut /\ getr regs' 12 = w64 (3 * iv) /\ getr regs' 23 = Z_to_bv 64 (iv - 1) /\
(forall r : bv 5, In r LCPH_KEEPP -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Lemma lcph_rs_ro : forall cut rr, In rr (lcph_mem cut) -> YQ0b.r_whi rr <= YQ0b.r_wlo rr.
Proof. intros cut rr [<- | [<- | []]]; cbn; lia. Qed.
Lemma LCPH_run : forall (fy : FPState) (regs : bvmap 5 word) mem md (n : tnode) (c0 c1 leafv : Z),
lcph_base fy regs mem md -> getr regs 23 = w64 iv ->
getr regs 22 = w64 (node + 48) -> getr regs 20 = Z_to_bv 64 (SB + (node + 48) / 8) ->
val_mem trasegs (mrestrict (w_H W) mem) (s1v + 368) 8 (node + 16) ->
obj_at trasegs (mrestrict (w_H W) mem) node LAY_Node (node_vals c0 c1 n leafv) -> tnode_wf n ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LCP_HEAD) mem (seg_rom trasegs)) md)
(LCPH_post fy regs mem (tn_cut n) (nth (Z.to_nat (tn_cut n)) (tn_mean n) 0)).
Proof.
intros fy regs mem md n c0 c1 leafv HB G23 G22 G20 V368 Ond Hwf.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
destruct Hwf as (Hcut & _ & _ & _ & Hlen3 & Hmeans).
pose proof HB as (HJ & Hfrm & G25 & G9). pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ node NODE_SIZE HAR HinN) as (Hn16 & Hn4096 & Hnceil & _). change (req_size NODE_SIZE) with 56 in Hnceil.
destruct (LCPH_seed fy regs mem md n c0 c1 leafv HB G23 G22 G20 V368 Ond Hlen3) as (HS & SHOK & HE & HVN & U32 & U23).
set (E := ew_fregs _ 64 _) in HS, SHOK, HE, HVN, U32, U23.
pose proof (st_okF_to_legacy trasegs _ _ _ HS) as HSL0.
pose proof (st_ok_restrict_reg trasegs (w_H W) E _ _ (20%bv : bv 5) HSL0) as P20.
pose proof (st_ok_restrict_reg trasegs (w_H W) E _ _ (22%bv : bv 5) HSL0) as P22.
cbn [ms_regs mkst restrict] in P20, P22.
lazymatch type of P20 with _ = sv_denot _ ?e => let v := eval vm_compute in e in change e with v in P20 end.
lazymatch type of P22 with _ = sv_denot _ ?e => let v := eval vm_compute in e in change e with v in P22 end.
clear HSL0.
assert (HAE96 : env_agree 96 E E) by (apply env_agree_refl).
assert (FIN : forall (fz : FPState) E1 ss1 ms1 md1 (cutv meanv : Z), @st_ok trasegs fz E1 ss1 (restrict (w_H W) ms1) -> env_agree 96 E E1 ->
ss_pc ss1 = LCU_HEAD -> ss_resv ss1 = None ->
sr_get (ss_regs ss1) 11 = SLit cutv -> 0 <= cutv <= 2 ->
sr_get (ss_regs ss1) 12 = SMd M_MUL (SOff 23 0) (SLit 3) -> sr_get (ss_regs ss1) 23 = SOff 23 (-1) ->
sr_get (ss_regs ss1) 20 = lcph_s4 -> sr_get (ss_regs ss1) 22 = lcph_s6 ->
forallb (fun rr : bv 5 => sv_eqb (sr_get (ss_regs ss1) rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) LCPH_KEEP = true ->
frm_zero (@fp_csr fz) -> reg_get (@fp_regs fz) (15%bv : bv 5) = Z_to_bv 64 meanv ->
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms1) md1 k ->
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) (ms_mem ms1) a = aview trasegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms1) a) ->
SRr trasegs W (mkCfg ms1 md1) (LCPH_post fy regs mem cutv meanv)).
{ intros fz E1 ss1 ms1 md1 cutv meanv HS1 HAE1 Hpc1 Hrv1 Q11 Hcv Q12 Q23 Q20 Q22 QK Hfz Hfz5 HJ1 Hk1 Hp1. pose proof HAE1 as [EA ED].
assert (HAE0 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (lcph_vals c0 c1 n leafv) ++ [])) E1).
{ split; [intros j Hj; rewrite EA by lia; subst E; rewrite ew_fregs_low by lia; reflexivity | rewrite ED; reflexivity]. }
pose proof (regs_kept_of_st_ok trasegs E1 ss1 _ regs _ LCPH_KEEP HS1 HAE0 QK) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trasegs (w_H W) E1 ss1 ms1 HS1 Hrv1), Hpc1. apply SRr_ret.
split; [reflexivity|]. exists fz, (ms_regs ms1), (ms_mem ms1), md1. split; [reflexivity|].
split; [split; [exact HJ1|]; split; [exact Hfz|]; split; [rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25 | rewrite (HKR (9%bv : bv 5) ltac:(cbv; tauto)); exact G9]|].
split; [exact Hfz5|].
split; [rewrite (st_ok_restrict_reg trasegs (w_H W) E1 ss1 ms1 (11%bv : bv 5) HS1), Q11; reflexivity|].
split.
{ rewrite (st_ok_restrict_reg trasegs (w_H W) E1 ss1 ms1 (12%bv : bv 5) HS1), Q12. apply lg_denot_of_U.
rewrite U_SMd. cbn [zmd_raw]. rewrite U_SOff, U_SLit, EA, U23, Z.add_0_r by lia.
rewrite (zcanon_id iv) by (unfold M64; clear - Hiv; lia). change (zcanon 3) with 3.
rewrite zcanon_id by (unfold M64; clear - Hiv; lia). clear; lia. }
split.
{ rewrite (st_ok_restrict_reg trasegs (w_H W) E1 ss1 ms1 (23%bv : bv 5) HS1), Q23. cbn [sv_denot]. rewrite EA, U23 by lia. reflexivity. }
split.
{ intros r [<- | [<- | Hr]]; [| | exact (HKR r Hr)].
- rewrite (st_ok_restrict_reg trasegs (w_H W) E1 ss1 ms1 (20%bv : bv 5) HS1), Q20, P20. exact (sv_denot_agree 96 E E1 lcph_s4 HAE1 ltac:(vm_compute; reflexivity)).
- rewrite (st_ok_restrict_reg trasegs (w_H W) E1 ss1 ms1 (22%bv : bv 5) HS1), Q22, P22. exact (sv_denot_agree 96 E E1 lcph_s6 HAE1 ltac:(vm_compute; reflexivity)). }
split; [exact Hk1 | exact Hp1]. }
assert (MN : forall j, (j < 3)%nat -> nth_error (node_vals c0 c1 n leafv) (2 + j) = Some (nth j (tn_mean n) 0)).
{ intros j Hj. unfold node_vals. destruct (tn_mean n) as [|m0 [|m1 [|m2 [|m3 l0]]]]; try discriminate Hlen3. destruct j as [|[|[|j]]]; try lia; reflexivity. }
assert (Hc3 : tn_cut n = 0 \/ tn_cut n = 1 \/ tn_cut n = 2) by (clear - Hcut; lia).
destruct Hc3 as [Ec | [Ec | Ec]]; rewrite Ec in HS |- *.
- aj_run_to_tokF tratbl_lib_ok HS HJ SHOK lcph_Bspan LCP_FLD.
{ cbn [ss_mem]. unfold lcph_mem. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr1; rename HG into HG1; clear HF.
lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
pose proof (st_okF_frm trasegs _ _ _ HS) as Hfrm2. pose proof (st_okF_freg trasegs _ _ _ (15%bv : bv 5) HS) as Hf52.
lazymatch type of Hf52 with _ = sv_denot ?Ex (sfr_get ?fr ?r) => let v := eval vm_compute in (sfr_get fr r) in change (sfr_get fr r) with v in Hf52 end.
cbn [sv_denot] in Hf52. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, ?(proj1 HAEx) in Hf52 by lia.
pose proof (HVN (2 + 0)%nat _ (MN 0%nat ltac:(lia))) as X. cbn [Nat.add] in X. rewrite X in Hf52. clear X.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msA := msx) in * end.
assert (KW1 : forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) (ms_mem msA) a = aview trasegs (w_H W) mem a) by (exact (lg_kept_ro _ _ _ _ _ HFr1 (lcph_rs_ro 0))).
pose proof (st_okF_to_legacy trasegs _ _ _ HS) as HSL. clear HS.
aj_run_to_tok tratbl_lib_ok HSL HJ SHOK lcph_Bspan LCU_HEAD.
{ apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HSL with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 96 E Ey) by (env_agree_chain HAEx) end.
apply (FIN _ _ _ _ _ 0 _ HSL HAEy); [reflexivity | reflexivity | reflexivity | clear; lia | reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | exact Hfrm2 | exact Hf52 | exact HJ | | ].
+ intros a Ha. rewrite (lg_kept_ro _ _ _ _ _ HFr (lcph_rs_ro 0) a Ha). exact (KW1 a Ha).
+ intros a Ha. apply (apresent_grows _ _ _ _ HG). apply (apresent_grows _ _ _ _ HG1). exact Ha.
- aj_run_to_tokF tratbl_lib_ok HS HJ SHOK lcph_Bspan LCP_FLD.
{ cbn [ss_mem]. unfold lcph_mem. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr1; rename HG into HG1; clear HF.
lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
pose proof (st_okF_frm trasegs _ _ _ HS) as Hfrm2. pose proof (st_okF_freg trasegs _ _ _ (15%bv : bv 5) HS) as Hf52.
lazymatch type of Hf52 with _ = sv_denot ?Ex (sfr_get ?fr ?r) => let v := eval vm_compute in (sfr_get fr r) in change (sfr_get fr r) with v in Hf52 end.
cbn [sv_denot] in Hf52. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, ?(proj1 HAEx) in Hf52 by lia.
pose proof (HVN (2 + 1)%nat _ (MN 1%nat ltac:(lia))) as X. cbn [Nat.add] in X. rewrite X in Hf52. clear X.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msA := msx) in * end.
assert (KW1 : forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) (ms_mem msA) a = aview trasegs (w_H W) mem a) by (exact (lg_kept_ro _ _ _ _ _ HFr1 (lcph_rs_ro 1))).
pose proof (st_okF_to_legacy trasegs _ _ _ HS) as HSL. clear HS.
aj_run_to_tok tratbl_lib_ok HSL HJ SHOK lcph_Bspan LCU_HEAD.
{ apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HSL with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 96 E Ey) by (env_agree_chain HAEx) end.
apply (FIN _ _ _ _ _ 1 _ HSL HAEy); [reflexivity | reflexivity | reflexivity | clear; lia | reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | exact Hfrm2 | exact Hf52 | exact HJ | | ].
+ intros a Ha. rewrite (lg_kept_ro _ _ _ _ _ HFr (lcph_rs_ro 1) a Ha). exact (KW1 a Ha).
+ intros a Ha. apply (apresent_grows _ _ _ _ HG). apply (apresent_grows _ _ _ _ HG1). exact Ha.
- aj_run_to_tokF tratbl_lib_ok HS HJ SHOK lcph_Bspan LCP_FLD.
{ cbn [ss_mem]. unfold lcph_mem. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr1; rename HG into HG1; clear HF.
lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
pose proof (st_okF_frm trasegs _ _ _ HS) as Hfrm2. pose proof (st_okF_freg trasegs _ _ _ (15%bv : bv 5) HS) as Hf52.
lazymatch type of Hf52 with _ = sv_denot ?Ex (sfr_get ?fr ?r) => let v := eval vm_compute in (sfr_get fr r) in change (sfr_get fr r) with v in Hf52 end.
cbn [sv_denot] in Hf52. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, ?(proj1 HAEx) in Hf52 by lia.
pose proof (HVN (2 + 2)%nat _ (MN 2%nat ltac:(lia))) as X. cbn [Nat.add] in X. rewrite X in Hf52. clear X.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msA := msx) in * end.
assert (KW1 : forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) (ms_mem msA) a = aview trasegs (w_H W) mem a) by (exact (lg_kept_ro _ _ _ _ _ HFr1 (lcph_rs_ro 2))).
pose proof (st_okF_to_legacy trasegs _ _ _ HS) as HSL. clear HS.
aj_run_to_tok tratbl_lib_ok HSL HJ SHOK lcph_Bspan LCU_HEAD.
{ apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HSL with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 96 E Ey) by (env_agree_chain HAEx) end.
apply (FIN _ _ _ _ _ 2 _ HSL HAEy); [reflexivity | reflexivity | reflexivity | clear; lia | reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | exact Hfrm2 | exact Hf52 | exact HJ | | ].
+ intros a Ha. rewrite (lg_kept_ro _ _ _ _ _ HFr (lcph_rs_ro 2) a Ha). exact (KW1 a Ha).
+ intros a Ha. apply (apresent_grows _ _ _ _ HG). apply (apresent_grows _ _ _ _ HG1). exact Ha.
Qed.
End b.
Definition LCPG_KEEP : list (bv 5) := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 14; 15; 16; 17; 18; 19; 20; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Section c.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)) (k : Z).
Variables (lyc : alayout) (Sc : astate) (W : world trasegs).
Variables (i1 kv : Z).
Hypothesis Hi1 : 0 <= i1 < 2 ^ 29. Hypothesis Hkv : 0 <= kv < 2 ^ 29.
Definition ss_LCPG : sstate := mkSS LCP_GLUE sr_atoms [] None (mkFacts [] [] []).
Definition lcpg_Bx : sv := SOff 25 0.
Definition lcpg_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Lemma LCPG_run : forall (fy : FPState) (regs : bvmap 5 word) mem md,
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
getr regs 12 = w64 (3 * i1 + 3) -> getr regs 21 = w64 kv ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LCP_GLUE) mem (seg_rom trasegs)) md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (@mkst fy regs' (Z_to_bv 64 LCD_HEAD) mem' (seg_rom trasegs)) md' /\
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k /\
getr regs' 12 = w64 (3 * i1) /\ getr regs' 13 = w64 (3 * kv) /\ getr regs' 21 = w64 (kv + 1) /\
(forall r : bv 5, In r LCPG_KEEP -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros fy regs mem md HJ G12 G21.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
set (E := Ereg regs (map (Z_to_bv 64) [] ++ [])).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (U12 : bv_unsigned (ew E 12) = 3 * i1 + 3) by (rewrite (HE0 12%nat 12%bv eq_refl), G12; apply unsigned_lit_small; clear - Hi1; lia).
assert (U21 : bv_unsigned (ew E 21) = kv) by (rewrite (HE0 21%nat 21%bv eq_refl), G21; apply unsigned_lit_small; clear - Hkv; lia).
assert (HS : @st_ok trasegs fy E ss_LCPG (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LCP_GLUE) mem (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LCPG. apply (entry_st_ok_full trasegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
- split; [exact I | split; exact I]. }
assert (SHOK : sh_ok trasegs lcpg_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
assert (HAE : env_agree 32 E E) by (apply env_agree_refl).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 LCP_GLUE) mem (seg_rom trasegs))) in HJ, SHOK.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK lcpg_Bspan LCD_HEAD.
{ unfold ss_LCPG. cbn [ss_mem]. apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 32 E Ey) by (env_agree_chain HAE) end.
pose proof HAEy as [EA ED].
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ LCPG_KEEP HS HAEy ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
assert (GR : forall (r : bv 5), getr (ms_regs ms) r = sv_denot _ (sr_get (ss_regs _) r)) by (intros r; exact (st_ok_restrict_reg trasegs (w_H W) _ _ ms r HS)).
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ ms HS eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. exists (ms_regs ms), (ms_mem ms). eexists. split; [reflexivity|].
split; [exact HJ|].
split; [rewrite (GR (12%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
cbn [sv_denot]; try rewrite EA by lia; rewrite U12; unfold w64; f_equal; clear; lia|].
split; [rewrite (GR (13%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
apply lg_denot_of_U; rewrite U_SMd; cbn [zmd_raw]; rewrite U_SOff, U_SLit; try rewrite EA by lia; rewrite U21, Z.add_0_r;
rewrite (zcanon_id kv) by (unfold M64; clear - Hkv; lia); change (zcanon 3) with 3; rewrite zcanon_id by (unfold M64; clear - Hkv; lia); clear; lia|].
split; [rewrite (GR (21%bv : bv 5)); lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
cbn [sv_denot]; try rewrite EA by lia; rewrite U21; reflexivity|].
split; [exact HKR|].
split; [exact (lg_kept_ro _ _ _ _ _ HFr ltac:(intros rr []))|].
intros a Ha. exact (apresent_grows _ _ _ _ HG Ha).
Qed.
End c.
Definition LCP_CLOB : list (bv 5) := [10; 11; 12; 13; 14; 15; 21; 23]%bv.
Definition LCP_KEEP : list (bv 5) := [1; 2; 3; 4; 5; 6; 7; 8; 9; 16; 17; 18; 19; 20; 22; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma lcp_clob_cases : forall r : bv 5, reg_in r LCP_CLOB = false -> r = 0%bv \/ In r LCP_KEEP.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]). destruct Hin.
Qed.
Lemma rga_lcr_part {rc : YN05.RunCeil} : forall (B : asyms), AR_laws trasegs B ->
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W pb pm p palc s1v node (n : tnode) c0 c1 leafv s m iv kv i1 k1 (fy : FPState) (regs : bvmap 5 word) memc mdc,
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> frm_zero (@fp_csr fy) ->
sp0 - STK <= s1v -> s1v + 376 <= sp0 ->
In (node, NODE_SIZE) (ablocks B lyc Sc) -> In (pb, pm) (ablocks B lyc Sc) -> pb <= p -> p + zlen palc <= pb + pm ->
obj_at trasegs (mrestrict (w_H W) memc) node LAY_Node (node_vals c0 c1 n leafv) -> tnode_wf n ->
val_mem trasegs (mrestrict (w_H W) memc) (s1v + 368) 8 (node + 16) ->
arr8 trasegs (mrestrict (w_H W) memc) p palc ->
is_quot (nth (Z.to_nat (tn_cut n)) (tn_mean n) 0) m s ->
0 <= iv <= i1 -> i1 < 2 ^ 29 -> 3 * i1 + tn_cut n < zlen palc ->
(forall z, iv <= z < i1 -> ptest palc (tn_cut n) s m z = true) -> ptest palc (tn_cut n) s m i1 = false ->
0 <= k1 <= kv -> kv < 2 ^ 29 -> 3 * kv + tn_cut n < zlen palc ->
(forall z, k1 < z <= kv -> ptest palc (tn_cut n) s m z = false) -> ptest palc (tn_cut n) s m k1 = true ->
getr regs 9 = w64 s1v -> getr regs 20 = Z_to_bv 64 (SB + (node + 48) / 8) -> getr regs 22 = w64 (node + 48) ->
getr regs 23 = w64 iv -> getr regs 21 = w64 kv -> getr regs 25 = w64 SB -> getr regs 26 = w64 p ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LCP_HEAD) memc (seg_rom trasegs)) mdc)
(fun W2 c2 => W2 = W /\ exists (fy' : FPState) regs2 mem2 md2,
c2 = mkCfg (@mkst fy' regs2 (Z_to_bv 64 LCD_EXIT) mem2 (seg_rom trasegs)) md2 /\
frm_zero (@fp_csr fy') /\
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
(forall r : bv 5, reg_in r LCP_CLOB = false -> getr regs2 r = getr regs r) /\
getr regs2 23 = w64 i1 /\ getr regs2 21 = w64 k1 /\ getr regs2 12 = w64 (3 * i1) /\ getr regs2 13 = Z_to_bv 64 (3 * k1 - 3) /\
getr regs2 11 = w64 (tn_cut n) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) mem2 a = aview trasegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a)).
Proof.
intros B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W pb pm p palc s1v node n c0 c1 leafv s m iv kv i1 k1 fy regs memc mdc
HJ Hfrm Hs1lo Hs1hi HinN HinP HP0 HP1 Ond Hwf V368 Hpa Hq Hiv Hi1 Hlen1 Hsm1 Hbig1 Hk1 Hkv Hlen2 Hsm2 Hbig2 G9 G20 G22 G23 G21 G25 G26.
pose proof asan_consts as (C1 & _). pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pb pm HAR HinP) as (_ & Hp4096 & Hpceil & _ & _ & _ & Hpm0).
pose proof (req_size_pos pm ltac:(lia)) as [_ Hrp].
assert (Rp : 4096 <= p /\ p + zlen palc <= 140737479966720) by (clear - HP0 HP1 Hp4096 Hpceil Hrp C1; lia).
pose proof Hwf as (Hcut & _ & _ & _ & Hlen3 & Hmeans).
set (cut := tn_cut n) in *. set (mean := nth (Z.to_nat cut) (tn_mean n) 0) in *.
assert (Hmean : 0 <= mean < 2 ^ 64).
{ subst mean. apply (proj1 (Forall_forall _ _) Hmeans). apply nth_In. rewrite Hlen3. clear - Hcut. lia. }
assert (KA : forall (mem1 : word -> option byte), (forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) mem1 a = aview trasegs (w_H W) memc a) ->
arr8 trasegs (mrestrict (w_H W) mem1) p palc).
{ intros mem1 Hk1m. apply (arr8_frame trasegs _ _ p palc Hpa). intros a Ha. apply (mbyte_of_aview trasegs). apply Hk1m. clear - Ha Rp. lia. }
eapply SRr_bind.
{ exact (LCPH_run B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W s1v node iv Hs1lo Hs1hi HinN ltac:(clear - Hiv Hi1; lia)
fy regs memc mdc n c0 c1 leafv (conj HJ (conj Hfrm (conj G25 G9))) G23 G22 G20 V368 Ond Hwf). }
cbv beta. intros W1 c1' _ (-> & fy1 & regs1 & mem1 & md1 & -> & (HJ1 & Hfrm1 & G25a & G9a) & Hf5a & R11a & R12a & R23a & HK1 & Hm1 & Hp1).
fold cut mean in Hf5a, R11a.
eapply SRr_bind.
{ exact (rga_lcr_up B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W pb pm p palc cut mean s m iv i1 fy1 regs1 mem1 md1
HJ1 Hfrm1 Hf5a Hmean Hq HinP HP0 HP1 (KA mem1 Hm1) Hcut Hiv Hi1 Hlen1 Hsm1 Hbig1 R11a R12a R23a
ltac:(rewrite (HK1 (26%bv : bv 5) ltac:(cbv; tauto)); exact G26) G25a). }
cbv beta. intros W2 c2' _ (-> & fy2 & regs2 & mem2 & md2 & -> & Hfrm2 & Hf5b & HJ2 & HK2 & R12b & R23b & R10b & Hm2 & Hp2).
eapply SRr_bind.
{ exact (LCPG_run B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W i1 kv ltac:(clear - Hiv Hi1; lia) ltac:(clear - Hk1 Hkv; lia) fy2 regs2 mem2 md2 HJ2 R12b
ltac:(rewrite (HK2 (21%bv : bv 5) ltac:(vm_compute; reflexivity)), (HK1 (21%bv : bv 5) ltac:(cbv; tauto)); exact G21)). }
cbv beta. intros W3 c3' _ (-> & regs3 & mem3 & md3 & -> & HJ3 & R12c & R13c & R21c & HK3 & Hm3 & Hp3).
assert (Hm13 : forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) mem3 a = aview trasegs (w_H W) memc a)
by (intros a Ha; rewrite (Hm3 a Ha), (Hm2 a Ha); exact (Hm1 a Ha)).
eapply SRr_mono.
{ exact (rga_lcr_down B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W pb pm p palc cut mean s m kv k1 fy2 regs3 mem3 md3
HJ3 Hfrm2 Hf5b Hmean Hq HinP HP0 HP1 (KA mem3 Hm13) Hcut Hk1 Hkv Hlen2 Hsm2 Hbig2
ltac:(rewrite (HK3 (11%bv : bv 5) ltac:(cbv; tauto)), (HK2 (11%bv : bv 5) ltac:(vm_compute; reflexivity)); exact R11a) R13c R21c
ltac:(rewrite (HK3 (26%bv : bv 5) ltac:(cbv; tauto)), (HK2 (26%bv : bv 5) ltac:(vm_compute; reflexivity)), (HK1 (26%bv : bv 5) ltac:(cbv; tauto)); exact G26)
ltac:(rewrite (HK3 (25%bv : bv 5) ltac:(cbv; tauto)), (HK2 (25%bv : bv 5) ltac:(vm_compute; reflexivity)); exact G25a)). }
cbv beta. intros W4 c4' _ (-> & fy4 & regs4 & mem4 & md4 & -> & Hfrm4 & Hf5d & HJ4 & HK4 & R13d & R21d & R10d & Hm4 & Hp4).
split; [reflexivity|]. exists fy4, regs4, mem4, md4. split; [reflexivity|]. split; [exact Hfrm4|]. split; [exact HJ4|].
split.
{ intros r Hr. destruct (lcp_clob_cases r Hr) as [-> | Hin]; [rewrite !getr_zero; reflexivity|].
cbv [LCP_KEEP In] in Hin.
repeat (destruct Hin as [<- | Hin];
[ match goal with |- getr regs4 ?x = _ =>
rewrite (HK4 x ltac:(vm_compute; reflexivity)), (HK3 x ltac:(cbv; tauto)), (HK2 x ltac:(vm_compute; reflexivity)); apply HK1; cbv; tauto end |]).
destruct Hin. }
split; [rewrite (HK4 (23%bv : bv 5) ltac:(vm_compute; reflexivity)), (HK3 (23%bv : bv 5) ltac:(cbv; tauto)); exact R23b|].
split; [exact R21d|].
split; [rewrite (HK4 (12%bv : bv 5) ltac:(vm_compute; reflexivity)); exact R12c|].
split; [exact R13d|].
split; [rewrite (HK4 (11%bv : bv 5) ltac:(vm_compute; reflexivity)), (HK3 (11%bv : bv 5) ltac:(cbv; tauto)), (HK2 (11%bv : bv 5) ltac:(vm_compute; reflexivity)); exact R11a|].
split; [intros a Ha; rewrite (Hm4 a Ha); exact (Hm13 a Ha)|].
intros a Ha. apply Hp4. apply Hp3. apply Hp2. apply Hp1. exact Ha.
Qed.
