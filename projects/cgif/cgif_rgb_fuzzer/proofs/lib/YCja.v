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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfx YCe9 YCey.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YP14 YI08 YI0c YI0g YI0d YI0f YCi1 YCia.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM00 YM04 YM01 YM02 YM03 YM06 YI0a.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCji.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition LDH_HEAD : Z := 0x83f24.
Definition LDH_FEQ : Z := 0x83f60.
Definition LDH_CLAMP : Z := 0x83fc4.
Definition LDH_TAIL : Z := 0x83fa4.
Definition LDH_BNE : Z := 0x83fb0.
Definition LDH_EXIT : Z := 0x84808.
Definition LDH_KEEP : list (bv 5) := [1; 2; 3; 4; 5; 6; 7; 8; 9; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LDH_KEEPA : list (bv 5) := [1; 2; 3; 4; 5; 6; 7; 8; 9; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LDH_FKEEP : list (bv 5) := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LDT_KEEP : list (bv 5) := [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 26; 27; 28; 29; 30]%bv.
Lemma ldh_keep_cases : forall r : bv 5, In r LDH_KEEP -> r = 18%bv \/ In r LDH_KEEPA.
Proof. intros r H. cbv [LDH_KEEP In] in H. cbv [LDH_KEEPA In]. repeat (destruct H as [<-|H]; [tauto|]). destruct H. Qed.
Section b.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trbsegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trbsegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)) (k : Z).
Variables (lyc : alayout) (Sc : astate) (W : world trbsegs).
Variables (s1v flt nF pimg pg pn i : Z).
Hypothesis HinF : In (flt, nF) (ablocks B lyc Sc).
Hypothesis HinG : In (pg, pn) (ablocks B lyc Sc). Hypothesis HG0 : pg <= pimg. Hypothesis HG1 : pimg + i < pg + pn.
Hypothesis HFG : (flt, nF) <> (pg, pn).
Hypothesis Hi : 0 <= i < 2 ^ 29.
Hypothesis Hs1lo : sp0 - STK <= s1v. Hypothesis Hs1hi : s1v + 408 <= sp0.
Hypothesis HGW : forall blc lyq ownq j, In (pg, pn) blc -> 0 <= j < req_size pn -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq ownq (pg + j).
Definition ldh_base (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k /\ frm_zero (@fp_csr fy) /\ getr regs 27 = w64 SB /\ getr regs 9 = w64 s1v.
Definition ldh_Bx : sv := SOff 27 0.
Definition ldh_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Lemma ldh_stack : forall fy regs mem md, ldh_base fy regs mem md -> 2 ^ 46 <= s1v /\ s1v + 408 <= 2 ^ 47 /\ alloc_ceiling <= s1v.
Proof.
intros fy regs mem md (HJ & _). pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
clear - Hs1lo Hs1hi Hstk0 Hceil Hslo Hshi H47 C1. lia.
Qed.
Definition LDH_post (fmt : Z) (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : world trbsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md' (tr : bool),
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 (if tr then LDH_TAIL else LDH_CLAMP)) mem' (seg_rom trbsegs)) md' /\
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k /\ frm_zero (@fp_csr fy') /\
(if tr then fmt = 4 /\ getr regs' 13 = w64 (i + 1)
else getr regs' 11 = w64 (fmt * i) /\ getr regs' 12 = w64 3 /\ getr regs' 13 = getr regs 31) /\
(forall r : bv 5, In r LDH_KEEP -> getr regs' r = getr regs r) /\
(forall r : bv 5, In r LDH_FKEEP -> reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (pimg + i <= a < pimg + i + 1) -> aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Definition ss_LDH3 : sstate := mkSS LDH_HEAD (sr_set sr_atoms 18%bv (SLit 3)) [] None (mkFacts [ (25%nat, mkAF 0 (2^29) 0); (27%nat, mkAF SB SB 0) ] [] []).
Lemma LDH_head3 : forall (fy : FPState) (regs : bvmap 5 word) mem md,
ldh_base fy regs mem md -> getr regs 18 = w64 3 -> getr regs 25 = w64 i ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDH_HEAD) mem (seg_rom trbsegs)) md) (LDH_post 3 fy regs mem).
Proof.
intros fy regs mem md HB G18 G25.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof HB as (HJ & Hfrm & G27 & G9).
set (E := Ereg regs []).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (U25 : bv_unsigned (ew E 25) = i) by (rewrite (HE0 25%nat 25%bv eq_refl), G25; apply unsigned_lit_small; clear - Hi; lia).
assert (E27 : ew E 27 = w64 SB) by (rewrite (HE0 27%nat 27%bv eq_refl); exact G27).
assert (HS : @st_ok trbsegs fy E ss_LDH3 (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LDH_HEAD) mem (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LDH3. apply (entry_st_ok_full trbsegs).
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X |]. rewrite G18. cbn [sv_denot]. reflexivity.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn. exact I.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E. rewrite U25, E27. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
rewrite !Z.pow_0_r, !Z.mod_1_r. clear - Hi. unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok trbsegs ldh_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
assert (HAE : env_agree 32 E E) by (apply env_agree_refl).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 LDH_HEAD) mem (seg_rom trbsegs))) in HJ, SHOK.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK ldh_Bspan LDH_CLAMP. { apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 32 E Ey) by (env_agree_chain HAE) end.
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regs _ LDH_KEEPA HS HAEy ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trbsegs (w_H W) _ _ ms HS eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. exists fy, (ms_regs ms), (ms_mem ms). eexists. exists false. split; [reflexivity|]. split; [exact HJ|]. split; [exact Hfrm|].
split.
{ split; [|split].
- rewrite (st_ok_restrict_reg trbsegs (w_H W) _ _ ms (11%bv : bv 5) HS).
lazymatch goal with |- sv_denot ?Ey (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v; try rewrite (sv_denot_agree 32 E Ey v HAEy ltac:(vm_compute; reflexivity)) end.
unfold w64. apply lg_denot_of_U. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SLit, U_SOff, U25, Z.add_0_r.
rewrite (zcanon_id 3), (zcanon_id i) by (unfold M64; clear - Hi; lia). apply zcanon_id. unfold M64. clear - Hi. lia.
- rewrite (st_ok_restrict_reg trbsegs (w_H W) _ _ ms (12%bv : bv 5) HS). reflexivity.
- rewrite (st_ok_restrict_reg trbsegs (w_H W) _ _ ms (13%bv : bv 5) HS).
lazymatch goal with |- sv_denot ?Ey (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v; try rewrite (sv_denot_agree 32 E Ey v HAEy ltac:(vm_compute; reflexivity)) end.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (HE0 31%nat 31%bv eq_refl). }
split.
{ intros r Hr. destruct (ldh_keep_cases r Hr) as [-> | Hr0]; [|exact (HKR r Hr0)].
rewrite (st_ok_restrict_reg trbsegs (w_H W) _ _ ms (18%bv : bv 5) HS), G18. reflexivity. }
split; [intros r Hr; reflexivity|].
split; [intros x Hx _; exact (lg_kept_ro _ _ _ _ _ HFr ltac:(intros rr []) x Hx) | intros x Hx; exact (apresent_grows _ _ _ _ HG Hx)].
Qed.
Definition ldh4_mem : smem :=
[ YQ0b.mkRegion (Some 33%nat) 0 4 0 0 [YQ0b.mkChunk 0 (CVal 4 (SOff 32 0))];
YQ0b.mkRegion (Some 9%nat) 312 408 0 0 [YQ0b.mkChunk 312 (CVal 8 (SOff 38 0)); YQ0b.mkChunk 400 (CVal 8 (SLit 1))];
YQ0b.mkRegion (Some 39%nat) 0 1 0 1 [] ].
Definition ldh4_al1 : sv := SAlu ALU_ADD (SOff 23 12) (SAlu ALU_SLL (SOff 25 0) (SLit 4)).
Definition ldh4_al2 : sv := SAlu ALU_ADD (SOff 25 0) (SOff 38 0).
Definition ldh4_facts : facts :=
mkFacts [ (9%nat, mkAF (2^46) (2^47) 0); (25%nat, mkAF 0 (2^29) 0); (22%nat, mkAF (2^64 - 1 - 140737479966720) (2^64 - 1 - 4096) 0);
(23%nat, mkAF 4096 140737479966720 4); (27%nat, mkAF SB SB 0); (32%nat, mkAF 0 (2^32 - 1) 0); (33%nat, mkAF 4096 140737479966720 2);
(38%nat, mkAF 4096 140737479966720 0); (39%nat, mkAF 4096 140737479966720 0) ]
[ mkAC BC_GEU (SOff 39 0) (SOff 38 0) ] [ (ldh4_al1, SOff 33 0); (ldh4_al2, SOff 39 0) ].
Definition ldh4_regs := sr_set sr_atoms 18%bv (SLit 4).
Definition ss_LDH4x : sstate := mkSS LDH_HEAD ldh4_regs ldh4_mem None ldh4_facts.
Definition ldh4_SH : list shent := [ mkSHE 33 0 4; mkSHE 39 0 1 ].
Lemma ldh4_rs : forall rr, In rr ldh4_mem ->
YQ0b.r_whi rr <= YQ0b.r_wlo rr \/ (YQ0b.r_base rr = Some 39%nat /\ 0 <= YQ0b.r_wlo rr /\ YQ0b.r_whi rr <= 1).
Proof. intros rr [<- | [<- | [<- | []]]]; cbn; first [left; lia | right; repeat split; lia]. Qed.
Lemma LDH_head4 : forall (fy : FPState) (regs : bvmap 5 word) mem md,
ldh_base fy regs mem md -> 4 * (4 * i + 3) + 4 <= nF ->
getr regs 18 = w64 4 -> getr regs 25 = w64 i -> getr regs 23 = w64 flt -> getr regs 22 = w64 (2 ^ 64 - 1 - flt) ->
val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 312) 8 pimg -> val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 400) 8 1 ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDH_HEAD) mem (seg_rom trbsegs)) md) (LDH_post 4 fy regs mem).
Proof.
intros fy regs mem md HB Hlen G18 G25 G23 G22 V312 V400.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof (ldh_stack fy regs mem md HB) as Rs1. pose proof asan_consts as (C1 & _).
pose proof HB as (HJ & Hfrm & G27 & G9). pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (Qf16 & Qf0 & Qf1 & _ & Hfpres & _ & Hnf0).
pose proof (req_size_pos nF ltac:(lia)) as [_ QnF].
destruct (al_blocks _ _ LAWS _ _ _ _ _ pg pn HAR HinG) as (_ & Qg0 & Qg1 & _ & Hgpres & _ & Hpn0).
pose proof (req_size_pos pn ltac:(lia)) as [_ Qpn].
pose proof (sep_blocks trbsegs _ LAWS lyc Sc _ _ _ flt nF pg pn HAR HinF HinG HFG) as Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
destruct (val_mem_of_present4 trbsegs (mrestrict (w_H W) mem) (flt + 16 * i + 12)) as (av & Hav & Vav).
{ intros j Hj. destruct (proj1 (Hfpres (flt + 16 * i + 12 + j) ltac:(clear - Hj Hi Hlen QnF; lia))) as (Hhid & bb & Hbb).
exists bb. unfold mbyte, mrestrict. rewrite Hhid, Hbb. reflexivity. }
set (E0 := Ereg regs (map (Z_to_bv 64) [av; flt + 16 * i + 12; 0; 0; 0; 0; pimg; pimg + i] ++ [])).
set (E := ew_fregs E0 64 (@fp_regs fy)).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E0 j = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall j x, nth_error [av; flt + 16 * i + 12; 0; 0; 0; 0; pimg; pimg + i] j = Some x -> ew E0 (32 + j) = Z_to_bv 64 x) by (intros j x Hj; subst E0; apply Ereg_vals; exact Hj).
assert (HEE : forall j, (j < 64)%nat -> ew E j = ew E0 j) by (intros j Hj; subst E; apply ew_fregs_low; exact Hj).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr).
{ intros j rr Hj. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5. rewrite HEE by lia. apply HE0. exact Hj. }
assert (HEF : forall r : bv 5, ew E (64 + ridx r)%nat = reg_get (@fp_regs fy) r) by (intros r; subst E; apply ew_fregs_at).
assert (Rpi : 4096 <= pimg /\ pimg + i < 140737479966720) by (clear - HG0 HG1 Hi Qg0 Qg1 Qpn C1; lia).
assert (Rfl : 4096 <= flt /\ flt + 16 * i + 16 <= 140737479966720) by (clear - Hi Hlen Qf0 Qf1 QnF C1; lia).
assert (U9 : bv_unsigned (ew E0 9) = s1v) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Rs1; lia).
assert (U25 : bv_unsigned (ew E0 25) = i) by (rewrite (HE0 25%nat 25%bv eq_refl), G25; apply unsigned_lit_small; clear - Hi; lia).
assert (U22 : bv_unsigned (ew E0 22) = 2 ^ 64 - 1 - flt) by (rewrite (HE0 22%nat 22%bv eq_refl), G22; apply unsigned_lit_small; clear - Rfl Hi; lia).
assert (U23 : bv_unsigned (ew E0 23) = flt) by (rewrite (HE0 23%nat 23%bv eq_refl), G23; apply unsigned_lit_small; clear - Rfl Hi; lia).
assert (E27 : ew E0 27 = w64 SB) by (rewrite (HE0 27%nat 27%bv eq_refl); exact G27).
assert (A32 : bv_unsigned (ew E0 32) = av) by (pose proof (HV 0%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hav; lia).
assert (A33 : bv_unsigned (ew E0 33) = flt + 16 * i + 12) by (pose proof (HV 1%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Rfl Hi; lia).
assert (A38 : bv_unsigned (ew E0 38) = pimg) by (pose proof (HV 6%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Rpi Hi; lia).
assert (A39 : bv_unsigned (ew E0 39) = pimg + i) by (pose proof (HV 7%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Rpi Hi; lia).
assert (DN : forall j x, bv_unsigned (ew E0 j) = x -> sv_denot E0 (SOff j 0) = Z_to_bv 64 x) by (intros j x Hj; cbn [sv_denot]; rewrite Hj, Z.add_0_r; reflexivity).
assert (Hf4 : (flt + 16 * i + 12) mod 4 = 0).
{ replace (flt + 16 * i + 12) with (flt + (4 * i + 3) * 4) by lia. rewrite Z.mod_add by lia.
clear - Qf16. pose proof (Z.div_mod flt 16 ltac:(lia)). replace flt with (4 * (4 * (flt / 16))) by lia. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
assert (HS0 : @st_ok trbsegs fy E0 ss_LDH4x (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LDH_HEAD) mem (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LDH4x, ldh4_regs. apply (entry_st_ok_full trbsegs).
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X |]. rewrite G18. cbn [sv_denot]. reflexivity.
- vm_compute. reflexivity.
- unfold ldh4_mem. repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite A33.
split; [clear - Rfl Hi; lia|]. split; [clear - Rfl; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trbsegs E0 _ (flt + 16 * i + 12) 0 4 _ av); [exact (DN _ _ A32) | zside | zside | rewrite Z.add_0_r; exact Vav].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite U9.
split; [clear - Rs1; lia|]. split; [clear - Rs1; lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
* apply (chunk_ok_val trbsegs E0 _ s1v 312 8 _ pimg); [exact (DN _ _ A38) | zside | zside | exact V312].
* apply (chunk_ok_val trbsegs E0 _ s1v 400 8 _ 1); [cbn [sv_denot]; reflexivity | zside | zside | exact V400].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite A39.
split; [clear - Rpi Hi; lia|]. split; [clear - Rpi; lia|]. split; [|apply Forall_nil].
intros o Ho. apply (apresent_writable trbsegs). apply (proj1 (Hgpres (pimg + i + o) ltac:(clear - Ho HG0 HG1 Hi Qpn; lia))).
- apply pairwise_disjoint_of_extents. unfold ldh4_mem, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. change (Ereg regs _) with E0. rewrite A33, U9, A39.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. clear - Rs1 Rpi Rfl C1 HG0 HG1 Hi Hlen Qf0 Qf1 Qg0 Qg1 Qpn QnF Hsep. repeat split; lia.
- split; [|split; [split; [|exact I] | split; [|split; [|exact I]]]].
+ cbn [f_atoms atoms_ok ldh4_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (Ereg regs _) with E0.
rewrite U9, U25, U22, U23, E27, A32, A33, A38, A39. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - Rs1 Hi Rpi Rfl Hav Hf4 Qf16. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
+ unfold acond_ok. cbn [ac_c ac_a ac_b]. change (Ereg regs _) with E0. rewrite YO3v.branch_geu_U, !U_SOff, A38, A39, !Z.add_0_r.
rewrite !zcanon_id by (unfold M64; clear - Rpi Hi; lia). apply Bool.negb_true_iff, Z.ltb_ge. clear - Hi. lia.
+ change (Ereg regs _) with E0. unfold ldh4_al1. apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, U23, U25, A33, !Z.add_0_r.
rewrite (zcanon_id (flt + 12)), (zcanon_id i) by (unfold M64; clear - Rfl Hi; lia). change (Z.land (zcanon 4) 63) with 4.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16. rewrite (zcanon_id (i * 16)) by (unfold M64; clear - Hi; lia). f_equal. lia.
+ change (Ereg regs _) with E0. unfold ldh4_al2. apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U25, A38, A39, !Z.add_0_r.
rewrite (zcanon_id i), (zcanon_id pimg) by (unfold M64; clear - Rpi Hi; lia). f_equal. lia. }
assert (SHOK0 : sh_ok trbsegs ldh_Bx ldh4_SH E0 (mrestrict (w_H W) mem)).
{ unfold sh_ok, ldh4_SH. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range trbsegs (w_H W) mem E0 ldh_Bx 33 (flt + 16 * i + 12) 4 (flt + 16 * i + 12) 0 4).
+ apply (range_addressable_of_block trbsegs B LAWS lyc Sc W mem md flt nF _ _ HAR HinF); clear - Hi Hlen QnF; lia.
+ unfold U, ldh_Bx. cbn [sv_denot]. rewrite E27, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A33.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ flt nF HAR HinF) as Himg.
revert Hy Hia Himg Hi Hlen QnF Qf0 Qf1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia.
- apply (shent_ok_of_range trbsegs (w_H W) mem E0 ldh_Bx 39 (pimg + i) 1 (pimg + i) 0 1).
+ apply (range_addressable_of_block trbsegs B LAWS lyc Sc W mem md pg pn _ _ HAR HinG); clear - HG0 HG1 Hi Qpn; lia.
+ unfold U, ldh_Bx. cbn [sv_denot]. rewrite E27, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A39.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ pg pn HAR HinG) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ pg pn HAR HinG) as Himg.
revert Hy Hia Himg HG0 HG1 Hi Qpn Qg0 Qg1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia. }
pose proof (st_ok_enterF trbsegs fy 64 E0 ss_LDH4x _ HS0 ltac:(vm_compute; reflexivity) Hfrm) as HS.
pose proof (sh_ok_agree trbsegs ldh_Bx ldh4_SH 64 E0 E _ (env_agree_ew_fregs E0 64 _) ltac:(vm_compute; reflexivity) SHOK0) as SHOK.
change (ew_fregs E0 64 (@fp_regs fy)) with E in HS. clear HS0 SHOK0.
assert (HU39 : bv_unsigned (ew E 39) = pimg + i) by (rewrite HEE by lia; exact A39).
assert (HU25 : bv_unsigned (ew E 25) = i) by (rewrite HEE by lia; exact U25).
assert (HAE96 : env_agree 96 E E) by (apply env_agree_refl).
assert (AWR : forall Ex cs1 cs2 cs3, bv_unsigned (ew Ex 39) = pimg + i ->
awr_ok Ex [YQ0b.mkRegion (Some 33%nat) 0 4 0 0 cs1; YQ0b.mkRegion (Some 9%nat) 312 408 0 0 cs2; YQ0b.mkRegion (Some 39%nat) 0 1 0 1 cs3]
STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own).
{ intros Ex cs1 cs2 cs3 HUx. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
eapply awr_ok_cons_gen; [reflexivity | exact HUx | | apply awr_ok_nil].
cbn [YQ0b.r_wlo YQ0b.r_whi]. intros a Ha. replace a with (pg + (a - pg)) by lia. apply HGW; [exact HinG | clear - Ha HG0 HG1 Hi Qpn; lia]. }
aj_run_to_tokF trbtbl_lib_ok HS HJ SHOK ldh_Bspan LDH_FEQ. { cbn [ss_mem]. unfold ldh4_mem. apply AWR. exact HU39. }
rename HFr into HFr1; rename HG into HGr1; clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msA := msx) in * end.
assert (KW1 : forall a, 0 <= a < 2 ^ 64 -> ~ (pimg + i <= a < pimg + i + 1) -> aview trbsegs (w_H W) (ms_mem msA) a = aview trbsegs (w_H W) mem a).
{ intros a Ha Hnw. apply (lg_kept_win _ _ _ _ _ 39%nat (pimg + i) 0 1 HFr1); [exact ldh4_rs | exact HU39 | exact Ha | clear - Hnw; lia]. }
lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
lazymatch type of HS with st_okF _ ?Ex ?ssx ?msx =>
assert (HFK : forall r : bv 5, In r LDH_FKEEP -> reg_get (ms_fregs msx) r = reg_get (@fp_regs fy) r)
by (apply (st_okF_fregs_kept trbsegs Ex ssx msx 64 (@fp_regs fy) LDH_FKEEP HS);
[ intros r; first [ apply HEF | rewrite (proj1 HAEx) by (pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5; unfold ridx; lia); apply HEF ]
| vm_compute; reflexivity ]) end.
lg_branchF trbtbl_lib_ok HS.
all: pose proof (st_okF_frm trbsegs _ _ _ HS) as Hfrm'; pose proof (st_okF_to_legacy trbsegs _ _ _ HS) as HSL; clear HS.
all: lazymatch type of HSL with st_ok _ ?Ex _ _ => assert (U39X : bv_unsigned (ew Ex 39) = pimg + i) by (rewrite (proj1 HAEx) by lia; exact HU39);
assert (U25X : bv_unsigned (ew Ex 25) = i) by (rewrite (proj1 HAEx) by lia; exact HU25) end.
-
aj_run_to_tok trbtbl_lib_ok HSL HJ SHOK ldh_Bspan LDH_CLAMP. { apply AWR. exact U39X. }
lazymatch type of HSL with st_ok _ _ _ (restrict _ ?msx) => rename msx into msZ end.
lazymatch type of HSL with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 96 E Ey) by (env_agree_chain HAEx) end.
lazymatch type of HSL with st_ok _ ?Ey _ _ =>
assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) [av; flt + 16 * i + 12; 0; 0; 0; 0; pimg; pimg + i] ++ [])) Ey)
by (destruct HAEy as [EA ED]; split; [intros j Hj; rewrite EA by lia; subst E; rewrite ew_fregs_low by lia; reflexivity | rewrite ED; reflexivity]) end.
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regs _ LDH_KEEPA HSL HAE' ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trbsegs (w_H W) _ _ msZ HSL eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. lazymatch type of HSL with @st_ok _ ?fz _ _ _ => exists fz end. exists (ms_regs msZ), (ms_mem msZ). eexists. exists false. split; [reflexivity|]. split; [exact HJ|]. split; [exact Hfrm'|].
split.
{ split; [|split].
- rewrite (st_ok_restrict_reg trbsegs (w_H W) _ _ msZ (11%bv : bv 5) HSL).
lazymatch goal with |- sv_denot ?Ey (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end.
unfold w64. apply lg_denot_of_U. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SLit, U_SOff, (proj1 HAEy), HU25, Z.add_0_r by lia.
rewrite (zcanon_id 4), (zcanon_id i) by (unfold M64; clear - Hi; lia). apply zcanon_id. unfold M64. clear - Hi. lia.
- rewrite (st_ok_restrict_reg trbsegs (w_H W) _ _ msZ (12%bv : bv 5) HSL). reflexivity.
- rewrite (st_ok_restrict_reg trbsegs (w_H W) _ _ msZ (13%bv : bv 5) HSL).
lazymatch goal with |- sv_denot ?Ey (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (proj1 HAEy) by lia. exact (HE 31%nat 31%bv eq_refl). }
split.
{ intros r Hr. destruct (ldh_keep_cases r Hr) as [-> | Hr0]; [|exact (HKR r Hr0)].
rewrite (st_ok_restrict_reg trbsegs (w_H W) _ _ msZ (18%bv : bv 5) HSL), G18. reflexivity. }
split; [exact HFK|].
split; [| intros x Hx; apply (apresent_grows _ _ _ _ HG); exact (apresent_grows _ _ _ _ HGr1 Hx)].
intros x Hx Hnw. rewrite (lg_kept_win _ _ _ _ _ 39%nat (pimg + i) 0 1 HFr ltac:(exact ldh4_rs) U39X x Hx ltac:(clear - Hnw; lia)). exact (KW1 x Hx Hnw).
-
aj_run_to_tok trbtbl_lib_ok HSL HJ SHOK ldh_Bspan LDH_TAIL. { apply AWR. exact U39X. }
lazymatch type of HSL with st_ok _ _ _ (restrict _ ?msx) => rename msx into msZ end.
lazymatch type of HSL with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 96 E Ey) by (env_agree_chain HAEx) end.
lazymatch type of HSL with st_ok _ ?Ey _ _ =>
assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) [av; flt + 16 * i + 12; 0; 0; 0; 0; pimg; pimg + i] ++ [])) Ey)
by (destruct HAEy as [EA ED]; split; [intros j Hj; rewrite EA by lia; subst E; rewrite ew_fregs_low by lia; reflexivity | rewrite ED; reflexivity]) end.
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regs _ LDH_KEEPA HSL HAE' ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HSL with st_ok _ ?Ey _ _ => assert (U39Y : bv_unsigned (ew Ey 39) = pimg + i) by (rewrite (proj1 HAEy) by lia; exact HU39) end.
rewrite (st_ok_restrict_mkst trbsegs (w_H W) _ _ msZ HSL eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. lazymatch type of HSL with @st_ok _ ?fz _ _ _ => exists fz end. exists (ms_regs msZ), (ms_mem msZ). eexists. exists true. split; [reflexivity|]. split; [exact HJ|]. split; [exact Hfrm'|].
split.
{ split; [reflexivity|].
rewrite (st_ok_restrict_reg trbsegs (w_H W) _ _ msZ (13%bv : bv 5) HSL).
lazymatch goal with |- sv_denot ?Ey (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end.
cbn [sv_denot]. rewrite (proj1 HAEy), HU25 by lia. reflexivity. }
split.
{ intros r Hr. destruct (ldh_keep_cases r Hr) as [-> | Hr0]; [|exact (HKR r Hr0)].
rewrite (st_ok_restrict_reg trbsegs (w_H W) _ _ msZ (18%bv : bv 5) HSL), G18. reflexivity. }
split; [exact HFK|].
split; [| intros x Hx; apply (apresent_grows _ _ _ _ HG); exact (apresent_grows _ _ _ _ HGr1 Hx)].
intros x Hx Hnw. rewrite (lg_kept_win _ _ _ _ _ 39%nat (pimg + i) 0 1 HFr ltac:(exact ldh4_rs) U39Y x Hx ltac:(clear - Hnw; lia)). exact (KW1 x Hx Hnw).
Qed.
Definition ldt_mem : smem := [ YQ0b.mkRegion (Some 9%nat) 384 392 0 0 [YQ0b.mkChunk 384 (CVal 8 (SOff 35 0))] ].
Definition ss_LDT : sstate := mkSS LDH_TAIL sr_atoms ldt_mem None (mkFacts [ (9%nat, mkAF (2^46) (2^47) 0); (27%nat, mkAF SB SB 0) ] [] []).
Lemma ldt_rs_ro : forall rr, In rr ldt_mem -> YQ0b.r_whi rr <= YQ0b.r_wlo rr.
Proof. intros rr [<- | []]. cbn. lia. Qed.
Definition LDT_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (pc m1 i1 : Z) : world trbsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (@mkst fy regs' (Z_to_bv 64 pc) mem' (seg_rom trbsegs)) md' /\
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k /\
getr regs' 31 = w64 m1 /\ getr regs' 25 = w64 i1 /\
(forall r : bv 5, In r LDT_KEEP -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Lemma LDH_tail : forall (fy : FPState) (regs : bvmap 5 word) mem md (m fmt i1 N : Z),
ldh_base fy regs mem md -> getr regs 31 = w64 m -> getr regs 18 = w64 fmt -> getr regs 13 = w64 i1 ->
0 <= m < 2 ^ 62 -> 0 <= fmt < 2 ^ 62 -> 0 <= i1 < 2 ^ 64 -> 0 <= N < 2 ^ 64 ->
val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 384) 8 N ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LDH_TAIL) mem (seg_rom trbsegs)) md)
(LDT_post fy regs mem (if i1 =? N then LDH_EXIT else LDH_HEAD) (m + fmt) i1).
Proof.
intros fy regs mem md m fmt i1 N HB G31 G18 G13 Hm Hfmt Hi1 HN Vslot.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof (ldh_stack fy regs mem md HB) as Rs1. pose proof asan_consts as (C1 & _).
pose proof HB as (HJ & Hfrm & G27 & G9).
set (E := Ereg regs (map (Z_to_bv 64) [0; 0; 0; N] ++ [])).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j x, nth_error [0; 0; 0; N] j = Some x -> ew E (32 + j) = Z_to_bv 64 x) by (intros j x Hj; subst E; apply Ereg_vals; exact Hj).
assert (U31 : bv_unsigned (ew E 31) = m) by (rewrite (HE0 31%nat 31%bv eq_refl), G31; apply unsigned_lit_small; clear - Hm; lia).
assert (U18 : bv_unsigned (ew E 18) = fmt) by (rewrite (HE0 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; clear - Hfmt; lia).
assert (U13 : bv_unsigned (ew E 13) = i1) by (rewrite (HE0 13%nat 13%bv eq_refl), G13; apply unsigned_lit_small; exact Hi1).
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Rs1; lia).
assert (UN : bv_unsigned (ew E 35) = N) by (pose proof (HV 3%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; exact HN).
assert (E27 : ew E 27 = w64 SB) by (rewrite (HE0 27%nat 27%bv eq_refl); exact G27).
assert (HS : @st_ok trbsegs fy E ss_LDT (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LDH_TAIL) mem (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LDT. apply (entry_st_ok_full trbsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold ldt_mem. apply Forall_cons; [|apply Forall_nil].
unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E. rewrite U9.
split; [clear - Rs1; lia|]. split; [clear - Rs1; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trbsegs E _ s1v 384 8 _ N); [cbn [sv_denot]; rewrite UN, Z.add_0_r; reflexivity | zside | zside | exact Vslot].
- apply pairwise_disjoint_of_extents. cbn. repeat split.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E. rewrite U9, E27. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
rewrite !Z.pow_0_r, !Z.mod_1_r. clear - Rs1. unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok trbsegs ldh_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
assert (HAE : env_agree 36 E E) by (apply env_agree_refl).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 LDH_TAIL) mem (seg_rom trbsegs))) in HJ, SHOK.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK ldh_Bspan LDH_BNE. { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr1; rename HG into HGr1; clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msA := msx) in * end.
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAEx : env_agree 36 E Ex) by (env_agree_chain HAE) end.
assert (KW1 : forall x, 0 <= x < 2 ^ 64 -> aview trbsegs (w_H W) (ms_mem msA) x = aview trbsegs (w_H W) mem x) by (exact (lg_kept_ro _ _ _ _ _ HFr1 ldt_rs_ro)).
assert (FIN : forall E' ss' ms' md' pc', @st_ok trbsegs fy E' ss' (restrict (w_H W) ms') -> env_agree 36 E E' ->
ss_pc ss' = pc' -> ss_resv ss' = None ->
(sr_get (ss_regs ss') 31 = SAlu ALU_ADD (SOff 31 0) (SOff 18 0) \/ sr_get (ss_regs ss') 31 = SAlu ALU_ADD (SOff 18 0) (SOff 31 0)) ->
sr_get (ss_regs ss') 25 = SOff 13 0 ->
forallb (fun rr : bv 5 => sv_eqb (sr_get (ss_regs ss') rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) LDT_KEEP = true ->
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') md' k ->
(forall x, 0 <= x < 2 ^ 64 -> aview trbsegs (w_H W) (ms_mem ms') x = aview trbsegs (w_H W) mem x) ->
(forall x, apresent (w_H W) mem x -> apresent (w_H W) (ms_mem ms') x) ->
SRr trbsegs W (mkCfg ms' md') (LDT_post fy regs mem pc' (m + fmt) i1)).
{ intros E' ss' ms' md' pc' HS' [EA ED] Hpc' Hrv' Q31 Q25 QK HJ' Hk' Hp'.
assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) [0; 0; 0; N] ++ [])) E') by (split; [intros j Hj; rewrite EA by lia; reflexivity | rewrite ED; reflexivity]).
pose proof (regs_kept_of_st_ok trbsegs E' ss' _ regs _ LDT_KEEP HS' HAE' QK) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trbsegs (w_H W) E' ss' ms' HS' Hrv'), Hpc'. apply SRr_ret.
split; [reflexivity|]. exists (ms_regs ms'), (ms_mem ms'), md'. split; [reflexivity|]. split; [exact HJ'|].
split.
{ rewrite (st_ok_restrict_reg trbsegs (w_H W) E' ss' ms' (31%bv : bv 5) HS').
destruct Q31 as [-> | ->]; apply lg_denot_of_U; rewrite U_SAlu; cbn [zalu_raw]; rewrite !U_SOff, !EA, U31, U18, !Z.add_0_r by lia;
rewrite (zcanon_id fmt), (zcanon_id m) by (unfold M64; clear - Hm Hfmt; lia); rewrite zcanon_id by (unfold M64; clear - Hm Hfmt; lia); lia. }
split.
{ rewrite (st_ok_restrict_reg trbsegs (w_H W) E' ss' ms' (25%bv : bv 5) HS'), Q25. cbn [sv_denot]. rewrite EA, U13, Z.add_0_r by lia. reflexivity. }
split; [exact HKR|]. split; [exact Hk' | exact Hp']. }
srr_branch_tok trbtbl_lib_ok HS SHOK ldh_Bspan.
- rewrite branch_ne_U, !U_SOff in Hc. rewrite ?(proj1 HAEx) in Hc by lia. rewrite U13, UN, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
apply Bool.negb_true_iff in Hc. rewrite Hc.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK ldh_Bspan LDH_HEAD. { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 36 E Ey) by (env_agree_chain HAEx) end.
apply (FIN _ _ _ _ LDH_HEAD HS HAEy); [reflexivity | reflexivity | first [left; reflexivity | right; reflexivity] | reflexivity | vm_compute; reflexivity | exact HJ | | ].
+ intros x Hx. rewrite (lg_kept_ro _ _ _ _ _ HFr ldt_rs_ro x Hx). exact (KW1 x Hx).
+ intros x Hx. apply (apresent_grows _ _ _ _ HG). exact (apresent_grows _ _ _ _ HGr1 Hx).
- rewrite branch_ne_U, !U_SOff in Hc. rewrite ?(proj1 HAEx) in Hc by lia. rewrite U13, UN, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
apply Bool.negb_false_iff in Hc. rewrite Hc.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK ldh_Bspan LDH_EXIT. { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 36 E Ey) by (env_agree_chain HAEx) end.
apply (FIN _ _ _ _ LDH_EXIT HS HAEy); [reflexivity | reflexivity | first [left; reflexivity | right; reflexivity] | reflexivity | vm_compute; reflexivity | exact HJ | | ].
+ intros x Hx. rewrite (lg_kept_ro _ _ _ _ _ HFr ldt_rs_ro x Hx). exact (KW1 x Hx).
+ intros x Hx. apply (apresent_grows _ _ _ _ HG). exact (apresent_grows _ _ _ _ HGr1 Hx).
Qed.
End b.
