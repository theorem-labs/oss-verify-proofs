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
Definition LNP_HEAD : Z := 0x84108.
Definition LNP_BR0 : Z := 0x8410c.
Definition LNP_AA : Z := 0x84110.
Definition LNP_AABR : Z := 0x84138.
Definition LNP_AN : Z := 0x84144.
Definition LNP_ANBR : Z := 0x84148.
Definition LNP_AC0 : Z := 0x8414c.
Definition LNP_AC0BR : Z := 0x841a0.
Definition LNP_AC1 : Z := 0x841a4.
Definition LNP_AC1BR : Z := 0x841f8.
Definition LNP_AC2 : Z := 0x841fc.
Definition LNP_AC2BR : Z := 0x84250.
Definition LNP_DESC : Z := 0x84254.
Definition LNP_STORE : Z := 0x84280.
Definition LNP_CLOB : list (bv 5) := [5; 6; 7; 12; 13]%bv.
Definition LNP_KEEP : list (bv 5) := [1; 2; 3; 4; 8; 9; 10; 11; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LNP_FKEEP : list (bv 5) := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma lnp_clob_cases : forall r : bv 5, reg_in r LNP_CLOB = false -> r = 0%bv \/ In r LNP_KEEP.
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
Variables (flt nF s1v : Z).
Hypothesis HinF : In (flt, nF) (ablocks B lyc Sc).
Hypothesis Hs1lo : sp0 - STK <= s1v. Hypothesis Hs1hi : s1v + 384 <= sp0.
Definition lnp_base (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k /\
frm_zero (@fp_csr fy) /\ getr regs 31 = w64 flt /\ getr regs 25 = w64 SB /\ getr regs 9 = w64 s1v.
Definition LNP_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (pc : Z) (Q : bvmap 5 word -> Prop) : world trasegs -> config -> Prop :=
fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 pc) mem' (seg_rom trasegs)) md' /\
lnp_base fy' regs' mem' md' /\ Q regs' /\
(forall r : bv 5, In r LNP_KEEP -> getr regs' r = getr regs r) /\
(forall r : bv 5, In r LNP_FKEEP -> reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Lemma lnp_env : forall fy regs mem md, lnp_base fy regs mem md ->
4096 <= flt /\ flt + req_size nF <= alloc_ceiling /\ flt mod 16 = 0 /\ nF <= req_size nF /\
140735332483072 <= alloc_ceiling <= 140737479966720 /\
2 ^ 46 <= s1v /\ s1v + 384 <= 2 ^ 47 /\ alloc_ceiling <= s1v.
Proof.
intros fy regs mem md (HJ & _). pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (Hf16 & Hf4096 & Hfceil & _ & _ & _ & Hnf0).
pose proof (req_size_pos nF ltac:(lia)) as [_ HrF].
repeat split; try assumption; try lia.
Qed.
Lemma lnp_cell4 : forall x, flt mod 16 = 0 -> (flt + 4 * x) mod 4 = 0.
Proof.
intros x H16. replace (flt + 4 * x) with (flt + x * 4) by lia. rewrite Z.mod_add by lia.
pose proof (Z.mod_pos_bound flt 16 ltac:(lia)). pose proof (Z.div_mod flt 16 ltac:(lia)).
replace flt with (4 * (4 * (flt / 16))) by lia. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity.
Qed.
Lemma lnp_cell_val : forall fy regs mem md x, lnp_base fy regs mem md -> 0 <= x -> 4 * x + 4 <= nF ->
exists v, 0 <= v < 2 ^ 32 /\ val_mem trasegs (mrestrict (w_H W) mem) (flt + 4 * x) 4 v.
Proof.
intros fy regs mem md x HB Hx Hlen. pose proof (lnp_env fy regs mem md HB) as (_ & _ & _ & QnF & _).
pose proof HB as (HJ & _). pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (_ & _ & _ & _ & Hfpres & _).
apply (val_mem_of_present4 trasegs). intros i Hi.
destruct (proj1 (Hfpres (flt + 4 * x + i) ltac:(clear - Hi Hx Hlen QnF; lia))) as (Hhid & bb & Hbb).
exists bb. unfold mbyte, mrestrict. rewrite Hhid, Hbb. reflexivity.
Qed.
Definition lnp_Bx : sv := SOff 25 0.
Definition lnp_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Local Ltac lnp_ro_tac :=
let rr := fresh "rr" in let Hin := fresh "Hin" in
intros rr Hin; cbn [ss_mem add_cond In] in Hin;
repeat (destruct Hin as [<- | Hin]); try contradiction; cbn [YQ0b.r_wlo YQ0b.r_whi]; lia.
Definition ss_LNPA0 : sstate := mkSS LNP_HEAD sr_atoms [] None (mkFacts [ (25%nat, mkAF SB SB 0); (29%nat, mkAF 0 (2^29) 0); (14%nat, mkAF 0 (2^29) 0) ] [] []).
Lemma LNP_A0 : forall (fy : FPState) (regs : bvmap 5 word) mem md (ha fmt i : Z),
lnp_base fy regs mem md -> getr regs 10 = w64 ha -> getr regs 29 = w64 fmt -> getr regs 14 = w64 i ->
0 <= ha < 2 ^ 64 -> 0 <= fmt < 2 ^ 29 -> 0 <= i < 2 ^ 29 ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LNP_HEAD) mem (seg_rom trasegs)) md)
(LNP_post fy regs mem (if ha =? 0 then LNP_AN else LNP_AA) (fun regs' => getr regs' 5 = w64 (fmt * i))).
Proof.
intros fy regs mem md ha fmt i HB G10 G29 G14 Hha Hfmt Hi.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HB as (HJ & Hfrm & G31 & G25 & G9).
set (E := Ereg regs []).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (U10 : bv_unsigned (ew E 10) = ha) by (rewrite (HE0 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; exact Hha).
assert (U29 : bv_unsigned (ew E 29) = fmt) by (rewrite (HE0 29%nat 29%bv eq_refl), G29; apply unsigned_lit_small; lia).
assert (U14 : bv_unsigned (ew E 14) = i) by (rewrite (HE0 14%nat 14%bv eq_refl), G14; apply unsigned_lit_small; lia).
assert (E25 : ew E 25 = w64 SB) by (rewrite (HE0 25%nat 25%bv eq_refl); exact G25).
assert (Hfi : 0 <= fmt * i < 2 ^ 60) by (split; [apply Z.mul_nonneg_nonneg; lia | apply (Z.le_lt_trans _ (2 ^ 29 * 2 ^ 29)); [apply Z.mul_le_mono_nonneg; lia | lia]]).
assert (HS : @st_ok trasegs fy E ss_LNPA0 (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LNP_HEAD) mem (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LNPA0. apply (entry_st_ok_full trasegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn. exact I.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E. rewrite U29, U14, E25. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok trasegs lnp_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
assert (HAE : env_agree 32 E E) by (apply env_agree_refl).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 LNP_HEAD) mem (seg_rom trasegs))) in HJ, SHOK.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK lnp_Bspan LNP_BR0. { apply awr_ok_nil. }
rename HFr into HFr1; rename HG into HG1; clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msA := msx) in * end.
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAEx : env_agree 32 E Ex) by (env_agree_chain HAE) end.
assert (FIN : forall E' ss' ms' md' pc', @st_ok trasegs fy E' ss' (restrict (w_H W) ms') -> env_agree 32 E E' ->
ss_pc ss' = pc' -> ss_resv ss' = None ->
sr_get (ss_regs ss') 5 = SMd M_MUL (SOff 14 0) (SOff 29 0) \/ sr_get (ss_regs ss') 5 = SMd M_MUL (SOff 29 0) (SOff 14 0) ->
forallb (fun rr : bv 5 => sv_eqb (sr_get (ss_regs ss') rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) LNP_KEEP = true ->
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') md' k ->
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) (ms_mem ms') a = aview trasegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms') a) ->
SRr trasegs W (mkCfg ms' md') (LNP_post fy regs mem pc' (fun regs' => getr regs' 5 = w64 (fmt * i)))).
{ intros E' ss' ms' md' pc' HS' [EA ED] Hpc' Hrv' Q5 QK HJ' Hk' Hp'.
assert (HAE' : env_agree 32 (Ereg regs []) E') by (split; [intros j Hj; rewrite EA by lia; reflexivity | rewrite ED; reflexivity]).
pose proof (regs_kept_of_st_ok trasegs E' ss' _ regs _ LNP_KEEP HS' HAE' QK) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trasegs (w_H W) E' ss' ms' HS' Hrv'), Hpc'. apply SRr_ret.
split; [reflexivity|]. exists fy, (ms_regs ms'), (ms_mem ms'), md'. split; [reflexivity|].
split; [split; [exact HJ'|]; split; [exact Hfrm|]; split; [rewrite (HKR (31%bv : bv 5) ltac:(cbv; tauto)); exact G31|];
split; [rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25 | rewrite (HKR (9%bv : bv 5) ltac:(cbv; tauto)); exact G9]|].
split.
{ rewrite (st_ok_restrict_reg trasegs (w_H W) E' ss' ms' (5%bv : bv 5) HS').
destruct Q5 as [-> | ->]; apply lg_denot_of_U; rewrite U_SMd; cbn [zmd_raw]; rewrite !U_SOff, !EA, U29, U14, !Z.add_0_r by lia;
rewrite (zcanon_id fmt), (zcanon_id i) by (unfold M64; lia); rewrite zcanon_id by (unfold M64; lia); lia. }
split; [exact HKR|]. split; [intros r Hr; reflexivity|]. split; [exact Hk' | exact Hp']. }
srr_branch_tok tratbl_lib_ok HS SHOK lnp_Bspan.
- rewrite branch_eq_U, U_SOff, U_SLit in Hc. rewrite ?(proj1 HAEx) in Hc by lia. rewrite U10, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
rewrite Hc.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK lnp_Bspan LNP_AN. { apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 32 E Ey) by (env_agree_chain HAEx) end.
apply (FIN _ _ _ _ LNP_AN HS HAEy); [reflexivity | reflexivity | first [left; reflexivity | right; reflexivity] | vm_compute; reflexivity | exact HJ | | ].
+ intros a Ha. rewrite (lg_kept_ro _ _ _ _ _ HFr ltac:(intros rr []) a Ha). exact (lg_kept_ro _ _ _ _ _ HFr1 ltac:(intros rr []) a Ha).
+ intros a Ha. apply (apresent_grows _ _ _ _ HG). exact (apresent_grows _ _ _ _ HG1 Ha).
- rewrite branch_eq_U, U_SOff, U_SLit in Hc. rewrite ?(proj1 HAEx) in Hc by lia. rewrite U10, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
rewrite Hc.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK lnp_Bspan LNP_AA. { apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 32 E Ey) by (env_agree_chain HAEx) end.
apply (FIN _ _ _ _ LNP_AA HS HAEy); [reflexivity | reflexivity | first [left; reflexivity | right; reflexivity] | vm_compute; reflexivity | exact HJ | | ].
+ intros a Ha. rewrite (lg_kept_ro _ _ _ _ _ HFr ltac:(intros rr []) a Ha). exact (lg_kept_ro _ _ _ _ _ HFr1 ltac:(intros rr []) a Ha).
+ intros a Ha. apply (apresent_grows _ _ _ _ HG). exact (apresent_grows _ _ _ _ HG1 Ha).
Qed.
Definition LNP_bpost (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (pcT pcF : Z) (KS : list (bv 5))
(Q : bool -> bvmap 5 word -> Prop) : world trasegs -> config -> Prop :=
fun W' c' => W' = W /\ exists (d : bool) (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 (if d then pcT else pcF)) mem' (seg_rom trasegs)) md' /\
lnp_base fy' regs' mem' md' /\ Q d regs' /\
(forall r : bv 5, In r KS -> getr regs' r = getr regs r) /\
(forall r : bv 5, In r LNP_FKEEP -> reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Definition LNP_KEEP5 : list (bv 5) := (5%bv : bv 5) :: LNP_KEEP.
Definition LNP_KEEP56 : list (bv 5) := (5%bv : bv 5) :: (6%bv : bv 5) :: LNP_KEEP.
Definition lnpa_alias : sv := SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SOff 5 0) (SLit 2)) (SLit 12)) (SOff 31 0).
Definition lnpa_mem : smem := [ YQ0b.mkRegion (Some 37%nat) 0 4 0 0 [YQ0b.mkChunk 0 (CVal 4 (SOff 38 0))] ].
Definition lnpa_facts : facts :=
mkFacts [ (5%nat, mkAF 0 (2^29) 0); (31%nat, mkAF 4096 140737479966720 4); (25%nat, mkAF SB SB 0);
(37%nat, mkAF 4096 140737479966720 2); (38%nat, mkAF 0 (2^32 - 1) 0) ] [] [ (lnpa_alias, SOff 37 0) ].
Definition ss_LNPAAx : sstate := mkSS LNP_AA sr_atoms lnpa_mem None lnpa_facts.
Definition lnpa_SH : list shent := [ mkSHE 37 0 4 ].
Definition lnpa_cond : sv := SF2 (FP2_cmp F_EQ FMT_S) (SF1 FP1_nanbox (SOff 38 0)) (SOff 79 0).
Section AA.
Variable t0v : Z.
Hypothesis Ht0 : 0 <= t0v < 2 ^ 29. Hypothesis Hlen : 4 * (t0v + 3) + 4 <= nF.
Lemma LNP_seedAA : forall (fy : FPState) (regs : bvmap 5 word) mem md (cv : Z),
lnp_base fy regs mem md -> getr regs 5 = w64 t0v ->
val_mem trasegs (mrestrict (w_H W) mem) (flt + 4 * (t0v + 3)) 4 cv -> 0 <= cv < 2 ^ 32 ->
let E0 := Ereg regs (map (Z_to_bv 64) [0; 0; 0; 0; 0; flt + 4 * (t0v + 3); cv] ++ []) in
let E := ew_fregs E0 64 (@fp_regs fy) in
st_okF trasegs E (mkSST LNP_AA sr_atoms (sfr_atoms 64) lnpa_mem None lnpa_facts)
(restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LNP_AA) mem (seg_rom trasegs))) /\
sh_ok trasegs lnp_Bx lnpa_SH E (mrestrict (w_H W) mem) /\
(forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) /\
(forall r : bv 5, ew E (64 + ridx r)%nat = reg_get (@fp_regs fy) r).
Proof.
intros fy regs mem md cv HB G5 Vc Hcv E0 E.
pose proof (lnp_env fy regs mem md HB) as (Qf0 & Qf1 & Qf16 & QnF & C1 & Qs0 & Qs1 & Qs2).
pose proof HB as (HJ & Hfrm & G31 & G25 & G9).
pose proof HJ as (HAR & _).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E0 j = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall j x, nth_error [0; 0; 0; 0; 0; flt + 4 * (t0v + 3); cv] j = Some x -> ew E0 (32 + j) = Z_to_bv 64 x) by (intros j x Hj; subst E0; apply Ereg_vals; exact Hj).
assert (HEE : forall j, (j < 64)%nat -> ew E j = ew E0 j) by (intros j Hj; subst E; apply ew_fregs_low; exact Hj).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr).
{ intros j rr Hj. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5. rewrite HEE by lia. apply HE0. exact Hj. }
assert (U5 : bv_unsigned (ew E0 5) = t0v) by (rewrite (HE0 5%nat 5%bv eq_refl), G5; apply unsigned_lit_small; clear - Ht0; lia).
assert (U31 : bv_unsigned (ew E0 31) = flt) by (rewrite (HE0 31%nat 31%bv eq_refl), G31; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Ht0 Hlen; lia).
assert (E25 : ew E0 25 = w64 SB) by (rewrite (HE0 25%nat 25%bv eq_refl); exact G25).
assert (A37 : bv_unsigned (ew E0 37) = flt + 4 * (t0v + 3)) by (pose proof (HV 5%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Ht0 Hlen; lia).
assert (A38 : bv_unsigned (ew E0 38) = cv) by (pose proof (HV 6%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hcv; lia).
assert (DN : forall j x, bv_unsigned (ew E0 j) = x -> sv_denot E0 (SOff j 0) = Z_to_bv 64 x).
{ intros j x Hj. cbn [sv_denot]. rewrite Hj, Z.add_0_r. reflexivity. }
pose proof (lnp_cell4 (t0v + 3) Qf16) as Hf4.
assert (HS0 : @st_ok trasegs fy E0 ss_LNPAAx (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LNP_AA) mem (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LNPAAx. apply (entry_st_ok_full trasegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold lnpa_mem. apply Forall_cons; [|apply Forall_nil].
unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite A37.
split; [clear - Qf0 Ht0; lia|]. split; [clear - Qf1 QnF C1 Ht0 Hlen; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trasegs E0 _ (flt + 4 * (t0v + 3)) 0 4 _ cv); [exact (DN _ _ A38) | zside | zside | rewrite Z.add_0_r; exact Vc].
- apply pairwise_disjoint_of_extents. unfold lnpa_mem, extent_of_region. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; [exact I|]].
+ cbn [lnpa_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (Ereg regs _) with E0.
rewrite U5, U31, E25, A37, A38. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - C1 Ht0 Hlen Qf0 Qf1 Qf16 QnF Hcv Hf4. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
+ cbn [lnpa_facts f_alias alias_ok]. change (Ereg regs _) with E0. split; [|exact I].
unfold lnpa_alias. apply U_inj. repeat (rewrite U_SAlu; cbn [zalu_raw]). rewrite !U_SOff, !U_SLit, U5, U31, A37, !Z.add_0_r.
change (Z.land (zcanon 2) 63) with 2.
rewrite (zcanon_id t0v), (zcanon_id flt), (zcanon_id 12) by (unfold M64; clear - Qf0 Qf1 QnF C1 Ht0 Hlen; lia).
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
rewrite (zcanon_id (t0v * 4)) by (unfold M64; clear - Ht0; lia).
rewrite (zcanon_id (t0v * 4 + 12)) by (unfold M64; clear - Ht0; lia).
rewrite ?zcanon_id by (unfold M64; clear - Qf0 Qf1 QnF C1 Ht0 Hlen; lia). lia. }
assert (SHOK0 : sh_ok trasegs lnp_Bx lnpa_SH E0 (mrestrict (w_H W) mem)).
{ unfold sh_ok, lnpa_SH. constructor; [|constructor].
apply (shent_ok_of_range trasegs (w_H W) mem E0 lnp_Bx 37 (flt + 4 * (t0v + 3)) 4 (flt + 4 * (t0v + 3)) 0 4).
+ apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md flt nF _ _ HAR HinF); clear - Ht0 Hlen QnF; lia.
+ unfold U, lnp_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A37.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ flt nF HAR HinF) as Hfimg.
revert Hy Hia Hfimg Ht0 Hlen QnF Qf0 Qf1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia. }
split; [exact (st_ok_enterF trasegs fy 64 E0 ss_LNPAAx _ HS0 ltac:(vm_compute; reflexivity) Hfrm)|].
split; [exact (sh_ok_agree trasegs lnp_Bx lnpa_SH 64 E0 E _ (env_agree_ew_fregs E0 64 _) ltac:(vm_compute; reflexivity) SHOK0)|].
split; [exact HE|]. intros r; subst E; apply ew_fregs_at.
Qed.
Lemma LNP_AA_run : forall (fy : FPState) (regs : bvmap 5 word) mem md,
lnp_base fy regs mem md -> getr regs 5 = w64 t0v ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LNP_AA) mem (seg_rom trasegs)) md)
(LNP_bpost fy regs mem LNP_DESC LNP_STORE LNP_KEEP5 (fun d regs' => d = false -> getr regs' 13 = w64 255)).
Proof.
intros fy regs mem md HB G5.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HB as (HJ & Hfrm & G31 & G25 & G9).
destruct (lnp_cell_val fy regs mem md (t0v + 3) HB ltac:(lia) Hlen) as (cv & Hcv & Vc).
destruct (LNP_seedAA fy regs mem md cv HB G5 Vc Hcv) as (HS & SHOK & HE & HEF).
set (E := ew_fregs _ 64 _) in HS, SHOK, HE, HEF.
assert (HAE96 : env_agree 96 E E) by (apply env_agree_refl).
apply (st_okF_branch trasegs E _ _ _ BC_EQ lnpa_cond (SLit 0) HS); clear HS; intros Hcnd HS; unfold lnpa_cond in HS; cbn [neg_bc] in HS.
all: lazymatch type of Hcnd with
| _ = true => aj_run_to_tokF tratbl_lib_ok HS HJ SHOK lnp_Bspan LNP_DESC
| _ = false => aj_run_to_tokF tratbl_lib_ok HS HJ SHOK lnp_Bspan LNP_STORE end;
[ cbn [ss_mem add_cond]; unfold lnpa_mem; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil | ].
all: lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
all: lazymatch type of HS with st_okF _ ?Ex ?ssx ?msx =>
assert (HFK : forall r : bv 5, In r LNP_FKEEP -> reg_get (ms_fregs msx) r = reg_get (@fp_regs fy) r)
by (apply (st_okF_fregs_kept trasegs Ex ssx msx 64 (@fp_regs fy) LNP_FKEEP HS);
[ intros r; first [ apply HEF | rewrite (proj1 HAEx) by (pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5; unfold ridx; lia); apply HEF ]
| vm_compute; reflexivity ]) end.
all: pose proof (st_okF_frm trasegs _ _ _ HS) as Hfrm'; pose proof (st_okF_to_legacy trasegs _ _ _ HS) as HSL; clear HS.
all: lazymatch type of HSL with st_ok _ ?Ex _ _ =>
assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) [0; 0; 0; 0; 0; flt + 4 * (t0v + 3); cv] ++ [])) Ex)
by (destruct HAEx as [EA ED]; split; [intros j Hj; rewrite ?EA by lia; subst E; rewrite ew_fregs_low by lia; reflexivity | rewrite ?ED; reflexivity]) end.
all: pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ LNP_KEEP5 HSL HAE' ltac:(vm_compute; reflexivity)) as HKR; cbn [ms_regs restrict] in HKR.
all: rreg HSL (13%bv : bv 5) R13.
all: rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ ms HSL eq_refl); cbn [ss_pc]; apply SRr_ret.
all: split; [reflexivity|].
1: exists true, (fp_of (restrict (w_H W) ms)), (ms_regs ms), (ms_mem ms); eexists; split; [reflexivity|].
2: exists false, (fp_of (restrict (w_H W) ms)), (ms_regs ms), (ms_mem ms); eexists; split; [reflexivity|].
all: (split; [split; [exact HJ|]; split; [exact Hfrm'|]; split; [rewrite (HKR (31%bv : bv 5) ltac:(cbv; tauto)); exact G31|];
split; [rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25 | rewrite (HKR (9%bv : bv 5) ltac:(cbv; tauto)); exact G9]|]).
1: split; [intros X; discriminate X|].
2: split; [intros _; exact R13|].
all: split; [exact HKR|]; split; [exact HFK|];
split; [exact (lg_kept_ro _ _ _ _ _ HFr ltac:(lnp_ro_tac)) | intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)].
Qed.
End AA.
Definition lnpn_mem : smem := [ YQ0b.mkRegion (Some 9%nat) 176 184 0 0 [YQ0b.mkChunk 176 (CVal 8 (SOff 36 0))] ].
Definition ss_LNPAN : sstate := mkSS LNP_AN sr_atoms lnpn_mem None (mkFacts [ (9%nat, mkAF (2^46) (2^47) 0); (25%nat, mkAF SB SB 0) ] [] []).
Lemma LNP_AN_run : forall (fy : FPState) (regs : bvmap 5 word) mem md (pbef : Z),
lnp_base fy regs mem md -> val_mem trasegs (mrestrict (w_H W) mem) (s1v + 176) 8 pbef -> 0 <= pbef < 2 ^ 64 ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LNP_AN) mem (seg_rom trasegs)) md)
(LNP_bpost fy regs mem LNP_DESC LNP_AC0 LNP_KEEP5 (fun d regs' => d = (pbef =? 0))).
Proof.
intros fy regs mem md pbef HB Vp Hpbef.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof (lnp_env fy regs mem md HB) as (Qf0 & Qf1 & Qf16 & QnF & C1 & Qs0 & Qs1 & Qs2).
pose proof HB as (HJ & Hfrm & G31 & G25 & G9).
set (E := Ereg regs (map (Z_to_bv 64) [0; 0; 0; 0; pbef] ++ [])).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Qs0 Qs1; lia).
assert (E25 : ew E 25 = w64 SB) by (rewrite (HE0 25%nat 25%bv eq_refl); exact G25).
assert (A36 : bv_unsigned (ew E 36) = pbef).
{ pose proof (Ereg_vals regs [0; 0; 0; 0; pbef] [] 4%nat pbef eq_refl) as X. cbn [Nat.add] in X. fold E in X. rewrite X. apply unsigned_lit_small. exact Hpbef. }
assert (HS : @st_ok trasegs fy E ss_LNPAN (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LNP_AN) mem (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LNPAN. apply (entry_st_ok_full trasegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold lnpn_mem. apply Forall_cons; [|apply Forall_nil].
unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E. rewrite U9.
split; [clear - Qs0; lia|]. split; [clear - Qs1; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trasegs E _ s1v 176 8 _ pbef); [cbn [sv_denot]; rewrite A36, Z.add_0_r; reflexivity | zside | zside | exact Vp].
- apply pairwise_disjoint_of_extents. unfold lnpn_mem, extent_of_region. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E. rewrite U9, E25. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
rewrite !Z.pow_0_r, !Z.mod_1_r. clear - Qs0 Qs1. unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok trasegs lnp_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
assert (HAE : env_agree 32 E E) by (apply env_agree_refl).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 LNP_AN) mem (seg_rom trasegs))) in HJ, SHOK.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK lnp_Bspan LNP_ANBR. { unfold ss_LNPAN, lnpn_mem. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr1; rename HG into HG1; clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msA := msx) in * end.
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAEx : env_agree 32 E Ex) by (env_agree_chain HAE) end.
assert (FIN : forall (d : bool) E' ss' ms' md', @st_ok trasegs fy E' ss' (restrict (w_H W) ms') -> env_agree 32 E E' ->
ss_pc ss' = (if d then LNP_DESC else LNP_AC0) -> ss_resv ss' = None -> d = (pbef =? 0) ->
forallb (fun rr : bv 5 => sv_eqb (sr_get (ss_regs ss') rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) LNP_KEEP5 = true ->
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') md' k ->
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) (ms_mem ms') a = aview trasegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms') a) ->
SRr trasegs W (mkCfg ms' md') (LNP_bpost fy regs mem LNP_DESC LNP_AC0 LNP_KEEP5 (fun d regs' => d = (pbef =? 0)))).
{ intros d E' ss' ms' md' HS' [EA ED] Hpc' Hrv' Hd QK HJ' Hk' Hp'.
assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) [0; 0; 0; 0; pbef] ++ [])) E') by (split; [intros j Hj; rewrite EA by lia; reflexivity | rewrite ED; reflexivity]).
pose proof (regs_kept_of_st_ok trasegs E' ss' _ regs _ LNP_KEEP5 HS' HAE' QK) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trasegs (w_H W) E' ss' ms' HS' Hrv'), Hpc'. apply SRr_ret.
split; [reflexivity|]. exists d, fy, (ms_regs ms'), (ms_mem ms'), md'. split; [reflexivity|].
split; [split; [exact HJ'|]; split; [exact Hfrm|]; split; [rewrite (HKR (31%bv : bv 5) ltac:(cbv; tauto)); exact G31|];
split; [rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25 | rewrite (HKR (9%bv : bv 5) ltac:(cbv; tauto)); exact G9]|].
split; [exact Hd|]. split; [exact HKR|]. split; [intros r Hr; reflexivity|]. split; [exact Hk' | exact Hp']. }
srr_branch_tok tratbl_lib_ok HS SHOK lnp_Bspan.
- rewrite branch_eq_U, U_SOff, U_SLit in Hc. rewrite ?(proj1 HAEx) in Hc by lia. rewrite A36, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK lnp_Bspan LNP_DESC. { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 32 E Ey) by (env_agree_chain HAEx) end.
apply (FIN true _ _ _ _ HS HAEy); [reflexivity | reflexivity | symmetry; exact Hc | vm_compute; reflexivity | exact HJ | | ].
+ intros a Ha. rewrite (lg_kept_ro _ _ _ _ _ HFr ltac:(lnp_ro_tac) a Ha). exact (lg_kept_ro _ _ _ _ _ HFr1 ltac:(lnp_ro_tac) a Ha).
+ intros a Ha. apply (apresent_grows _ _ _ _ HG). exact (apresent_grows _ _ _ _ HG1 Ha).
- rewrite branch_eq_U, U_SOff, U_SLit in Hc. rewrite ?(proj1 HAEx) in Hc by lia. rewrite A36, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK lnp_Bspan LNP_AC0. { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 32 E Ey) by (env_agree_chain HAEx) end.
apply (FIN false _ _ _ _ HS HAEy); [reflexivity | reflexivity | symmetry; exact Hc | vm_compute; reflexivity | exact HJ | | ].
+ intros a Ha. rewrite (lg_kept_ro _ _ _ _ _ HFr ltac:(lnp_ro_tac) a Ha). exact (lg_kept_ro _ _ _ _ _ HFr1 ltac:(lnp_ro_tac) a Ha).
+ intros a Ha. apply (apresent_grows _ _ _ _ HG). exact (apresent_grows _ _ _ _ HG1 Ha).
Qed.
Definition lnpc0_mem : smem :=
[ YQ0b.mkRegion (Some 9%nat) 176 264 0 0 [YQ0b.mkChunk 176 (CVal 8 (SOff 36 0)); YQ0b.mkChunk 256 (CVal 8 (SOff 35 0))];
YQ0b.mkRegion (Some 37%nat) 0 12 0 0 [YQ0b.mkChunk 0 (CVal 4 (SOff 38 0)); YQ0b.mkChunk 4 (CVal 4 (SOff 39 0)); YQ0b.mkChunk 8 (CVal 4 (SOff 40 0))];
YQ0b.mkRegion (Some 41%nat) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SOff 42 0))] ].
Definition lnpc0_alias : list (sv * sv) :=
[ (SAlu ALU_ADD (SAlu ALU_SLL (SOff 5 0) (SLit 2)) (SOff 31 0), SOff 37 0); (SAlu ALU_ADD (SOff 36 0) (SAlu ALU_SRL (SAlu ALU_SLL (SMd M_MUL (SOff 35 0) (SOff 14 0)) (SLit 32)) (SLit 32)), SOff 41 0) ].
Definition lnpc0_facts : facts :=
mkFacts [ (9%nat, mkAF (2^46) (2^47) 0); (5%nat, mkAF 0 (2^29) 0); (14%nat, mkAF 0 (2^29) 0); (35%nat, mkAF 0 4 0);
(31%nat, mkAF 4096 140737479966720 4); (25%nat, mkAF SB SB 0); (36%nat, mkAF 4096 140737479966720 0); (37%nat, mkAF 4096 140737479966720 2);
(38%nat, mkAF 0 (2^32 - 1) 0); (39%nat, mkAF 0 (2^32 - 1) 0); (40%nat, mkAF 0 (2^32 - 1) 0); (41%nat, mkAF 4096 140737479966720 0); (42%nat, mkAF 0 255 0) ] []
lnpc0_alias.
Definition ss_LNPC0x : sstate := mkSS LNP_AC0 sr_atoms lnpc0_mem None lnpc0_facts.
Definition lnpc_SH0 : list shent := [ mkSHE 37 0 12; mkSHE 41 0 1 ].
Definition lnpc0_cond : sv := SF2 (FP2_cmp F_EQ FMT_S) (SF1 FP1_nanbox (SOff 38 0)) (SF1 (FP1_cvt FC_S FC_WU RNE) (SOff 42 0)).
Section c.
Variables (t0v t1v pbef bb bn bfmt i : Z).
Hypothesis Ht0 : 0 <= t0v < 2 ^ 29. Hypothesis Hlen : 4 * (t0v + 2) + 4 <= nF.
Hypothesis Ht1 : 0 <= t1v < 2 ^ 29.
Hypothesis Hbfmt : 0 <= bfmt <= 4. Hypothesis Hi : 0 <= i < 2 ^ 29. Hypothesis Et1 : t1v = bfmt * i.
Hypothesis HinB : In (bb, bn) (ablocks B lyc Sc). Hypothesis HB0 : bb <= pbef. Hypothesis HB1 : pbef + t1v + 3 <= bb + bn.
Hypothesis HBF : (bb, bn) <> (flt, nF).
Lemma LNP_seedC0 : forall (fy : FPState) (regs : bvmap 5 word) mem md (c0 c1 c2 byv : Z),
lnp_base fy regs mem md -> getr regs 5 = w64 t0v ->
getr regs 14 = w64 i -> val_mem trasegs (mrestrict (w_H W) mem) (s1v + 256) 8 bfmt ->
val_mem trasegs (mrestrict (w_H W) mem) (s1v + 176) 8 pbef ->
val_mem trasegs (mrestrict (w_H W) mem) (flt + 4 * t0v) 4 c0 -> val_mem trasegs (mrestrict (w_H W) mem) (flt + 4 * t0v + 4) 4 c1 ->
val_mem trasegs (mrestrict (w_H W) mem) (flt + 4 * t0v + 8) 4 c2 -> 0 <= c0 < 2 ^ 32 -> 0 <= c1 < 2 ^ 32 -> 0 <= c2 < 2 ^ 32 ->
mbyte trasegs (mrestrict (w_H W) mem) (pbef + t1v + 0) = Some (Z_to_bv 8 byv) -> 0 <= byv < 256 ->
let E0 := Ereg regs (map (Z_to_bv 64) [0; 0; 0; bfmt; pbef; flt + 4 * t0v; c0; c1; c2; pbef + t1v + 0; byv] ++ []) in
let E := ew_fregs E0 64 (@fp_regs fy) in
st_okF trasegs E (mkSST LNP_AC0 sr_atoms (sfr_atoms 64) lnpc0_mem None lnpc0_facts)
(restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LNP_AC0) mem (seg_rom trasegs))) /\
sh_ok trasegs lnp_Bx lnpc_SH0 E (mrestrict (w_H W) mem) /\
(forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) /\
(forall r : bv 5, ew E (64 + ridx r)%nat = reg_get (@fp_regs fy) r) /\
bv_unsigned (ew E 35) = bfmt /\ bv_unsigned (ew E 14) = i.
Proof.
intros fy regs mem md c0 c1 c2 byv HB G5 G14 Vbf Vp V0 V1 V2 Hc0 Hc1 Hc2 Hbvb Hbv E0 E.
pose proof (lnp_env fy regs mem md HB) as (Qf0 & Qf1 & Qf16 & QnF & C1 & Qs0 & Qs1 & Qs2).
pose proof HB as (HJ & Hfrm & G31 & G25 & G9).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb bn HAR HinB) as (_ & Hb4096 & Hbceil & _ & _ & _ & Hbn0).
pose proof (req_size_pos bn ltac:(lia)) as [_ Hrb].
pose proof (sep_blocks trasegs _ LAWS lyc Sc _ _ _ bb bn flt nF HAR HinB HinF HBF) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E0 j = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall j x, nth_error [0; 0; 0; bfmt; pbef; flt + 4 * t0v; c0; c1; c2; pbef + t1v + 0; byv] j = Some x -> ew E0 (32 + j) = Z_to_bv 64 x) by (intros j x Hj; subst E0; apply Ereg_vals; exact Hj).
assert (HEE : forall j, (j < 64)%nat -> ew E j = ew E0 j) by (intros j Hj; subst E; apply ew_fregs_low; exact Hj).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr).
{ intros j rr Hj. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5. rewrite HEE by lia. apply HE0. exact Hj. }
assert (Rpb : 4096 <= pbef /\ pbef + t1v + 3 <= 140737479966720) by (clear - HB0 HB1 Hb4096 Hbceil Hrb C1 Ht1; lia).
assert (U9 : bv_unsigned (ew E0 9) = s1v) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Qs0 Qs1; lia).
assert (U5 : bv_unsigned (ew E0 5) = t0v) by (rewrite (HE0 5%nat 5%bv eq_refl), G5; apply unsigned_lit_small; clear - Ht0; lia).
assert (U14 : bv_unsigned (ew E0 14) = i) by (rewrite (HE0 14%nat 14%bv eq_refl), G14; apply unsigned_lit_small; clear - Hi; lia).
assert (A35 : bv_unsigned (ew E0 35) = bfmt) by (pose proof (HV 3%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hbfmt; lia).
assert (U31 : bv_unsigned (ew E0 31) = flt) by (rewrite (HE0 31%nat 31%bv eq_refl), G31; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Ht0 Hlen; lia).
assert (E25 : ew E0 25 = w64 SB) by (rewrite (HE0 25%nat 25%bv eq_refl); exact G25).
assert (A36 : bv_unsigned (ew E0 36) = pbef) by (pose proof (HV 4%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Rpb Ht1; lia).
assert (A37 : bv_unsigned (ew E0 37) = flt + 4 * t0v) by (pose proof (HV 5%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Ht0 Hlen; lia).
assert (A38 : bv_unsigned (ew E0 38) = c0) by (pose proof (HV 6%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hc0; lia).
assert (A39 : bv_unsigned (ew E0 39) = c1) by (pose proof (HV 7%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hc1; lia).
assert (A40 : bv_unsigned (ew E0 40) = c2) by (pose proof (HV 8%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hc2; lia).
assert (A41 : bv_unsigned (ew E0 41) = pbef + t1v + 0) by (pose proof (HV 9%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Rpb Ht1; lia).
assert (A42 : bv_unsigned (ew E0 42) = byv) by (pose proof (HV 10%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hbv; lia).
assert (DN : forall j x, bv_unsigned (ew E0 j) = x -> sv_denot E0 (SOff j 0) = Z_to_bv 64 x).
{ intros j x Hj. cbn [sv_denot]. rewrite Hj, Z.add_0_r. reflexivity. }
pose proof (lnp_cell4 t0v Qf16) as Hf4.
assert (HS0 : @st_ok trasegs fy E0 ss_LNPC0x (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LNP_AC0) mem (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LNPC0x. apply (entry_st_ok_full trasegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold lnpc0_mem. repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite U9.
split; [clear - Qs0; lia|]. split; [clear - Qs1; lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
* apply (chunk_ok_val trasegs E0 _ s1v 176 8 _ pbef); [exact (DN _ _ A36) | zside | zside | exact Vp].
* apply (chunk_ok_val trasegs E0 _ s1v 256 8 _ bfmt); [exact (DN _ _ A35) | zside | zside | exact Vbf].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite A37.
split; [clear - Qf0 Ht0; lia|]. split; [clear - Qf1 QnF C1 Ht0 Hlen; lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
* apply (chunk_ok_val trasegs E0 _ (flt + 4 * t0v) 0 4 _ c0); [exact (DN _ _ A38) | zside | zside | rewrite Z.add_0_r; exact V0].
* apply (chunk_ok_val trasegs E0 _ (flt + 4 * t0v) 4 4 _ c1); [exact (DN _ _ A39) | zside | zside | exact V1].
* apply (chunk_ok_val trasegs E0 _ (flt + 4 * t0v) 8 4 _ c2); [exact (DN _ _ A40) | zside | zside | exact V2].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite A41.
split; [clear - Rpb Ht1; lia|]. split; [clear - Rpb; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trasegs E0 _ (pbef + t1v + 0) 0 1 _ byv); [exact (DN _ _ A42) | zside | zside |].
apply (val_mem_byte trasegs); [rewrite Z.add_0_r; exact Hbvb | exact Hbv].
- apply pairwise_disjoint_of_extents. unfold lnpc0_mem, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. change (Ereg regs _) with E0. rewrite U9, A37, A41.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
clear - Qs2 Qf1 QnF Ht0 Hlen Ht1 HB0 HB1 Hrb Hbceil Hd. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [lnpc0_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (Ereg regs _) with E0.
rewrite U9, U5, U14, A35, U31, E25, A36, A37, A38, A39, A40, A41, A42. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - Qs0 Qs1 C1 Ht0 Hlen Ht1 Hbfmt Hi Qf0 Qf1 Qf16 QnF Hc0 Hc1 Hc2 Hbv Rpb Hf4. unfold SB.
repeat match goal with |- _ /\ _ => split end; lia.
+ cbn [lnpc0_facts f_alias alias_ok lnpc0_alias]. change (Ereg regs _) with E0.
repeat match goal with |- _ /\ _ => split end; try exact I.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, U5, U31, A37, !Z.add_0_r.
rewrite (zcanon_id flt), (zcanon_id t0v) by (unfold M64; clear - Qf0 Qf1 QnF C1 Ht0 Hlen; lia). change (Z.land (zcanon 2) 63) with 2.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite (zcanon_id (t0v * 4)) by (unfold M64; clear - Ht0; lia).
f_equal; lia.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite !U_SOff, !U_SLit, U14, A35, A36, A41, !Z.add_0_r.
rewrite (zcanon_id bfmt), (zcanon_id i), (zcanon_id pbef) by (unfold M64; clear - Hbfmt Hi Rpb Ht1; lia).
rewrite <- Et1. rewrite (zcanon_id t1v) by (unfold M64; clear - Ht1; lia).
change (Z.land (zcanon 32) 63) with 32. rewrite Z.shiftl_mul_pow2 by lia.
rewrite (zcanon_id (t1v * 2 ^ 32)) by (unfold M64; clear - Ht1; lia).
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia.
rewrite (zcanon_id t1v) by (unfold M64; clear - Ht1; lia). f_equal; lia.
}
assert (SHOK0 : sh_ok trasegs lnp_Bx lnpc_SH0 E0 (mrestrict (w_H W) mem)).
{ unfold sh_ok, lnpc_SH0. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range trasegs (w_H W) mem E0 lnp_Bx 37 (flt + 4 * t0v) 12 (flt + 4 * t0v) 0 12).
+ apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md flt nF _ _ HAR HinF); clear - Ht0 Hlen QnF; lia.
+ unfold U, lnp_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A37.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ flt nF HAR HinF) as Hfimg.
revert Hy Hia Hfimg Ht0 Hlen QnF Qf0 Qf1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia.
- apply (shent_ok_of_range trasegs (w_H W) mem E0 lnp_Bx 41 (pbef + t1v + 0) 1 (pbef + t1v + 0) 0 1).
+ apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md bb bn _ _ HAR HinB); clear - HB0 HB1 Hrb Ht1; lia.
+ unfold U, lnp_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A41.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ bb bn HAR HinB) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ bb bn HAR HinB) as Hbimg.
revert Hy Hia Hbimg HB0 HB1 Hrb Ht1 Hb4096 Hbceil C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia. }
split; [exact (st_ok_enterF trasegs fy 64 E0 ss_LNPC0x _ HS0 ltac:(vm_compute; reflexivity) Hfrm)|].
split; [exact (sh_ok_agree trasegs lnp_Bx lnpc_SH0 64 E0 E _ (env_agree_ew_fregs E0 64 _) ltac:(vm_compute; reflexivity) SHOK0)|].
split; [exact HE|]. split; [intros r; subst E; apply ew_fregs_at|]. rewrite !HEE by lia. split; assumption.
Qed.
Lemma LNP_AC0_run : forall (fy : FPState) (regs : bvmap 5 word) mem md,
lnp_base fy regs mem md -> getr regs 5 = w64 t0v ->
getr regs 14 = w64 i -> val_mem trasegs (mrestrict (w_H W) mem) (s1v + 256) 8 bfmt ->
val_mem trasegs (mrestrict (w_H W) mem) (s1v + 176) 8 pbef ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LNP_AC0) mem (seg_rom trasegs)) md)
(LNP_bpost fy regs mem LNP_DESC LNP_AC1 LNP_KEEP5
(fun d regs' => getr regs' 6 = w64 t1v)).
Proof.
intros fy regs mem md HB G5 G14 Vbf Vp.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HB as (HJ & Hfrm & G31 & G25 & G9).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb bn HAR HinB) as (_ & _ & _ & _ & Hbpres & _ & Hbn0).
pose proof (req_size_pos bn ltac:(lia)) as [_ Hrb].
destruct (proj1 (Hbpres (pbef + t1v + 0) ltac:(clear - HB0 HB1 Hrb Ht1; lia))) as (Hhid & pp & Hpp).
assert (Hbvb : mbyte trasegs (mrestrict (w_H W) mem) (pbef + t1v + 0) = Some (Z_to_bv 8 (bv_unsigned pp))).
{ unfold mbyte, mrestrict. rewrite Hhid, Hpp, Z_to_bv_bv_unsigned. reflexivity. }
pose proof (bv_unsigned_in_range 8 pp) as Hbv. change (bv_modulus 8) with 256 in Hbv.
destruct (lnp_cell_val fy regs mem md t0v HB ltac:(lia) ltac:(lia)) as (c0 & Hc0 & V0).
destruct (lnp_cell_val fy regs mem md (t0v + 1) HB ltac:(lia) ltac:(lia)) as (c1 & Hc1 & V1). replace (flt + 4 * (t0v + 1)) with (flt + 4 * t0v + 4) in V1 by lia.
destruct (lnp_cell_val fy regs mem md (t0v + 2) HB ltac:(lia) ltac:(lia)) as (c2 & Hc2 & V2). replace (flt + 4 * (t0v + 2)) with (flt + 4 * t0v + 8) in V2 by lia.
destruct (LNP_seedC0 fy regs mem md c0 c1 c2 _ HB G5 G14 Vbf Vp V0 V1 V2 Hc0 Hc1 Hc2 Hbvb Hbv) as (HS & SHOK & HE & HEF & HU35 & HU14).
set (E := ew_fregs _ 64 _) in HS, SHOK, HE, HEF, HU35, HU14.
assert (HAE96 : env_agree 96 E E) by (apply env_agree_refl).
apply (st_okF_branch trasegs E _ _ _ BC_EQ lnpc0_cond (SLit 0) HS); clear HS; intros Hcnd HS; unfold lnpc0_cond in HS; cbn [neg_bc] in HS.
all: lazymatch type of Hcnd with
| _ = true => aj_run_to_tokF tratbl_lib_ok HS HJ SHOK lnp_Bspan LNP_DESC
| _ => aj_run_to_tokF tratbl_lib_ok HS HJ SHOK lnp_Bspan LNP_AC1 end;
[ cbn [ss_mem add_cond]; unfold lnpc0_mem; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil | ].
all: lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
all: lazymatch type of HS with st_okF _ ?Ex ?ssx ?msx =>
assert (HFK : forall r : bv 5, In r LNP_FKEEP -> reg_get (ms_fregs msx) r = reg_get (@fp_regs fy) r)
by (apply (st_okF_fregs_kept trasegs Ex ssx msx 64 (@fp_regs fy) LNP_FKEEP HS);
[ intros r; first [ apply HEF | rewrite (proj1 HAEx) by (pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5; unfold ridx; lia); apply HEF ]
| vm_compute; reflexivity ]) end.
all: pose proof (st_okF_frm trasegs _ _ _ HS) as Hfrm'; pose proof (st_okF_to_legacy trasegs _ _ _ HS) as HSL; clear HS.
all: lazymatch type of HSL with st_ok _ ?Ex _ _ =>
assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) [0; 0; 0; bfmt; pbef; flt + 4 * t0v; c0; c1; c2; pbef + t1v + 0; bv_unsigned pp] ++ [])) Ex)
by (destruct HAEx as [EA ED]; split; [intros j Hj; rewrite ?EA by lia; subst E; rewrite ew_fregs_low by lia; reflexivity | rewrite ?ED; reflexivity]) end.
all: pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ LNP_KEEP5 HSL HAE' ltac:(vm_compute; reflexivity)) as HKR; cbn [ms_regs restrict] in HKR.
all: assert (R6 : getr (ms_regs ms) 6 = w64 t1v)
by (rewrite (st_ok_restrict_reg trasegs (w_H W) _ _ ms (6%bv : bv 5) HSL);
lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
apply lg_denot_of_U; rewrite U_SMd; cbn [zmd_raw]; rewrite !U_SOff, ?(proj1 HAEx), HU35, HU14, !Z.add_0_r by lia;
rewrite (zcanon_id bfmt), (zcanon_id i) by (unfold M64; clear - Hbfmt Hi; lia); rewrite <- Et1; apply zcanon_id; unfold M64; clear - Ht1; lia).
all: rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ ms HSL eq_refl); cbn [ss_pc]; apply SRr_ret.
all: split; [reflexivity|].
all: lazymatch type of Hcnd with
| _ = true => exists true, (fp_of (restrict (w_H W) ms)), (ms_regs ms), (ms_mem ms); eexists; split; [reflexivity|]
| _ => exists false, (fp_of (restrict (w_H W) ms)), (ms_regs ms), (ms_mem ms); eexists; split; [reflexivity|] end.
all: (split; [split; [exact HJ|]; split; [exact Hfrm'|]; split; [rewrite (HKR (31%bv : bv 5) ltac:(cbv; tauto)); exact G31|];
split; [rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25 | rewrite (HKR (9%bv : bv 5) ltac:(cbv; tauto)); exact G9]|]).
all: split; [exact R6|].
all: split; [exact HKR|]; split; [exact HFK|];
split; [exact (lg_kept_ro _ _ _ _ _ HFr ltac:(lnp_ro_tac)) | intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)].
Qed.
End c.
Definition lnpc1_mem : smem :=
[ YQ0b.mkRegion (Some 9%nat) 176 264 0 0 [YQ0b.mkChunk 176 (CVal 8 (SOff 36 0))];
YQ0b.mkRegion (Some 37%nat) 0 12 0 0 [YQ0b.mkChunk 0 (CVal 4 (SOff 38 0)); YQ0b.mkChunk 4 (CVal 4 (SOff 39 0)); YQ0b.mkChunk 8 (CVal 4 (SOff 40 0))];
YQ0b.mkRegion (Some 41%nat) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SOff 42 0))] ].
Definition lnpc1_alias : list (sv * sv) :=
[ (SAlu ALU_ADD (SAlu ALU_SLL (SOff 5 0) (SLit 2)) (SOff 31 0), SOff 37 0); (SAlu ALU_ADD (SOff 6 1) (SOff 36 0), SOff 41 0) ].
Definition lnpc1_facts : facts :=
mkFacts [ (9%nat, mkAF (2^46) (2^47) 0); (5%nat, mkAF 0 (2^29) 0); (6%nat, mkAF 0 (2^29) 0);
(31%nat, mkAF 4096 140737479966720 4); (25%nat, mkAF SB SB 0); (36%nat, mkAF 4096 140737479966720 0); (37%nat, mkAF 4096 140737479966720 2);
(38%nat, mkAF 0 (2^32 - 1) 0); (39%nat, mkAF 0 (2^32 - 1) 0); (40%nat, mkAF 0 (2^32 - 1) 0); (41%nat, mkAF 4096 140737479966720 0); (42%nat, mkAF 0 255 0) ] []
lnpc1_alias.
Definition ss_LNPC1x : sstate := mkSS LNP_AC1 sr_atoms lnpc1_mem None lnpc1_facts.
Definition lnpc_SH1 : list shent := [ mkSHE 37 0 12; mkSHE 41 0 1 ].
Definition lnpc1_cond : sv := SF2 (FP2_cmp F_EQ FMT_S) (SF1 FP1_nanbox (SOff 39 0)) (SF1 (FP1_cvt FC_S FC_WU RNE) (SOff 42 0)).
Section e.
Variables (t0v t1v pbef bb bn  : Z).
Hypothesis Ht0 : 0 <= t0v < 2 ^ 29. Hypothesis Hlen : 4 * (t0v + 2) + 4 <= nF.
Hypothesis Ht1 : 0 <= t1v < 2 ^ 29.
Hypothesis HinB : In (bb, bn) (ablocks B lyc Sc). Hypothesis HB0 : bb <= pbef. Hypothesis HB1 : pbef + t1v + 3 <= bb + bn.
Hypothesis HBF : (bb, bn) <> (flt, nF).
Lemma LNP_seedC1 : forall (fy : FPState) (regs : bvmap 5 word) mem md (c0 c1 c2 byv : Z),
lnp_base fy regs mem md -> getr regs 5 = w64 t0v ->
getr regs 6 = w64 t1v ->
val_mem trasegs (mrestrict (w_H W) mem) (s1v + 176) 8 pbef ->
val_mem trasegs (mrestrict (w_H W) mem) (flt + 4 * t0v) 4 c0 -> val_mem trasegs (mrestrict (w_H W) mem) (flt + 4 * t0v + 4) 4 c1 ->
val_mem trasegs (mrestrict (w_H W) mem) (flt + 4 * t0v + 8) 4 c2 -> 0 <= c0 < 2 ^ 32 -> 0 <= c1 < 2 ^ 32 -> 0 <= c2 < 2 ^ 32 ->
mbyte trasegs (mrestrict (w_H W) mem) (pbef + t1v + 1) = Some (Z_to_bv 8 byv) -> 0 <= byv < 256 ->
let E0 := Ereg regs (map (Z_to_bv 64) [0; 0; 0; 0; pbef; flt + 4 * t0v; c0; c1; c2; pbef + t1v + 1; byv] ++ []) in
let E := ew_fregs E0 64 (@fp_regs fy) in
st_okF trasegs E (mkSST LNP_AC1 sr_atoms (sfr_atoms 64) lnpc1_mem None lnpc1_facts)
(restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LNP_AC1) mem (seg_rom trasegs))) /\
sh_ok trasegs lnp_Bx lnpc_SH1 E (mrestrict (w_H W) mem) /\
(forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) /\
(forall r : bv 5, ew E (64 + ridx r)%nat = reg_get (@fp_regs fy) r).
Proof.
intros fy regs mem md c0 c1 c2 byv HB G5 G6 Vp V0 V1 V2 Hc0 Hc1 Hc2 Hbvb Hbv E0 E.
pose proof (lnp_env fy regs mem md HB) as (Qf0 & Qf1 & Qf16 & QnF & C1 & Qs0 & Qs1 & Qs2).
pose proof HB as (HJ & Hfrm & G31 & G25 & G9).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb bn HAR HinB) as (_ & Hb4096 & Hbceil & _ & _ & _ & Hbn0).
pose proof (req_size_pos bn ltac:(lia)) as [_ Hrb].
pose proof (sep_blocks trasegs _ LAWS lyc Sc _ _ _ bb bn flt nF HAR HinB HinF HBF) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E0 j = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall j x, nth_error [0; 0; 0; 0; pbef; flt + 4 * t0v; c0; c1; c2; pbef + t1v + 1; byv] j = Some x -> ew E0 (32 + j) = Z_to_bv 64 x) by (intros j x Hj; subst E0; apply Ereg_vals; exact Hj).
assert (HEE : forall j, (j < 64)%nat -> ew E j = ew E0 j) by (intros j Hj; subst E; apply ew_fregs_low; exact Hj).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr).
{ intros j rr Hj. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5. rewrite HEE by lia. apply HE0. exact Hj. }
assert (Rpb : 4096 <= pbef /\ pbef + t1v + 3 <= 140737479966720) by (clear - HB0 HB1 Hb4096 Hbceil Hrb C1 Ht1; lia).
assert (U9 : bv_unsigned (ew E0 9) = s1v) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Qs0 Qs1; lia).
assert (U5 : bv_unsigned (ew E0 5) = t0v) by (rewrite (HE0 5%nat 5%bv eq_refl), G5; apply unsigned_lit_small; clear - Ht0; lia).
assert (U6 : bv_unsigned (ew E0 6) = t1v) by (rewrite (HE0 6%nat 6%bv eq_refl), G6; apply unsigned_lit_small; clear - Ht1; lia).
assert (U31 : bv_unsigned (ew E0 31) = flt) by (rewrite (HE0 31%nat 31%bv eq_refl), G31; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Ht0 Hlen; lia).
assert (E25 : ew E0 25 = w64 SB) by (rewrite (HE0 25%nat 25%bv eq_refl); exact G25).
assert (A36 : bv_unsigned (ew E0 36) = pbef) by (pose proof (HV 4%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Rpb Ht1; lia).
assert (A37 : bv_unsigned (ew E0 37) = flt + 4 * t0v) by (pose proof (HV 5%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Ht0 Hlen; lia).
assert (A38 : bv_unsigned (ew E0 38) = c0) by (pose proof (HV 6%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hc0; lia).
assert (A39 : bv_unsigned (ew E0 39) = c1) by (pose proof (HV 7%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hc1; lia).
assert (A40 : bv_unsigned (ew E0 40) = c2) by (pose proof (HV 8%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hc2; lia).
assert (A41 : bv_unsigned (ew E0 41) = pbef + t1v + 1) by (pose proof (HV 9%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Rpb Ht1; lia).
assert (A42 : bv_unsigned (ew E0 42) = byv) by (pose proof (HV 10%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hbv; lia).
assert (DN : forall j x, bv_unsigned (ew E0 j) = x -> sv_denot E0 (SOff j 0) = Z_to_bv 64 x).
{ intros j x Hj. cbn [sv_denot]. rewrite Hj, Z.add_0_r. reflexivity. }
pose proof (lnp_cell4 t0v Qf16) as Hf4.
assert (HS0 : @st_ok trasegs fy E0 ss_LNPC1x (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LNP_AC1) mem (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LNPC1x. apply (entry_st_ok_full trasegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold lnpc1_mem. repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite U9.
split; [clear - Qs0; lia|]. split; [clear - Qs1; lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
* apply (chunk_ok_val trasegs E0 _ s1v 176 8 _ pbef); [exact (DN _ _ A36) | zside | zside | exact Vp].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite A37.
split; [clear - Qf0 Ht0; lia|]. split; [clear - Qf1 QnF C1 Ht0 Hlen; lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
* apply (chunk_ok_val trasegs E0 _ (flt + 4 * t0v) 0 4 _ c0); [exact (DN _ _ A38) | zside | zside | rewrite Z.add_0_r; exact V0].
* apply (chunk_ok_val trasegs E0 _ (flt + 4 * t0v) 4 4 _ c1); [exact (DN _ _ A39) | zside | zside | exact V1].
* apply (chunk_ok_val trasegs E0 _ (flt + 4 * t0v) 8 4 _ c2); [exact (DN _ _ A40) | zside | zside | exact V2].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite A41.
split; [clear - Rpb Ht1; lia|]. split; [clear - Rpb; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trasegs E0 _ (pbef + t1v + 1) 0 1 _ byv); [exact (DN _ _ A42) | zside | zside |].
apply (val_mem_byte trasegs); [rewrite Z.add_0_r; exact Hbvb | exact Hbv].
- apply pairwise_disjoint_of_extents. unfold lnpc1_mem, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. change (Ereg regs _) with E0. rewrite U9, A37, A41.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
clear - Qs2 Qf1 QnF Ht0 Hlen Ht1 HB0 HB1 Hrb Hbceil Hd. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [lnpc1_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (Ereg regs _) with E0.
rewrite U9, U5, U6, U31, E25, A36, A37, A38, A39, A40, A41, A42. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - Qs0 Qs1 C1 Ht0 Hlen Ht1 Qf0 Qf1 Qf16 QnF Hc0 Hc1 Hc2 Hbv Rpb Hf4. unfold SB.
repeat match goal with |- _ /\ _ => split end; lia.
+ cbn [lnpc1_facts f_alias alias_ok lnpc1_alias]. change (Ereg regs _) with E0.
repeat match goal with |- _ /\ _ => split end; try exact I.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, U5, U31, A37, !Z.add_0_r.
rewrite (zcanon_id flt), (zcanon_id t0v) by (unfold M64; clear - Qf0 Qf1 QnF C1 Ht0 Hlen; lia). change (Z.land (zcanon 2) 63) with 2.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite (zcanon_id (t0v * 4)) by (unfold M64; clear - Ht0; lia).
f_equal; lia.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U6, A36, A41, !Z.add_0_r.
rewrite (zcanon_id (t1v + 1)), (zcanon_id pbef) by (unfold M64; clear - Rpb Ht1; lia). f_equal; lia. }
assert (SHOK0 : sh_ok trasegs lnp_Bx lnpc_SH1 E0 (mrestrict (w_H W) mem)).
{ unfold sh_ok, lnpc_SH1. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range trasegs (w_H W) mem E0 lnp_Bx 37 (flt + 4 * t0v) 12 (flt + 4 * t0v) 0 12).
+ apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md flt nF _ _ HAR HinF); clear - Ht0 Hlen QnF; lia.
+ unfold U, lnp_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A37.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ flt nF HAR HinF) as Hfimg.
revert Hy Hia Hfimg Ht0 Hlen QnF Qf0 Qf1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia.
- apply (shent_ok_of_range trasegs (w_H W) mem E0 lnp_Bx 41 (pbef + t1v + 1) 1 (pbef + t1v + 1) 0 1).
+ apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md bb bn _ _ HAR HinB); clear - HB0 HB1 Hrb Ht1; lia.
+ unfold U, lnp_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A41.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ bb bn HAR HinB) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ bb bn HAR HinB) as Hbimg.
revert Hy Hia Hbimg HB0 HB1 Hrb Ht1 Hb4096 Hbceil C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia. }
split; [exact (st_ok_enterF trasegs fy 64 E0 ss_LNPC1x _ HS0 ltac:(vm_compute; reflexivity) Hfrm)|].
split; [exact (sh_ok_agree trasegs lnp_Bx lnpc_SH1 64 E0 E _ (env_agree_ew_fregs E0 64 _) ltac:(vm_compute; reflexivity) SHOK0)|].
split; [exact HE|]. intros r; subst E; apply ew_fregs_at.
Qed.
Lemma LNP_AC1_run : forall (fy : FPState) (regs : bvmap 5 word) mem md,
lnp_base fy regs mem md -> getr regs 5 = w64 t0v ->
getr regs 6 = w64 t1v ->
val_mem trasegs (mrestrict (w_H W) mem) (s1v + 176) 8 pbef ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LNP_AC1) mem (seg_rom trasegs)) md)
(LNP_bpost fy regs mem LNP_DESC LNP_AC2 LNP_KEEP56
(fun d regs' => True)).
Proof.
intros fy regs mem md HB G5 G6 Vp.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HB as (HJ & Hfrm & G31 & G25 & G9).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb bn HAR HinB) as (_ & _ & _ & _ & Hbpres & _ & Hbn0).
pose proof (req_size_pos bn ltac:(lia)) as [_ Hrb].
destruct (proj1 (Hbpres (pbef + t1v + 1) ltac:(clear - HB0 HB1 Hrb Ht1; lia))) as (Hhid & pp & Hpp).
assert (Hbvb : mbyte trasegs (mrestrict (w_H W) mem) (pbef + t1v + 1) = Some (Z_to_bv 8 (bv_unsigned pp))).
{ unfold mbyte, mrestrict. rewrite Hhid, Hpp, Z_to_bv_bv_unsigned. reflexivity. }
pose proof (bv_unsigned_in_range 8 pp) as Hbv. change (bv_modulus 8) with 256 in Hbv.
destruct (lnp_cell_val fy regs mem md t0v HB ltac:(lia) ltac:(lia)) as (c0 & Hc0 & V0).
destruct (lnp_cell_val fy regs mem md (t0v + 1) HB ltac:(lia) ltac:(lia)) as (c1 & Hc1 & V1). replace (flt + 4 * (t0v + 1)) with (flt + 4 * t0v + 4) in V1 by lia.
destruct (lnp_cell_val fy regs mem md (t0v + 2) HB ltac:(lia) ltac:(lia)) as (c2 & Hc2 & V2). replace (flt + 4 * (t0v + 2)) with (flt + 4 * t0v + 8) in V2 by lia.
destruct (LNP_seedC1 fy regs mem md c0 c1 c2 _ HB G5 G6 Vp V0 V1 V2 Hc0 Hc1 Hc2 Hbvb Hbv) as (HS & SHOK & HE & HEF).
set (E := ew_fregs _ 64 _) in HS, SHOK, HE, HEF.
assert (HAE96 : env_agree 96 E E) by (apply env_agree_refl).
apply (st_okF_branch trasegs E _ _ _ BC_EQ lnpc1_cond (SLit 0) HS); clear HS; intros Hcnd HS; unfold lnpc1_cond in HS; cbn [neg_bc] in HS.
all: lazymatch type of Hcnd with
| _ = true => aj_run_to_tokF tratbl_lib_ok HS HJ SHOK lnp_Bspan LNP_DESC
| _ => aj_run_to_tokF tratbl_lib_ok HS HJ SHOK lnp_Bspan LNP_AC2 end;
[ cbn [ss_mem add_cond]; unfold lnpc1_mem; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil | ].
all: lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
all: lazymatch type of HS with st_okF _ ?Ex ?ssx ?msx =>
assert (HFK : forall r : bv 5, In r LNP_FKEEP -> reg_get (ms_fregs msx) r = reg_get (@fp_regs fy) r)
by (apply (st_okF_fregs_kept trasegs Ex ssx msx 64 (@fp_regs fy) LNP_FKEEP HS);
[ intros r; first [ apply HEF | rewrite (proj1 HAEx) by (pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5; unfold ridx; lia); apply HEF ]
| vm_compute; reflexivity ]) end.
all: pose proof (st_okF_frm trasegs _ _ _ HS) as Hfrm'; pose proof (st_okF_to_legacy trasegs _ _ _ HS) as HSL; clear HS.
all: lazymatch type of HSL with st_ok _ ?Ex _ _ =>
assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) [0; 0; 0; 0; pbef; flt + 4 * t0v; c0; c1; c2; pbef + t1v + 1; bv_unsigned pp] ++ [])) Ex)
by (destruct HAEx as [EA ED]; split; [intros j Hj; rewrite ?EA by lia; subst E; rewrite ew_fregs_low by lia; reflexivity | rewrite ?ED; reflexivity]) end.
all: pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ LNP_KEEP56 HSL HAE' ltac:(vm_compute; reflexivity)) as HKR; cbn [ms_regs restrict] in HKR.
all: rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ ms HSL eq_refl); cbn [ss_pc]; apply SRr_ret.
all: split; [reflexivity|].
all: lazymatch type of Hcnd with
| _ = true => exists true, (fp_of (restrict (w_H W) ms)), (ms_regs ms), (ms_mem ms); eexists; split; [reflexivity|]
| _ => exists false, (fp_of (restrict (w_H W) ms)), (ms_regs ms), (ms_mem ms); eexists; split; [reflexivity|] end.
all: (split; [split; [exact HJ|]; split; [exact Hfrm'|]; split; [rewrite (HKR (31%bv : bv 5) ltac:(cbv; tauto)); exact G31|];
split; [rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25 | rewrite (HKR (9%bv : bv 5) ltac:(cbv; tauto)); exact G9]|]).
all: split; [exact I|].
all: split; [exact HKR|]; split; [exact HFK|];
split; [exact (lg_kept_ro _ _ _ _ _ HFr ltac:(lnp_ro_tac)) | intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)].
Qed.
End e.
Definition lnpc2_mem : smem :=
[ YQ0b.mkRegion (Some 9%nat) 176 264 0 0 [YQ0b.mkChunk 176 (CVal 8 (SOff 36 0))];
YQ0b.mkRegion (Some 37%nat) 0 12 0 0 [YQ0b.mkChunk 0 (CVal 4 (SOff 38 0)); YQ0b.mkChunk 4 (CVal 4 (SOff 39 0)); YQ0b.mkChunk 8 (CVal 4 (SOff 40 0))];
YQ0b.mkRegion (Some 41%nat) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SOff 42 0))] ].
Definition lnpc2_alias : list (sv * sv) :=
[ (SAlu ALU_ADD (SAlu ALU_SLL (SOff 5 0) (SLit 2)) (SOff 31 0), SOff 37 0); (SAlu ALU_ADD (SOff 6 2) (SOff 36 0), SOff 41 0) ].
Definition lnpc2_facts : facts :=
mkFacts [ (9%nat, mkAF (2^46) (2^47) 0); (5%nat, mkAF 0 (2^29) 0); (6%nat, mkAF 0 (2^29) 0);
(31%nat, mkAF 4096 140737479966720 4); (25%nat, mkAF SB SB 0); (36%nat, mkAF 4096 140737479966720 0); (37%nat, mkAF 4096 140737479966720 2);
(38%nat, mkAF 0 (2^32 - 1) 0); (39%nat, mkAF 0 (2^32 - 1) 0); (40%nat, mkAF 0 (2^32 - 1) 0); (41%nat, mkAF 4096 140737479966720 0); (42%nat, mkAF 0 255 0) ] []
lnpc2_alias.
Definition ss_LNPC2x : sstate := mkSS LNP_AC2 sr_atoms lnpc2_mem None lnpc2_facts.
Definition lnpc_SH2 : list shent := [ mkSHE 37 0 12; mkSHE 41 0 1 ].
Definition lnpc2_cond : sv := SF2 (FP2_cmp F_EQ FMT_S) (SF1 FP1_nanbox (SOff 40 0)) (SF1 (FP1_cvt FC_S FC_WU RNE) (SOff 42 0)).
Section f.
Variables (t0v t1v pbef bb bn  : Z).
Hypothesis Ht0 : 0 <= t0v < 2 ^ 29. Hypothesis Hlen : 4 * (t0v + 2) + 4 <= nF.
Hypothesis Ht1 : 0 <= t1v < 2 ^ 29.
Hypothesis HinB : In (bb, bn) (ablocks B lyc Sc). Hypothesis HB0 : bb <= pbef. Hypothesis HB1 : pbef + t1v + 3 <= bb + bn.
Hypothesis HBF : (bb, bn) <> (flt, nF).
Lemma LNP_seedC2 : forall (fy : FPState) (regs : bvmap 5 word) mem md (c0 c1 c2 byv : Z),
lnp_base fy regs mem md -> getr regs 5 = w64 t0v ->
getr regs 6 = w64 t1v ->
val_mem trasegs (mrestrict (w_H W) mem) (s1v + 176) 8 pbef ->
val_mem trasegs (mrestrict (w_H W) mem) (flt + 4 * t0v) 4 c0 -> val_mem trasegs (mrestrict (w_H W) mem) (flt + 4 * t0v + 4) 4 c1 ->
val_mem trasegs (mrestrict (w_H W) mem) (flt + 4 * t0v + 8) 4 c2 -> 0 <= c0 < 2 ^ 32 -> 0 <= c1 < 2 ^ 32 -> 0 <= c2 < 2 ^ 32 ->
mbyte trasegs (mrestrict (w_H W) mem) (pbef + t1v + 2) = Some (Z_to_bv 8 byv) -> 0 <= byv < 256 ->
let E0 := Ereg regs (map (Z_to_bv 64) [0; 0; 0; 0; pbef; flt + 4 * t0v; c0; c1; c2; pbef + t1v + 2; byv] ++ []) in
let E := ew_fregs E0 64 (@fp_regs fy) in
st_okF trasegs E (mkSST LNP_AC2 sr_atoms (sfr_atoms 64) lnpc2_mem None lnpc2_facts)
(restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LNP_AC2) mem (seg_rom trasegs))) /\
sh_ok trasegs lnp_Bx lnpc_SH2 E (mrestrict (w_H W) mem) /\
(forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) /\
(forall r : bv 5, ew E (64 + ridx r)%nat = reg_get (@fp_regs fy) r).
Proof.
intros fy regs mem md c0 c1 c2 byv HB G5 G6 Vp V0 V1 V2 Hc0 Hc1 Hc2 Hbvb Hbv E0 E.
pose proof (lnp_env fy regs mem md HB) as (Qf0 & Qf1 & Qf16 & QnF & C1 & Qs0 & Qs1 & Qs2).
pose proof HB as (HJ & Hfrm & G31 & G25 & G9).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb bn HAR HinB) as (_ & Hb4096 & Hbceil & _ & _ & _ & Hbn0).
pose proof (req_size_pos bn ltac:(lia)) as [_ Hrb].
pose proof (sep_blocks trasegs _ LAWS lyc Sc _ _ _ bb bn flt nF HAR HinB HinF HBF) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E0 j = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall j x, nth_error [0; 0; 0; 0; pbef; flt + 4 * t0v; c0; c1; c2; pbef + t1v + 2; byv] j = Some x -> ew E0 (32 + j) = Z_to_bv 64 x) by (intros j x Hj; subst E0; apply Ereg_vals; exact Hj).
assert (HEE : forall j, (j < 64)%nat -> ew E j = ew E0 j) by (intros j Hj; subst E; apply ew_fregs_low; exact Hj).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr).
{ intros j rr Hj. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5. rewrite HEE by lia. apply HE0. exact Hj. }
assert (Rpb : 4096 <= pbef /\ pbef + t1v + 3 <= 140737479966720) by (clear - HB0 HB1 Hb4096 Hbceil Hrb C1 Ht1; lia).
assert (U9 : bv_unsigned (ew E0 9) = s1v) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Qs0 Qs1; lia).
assert (U5 : bv_unsigned (ew E0 5) = t0v) by (rewrite (HE0 5%nat 5%bv eq_refl), G5; apply unsigned_lit_small; clear - Ht0; lia).
assert (U6 : bv_unsigned (ew E0 6) = t1v) by (rewrite (HE0 6%nat 6%bv eq_refl), G6; apply unsigned_lit_small; clear - Ht1; lia).
assert (U31 : bv_unsigned (ew E0 31) = flt) by (rewrite (HE0 31%nat 31%bv eq_refl), G31; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Ht0 Hlen; lia).
assert (E25 : ew E0 25 = w64 SB) by (rewrite (HE0 25%nat 25%bv eq_refl); exact G25).
assert (A36 : bv_unsigned (ew E0 36) = pbef) by (pose proof (HV 4%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Rpb Ht1; lia).
assert (A37 : bv_unsigned (ew E0 37) = flt + 4 * t0v) by (pose proof (HV 5%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Ht0 Hlen; lia).
assert (A38 : bv_unsigned (ew E0 38) = c0) by (pose proof (HV 6%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hc0; lia).
assert (A39 : bv_unsigned (ew E0 39) = c1) by (pose proof (HV 7%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hc1; lia).
assert (A40 : bv_unsigned (ew E0 40) = c2) by (pose proof (HV 8%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hc2; lia).
assert (A41 : bv_unsigned (ew E0 41) = pbef + t1v + 2) by (pose proof (HV 9%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Rpb Ht1; lia).
assert (A42 : bv_unsigned (ew E0 42) = byv) by (pose proof (HV 10%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hbv; lia).
assert (DN : forall j x, bv_unsigned (ew E0 j) = x -> sv_denot E0 (SOff j 0) = Z_to_bv 64 x).
{ intros j x Hj. cbn [sv_denot]. rewrite Hj, Z.add_0_r. reflexivity. }
pose proof (lnp_cell4 t0v Qf16) as Hf4.
assert (HS0 : @st_ok trasegs fy E0 ss_LNPC2x (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LNP_AC2) mem (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LNPC2x. apply (entry_st_ok_full trasegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold lnpc2_mem. repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite U9.
split; [clear - Qs0; lia|]. split; [clear - Qs1; lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
* apply (chunk_ok_val trasegs E0 _ s1v 176 8 _ pbef); [exact (DN _ _ A36) | zside | zside | exact Vp].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite A37.
split; [clear - Qf0 Ht0; lia|]. split; [clear - Qf1 QnF C1 Ht0 Hlen; lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
* apply (chunk_ok_val trasegs E0 _ (flt + 4 * t0v) 0 4 _ c0); [exact (DN _ _ A38) | zside | zside | rewrite Z.add_0_r; exact V0].
* apply (chunk_ok_val trasegs E0 _ (flt + 4 * t0v) 4 4 _ c1); [exact (DN _ _ A39) | zside | zside | exact V1].
* apply (chunk_ok_val trasegs E0 _ (flt + 4 * t0v) 8 4 _ c2); [exact (DN _ _ A40) | zside | zside | exact V2].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite A41.
split; [clear - Rpb Ht1; lia|]. split; [clear - Rpb; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trasegs E0 _ (pbef + t1v + 2) 0 1 _ byv); [exact (DN _ _ A42) | zside | zside |].
apply (val_mem_byte trasegs); [rewrite Z.add_0_r; exact Hbvb | exact Hbv].
- apply pairwise_disjoint_of_extents. unfold lnpc2_mem, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. change (Ereg regs _) with E0. rewrite U9, A37, A41.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
clear - Qs2 Qf1 QnF Ht0 Hlen Ht1 HB0 HB1 Hrb Hbceil Hd. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [lnpc2_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (Ereg regs _) with E0.
rewrite U9, U5, U6, U31, E25, A36, A37, A38, A39, A40, A41, A42. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - Qs0 Qs1 C1 Ht0 Hlen Ht1 Qf0 Qf1 Qf16 QnF Hc0 Hc1 Hc2 Hbv Rpb Hf4. unfold SB.
repeat match goal with |- _ /\ _ => split end; lia.
+ cbn [lnpc2_facts f_alias alias_ok lnpc2_alias]. change (Ereg regs _) with E0.
repeat match goal with |- _ /\ _ => split end; try exact I.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, U5, U31, A37, !Z.add_0_r.
rewrite (zcanon_id flt), (zcanon_id t0v) by (unfold M64; clear - Qf0 Qf1 QnF C1 Ht0 Hlen; lia). change (Z.land (zcanon 2) 63) with 2.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite (zcanon_id (t0v * 4)) by (unfold M64; clear - Ht0; lia).
f_equal; lia.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U6, A36, A41, !Z.add_0_r.
rewrite (zcanon_id (t1v + 2)), (zcanon_id pbef) by (unfold M64; clear - Rpb Ht1; lia). f_equal; lia. }
assert (SHOK0 : sh_ok trasegs lnp_Bx lnpc_SH2 E0 (mrestrict (w_H W) mem)).
{ unfold sh_ok, lnpc_SH2. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range trasegs (w_H W) mem E0 lnp_Bx 37 (flt + 4 * t0v) 12 (flt + 4 * t0v) 0 12).
+ apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md flt nF _ _ HAR HinF); clear - Ht0 Hlen QnF; lia.
+ unfold U, lnp_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A37.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ flt nF HAR HinF) as Hfimg.
revert Hy Hia Hfimg Ht0 Hlen QnF Qf0 Qf1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia.
- apply (shent_ok_of_range trasegs (w_H W) mem E0 lnp_Bx 41 (pbef + t1v + 2) 1 (pbef + t1v + 2) 0 1).
+ apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md bb bn _ _ HAR HinB); clear - HB0 HB1 Hrb Ht1; lia.
+ unfold U, lnp_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A41.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ bb bn HAR HinB) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ bb bn HAR HinB) as Hbimg.
revert Hy Hia Hbimg HB0 HB1 Hrb Ht1 Hb4096 Hbceil C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia. }
split; [exact (st_ok_enterF trasegs fy 64 E0 ss_LNPC2x _ HS0 ltac:(vm_compute; reflexivity) Hfrm)|].
split; [exact (sh_ok_agree trasegs lnp_Bx lnpc_SH2 64 E0 E _ (env_agree_ew_fregs E0 64 _) ltac:(vm_compute; reflexivity) SHOK0)|].
split; [exact HE|]. intros r; subst E; apply ew_fregs_at.
Qed.
Lemma LNP_AC2_run : forall (fy : FPState) (regs : bvmap 5 word) mem md,
lnp_base fy regs mem md -> getr regs 5 = w64 t0v ->
getr regs 6 = w64 t1v ->
val_mem trasegs (mrestrict (w_H W) mem) (s1v + 176) 8 pbef ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LNP_AC2) mem (seg_rom trasegs)) md)
(LNP_bpost fy regs mem LNP_DESC LNP_STORE LNP_KEEP5
(fun d regs' => d = false -> getr regs' 13 = w64 255)).
Proof.
intros fy regs mem md HB G5 G6 Vp.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HB as (HJ & Hfrm & G31 & G25 & G9).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb bn HAR HinB) as (_ & _ & _ & _ & Hbpres & _ & Hbn0).
pose proof (req_size_pos bn ltac:(lia)) as [_ Hrb].
destruct (proj1 (Hbpres (pbef + t1v + 2) ltac:(clear - HB0 HB1 Hrb Ht1; lia))) as (Hhid & pp & Hpp).
assert (Hbvb : mbyte trasegs (mrestrict (w_H W) mem) (pbef + t1v + 2) = Some (Z_to_bv 8 (bv_unsigned pp))).
{ unfold mbyte, mrestrict. rewrite Hhid, Hpp, Z_to_bv_bv_unsigned. reflexivity. }
pose proof (bv_unsigned_in_range 8 pp) as Hbv. change (bv_modulus 8) with 256 in Hbv.
destruct (lnp_cell_val fy regs mem md t0v HB ltac:(lia) ltac:(lia)) as (c0 & Hc0 & V0).
destruct (lnp_cell_val fy regs mem md (t0v + 1) HB ltac:(lia) ltac:(lia)) as (c1 & Hc1 & V1). replace (flt + 4 * (t0v + 1)) with (flt + 4 * t0v + 4) in V1 by lia.
destruct (lnp_cell_val fy regs mem md (t0v + 2) HB ltac:(lia) ltac:(lia)) as (c2 & Hc2 & V2). replace (flt + 4 * (t0v + 2)) with (flt + 4 * t0v + 8) in V2 by lia.
destruct (LNP_seedC2 fy regs mem md c0 c1 c2 _ HB G5 G6 Vp V0 V1 V2 Hc0 Hc1 Hc2 Hbvb Hbv) as (HS & SHOK & HE & HEF).
set (E := ew_fregs _ 64 _) in HS, SHOK, HE, HEF.
assert (HAE96 : env_agree 96 E E) by (apply env_agree_refl).
apply (st_okF_branch trasegs E _ _ _ BC_NE lnpc2_cond (SLit 0) HS); clear HS; intros Hcnd HS; unfold lnpc2_cond in HS; cbn [neg_bc] in HS.
all: lazymatch type of Hcnd with
| _ = false => aj_run_to_tokF tratbl_lib_ok HS HJ SHOK lnp_Bspan LNP_DESC
| _ => aj_run_to_tokF tratbl_lib_ok HS HJ SHOK lnp_Bspan LNP_STORE end;
[ cbn [ss_mem add_cond]; unfold lnpc2_mem; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil | ].
all: lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
all: lazymatch type of HS with st_okF _ ?Ex ?ssx ?msx =>
assert (HFK : forall r : bv 5, In r LNP_FKEEP -> reg_get (ms_fregs msx) r = reg_get (@fp_regs fy) r)
by (apply (st_okF_fregs_kept trasegs Ex ssx msx 64 (@fp_regs fy) LNP_FKEEP HS);
[ intros r; first [ apply HEF | rewrite (proj1 HAEx) by (pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5; unfold ridx; lia); apply HEF ]
| vm_compute; reflexivity ]) end.
all: pose proof (st_okF_frm trasegs _ _ _ HS) as Hfrm'; pose proof (st_okF_to_legacy trasegs _ _ _ HS) as HSL; clear HS.
all: lazymatch type of HSL with st_ok _ ?Ex _ _ =>
assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) [0; 0; 0; 0; pbef; flt + 4 * t0v; c0; c1; c2; pbef + t1v + 2; bv_unsigned pp] ++ [])) Ex)
by (destruct HAEx as [EA ED]; split; [intros j Hj; rewrite ?EA by lia; subst E; rewrite ew_fregs_low by lia; reflexivity | rewrite ?ED; reflexivity]) end.
all: pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ LNP_KEEP5 HSL HAE' ltac:(vm_compute; reflexivity)) as HKR; cbn [ms_regs restrict] in HKR.
all: rreg HSL (13%bv : bv 5) R13.
all: rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ ms HSL eq_refl); cbn [ss_pc]; apply SRr_ret.
all: split; [reflexivity|].
all: lazymatch type of Hcnd with
| _ = false => exists true, (fp_of (restrict (w_H W) ms)), (ms_regs ms), (ms_mem ms); eexists; split; [reflexivity|]
| _ => exists false, (fp_of (restrict (w_H W) ms)), (ms_regs ms), (ms_mem ms); eexists; split; [reflexivity|] end.
all: (split; [split; [exact HJ|]; split; [exact Hfrm'|]; split; [rewrite (HKR (31%bv : bv 5) ltac:(cbv; tauto)); exact G31|];
split; [rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25 | rewrite (HKR (9%bv : bv 5) ltac:(cbv; tauto)); exact G9]|]).
all: split; [first [intros X; discriminate X | intros _; exact R13]|].
all: split; [exact HKR|]; split; [exact HFK|];
split; [exact (lg_kept_ro _ _ _ _ _ HFr ltac:(lnp_ro_tac)) | intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)].
Qed.
End f.
Definition lnp_rel (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (fy' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
(forall r : bv 5, In r LNP_KEEP5 -> getr regs' r = getr regs r) /\
(forall r : bv 5, In r LNP_FKEEP -> reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).

Lemma lnp_rel_trans : forall fy regs mem fy1 regs1 mem1 fy2 regs2 mem2,
lnp_rel fy regs mem fy1 regs1 mem1 -> lnp_rel fy1 regs1 mem1 fy2 regs2 mem2 -> lnp_rel fy regs mem fy2 regs2 mem2.
Proof.
intros fy regs mem fy1 regs1 mem1 fy2 regs2 mem2 (K1 & F1 & M1 & X1) (K2 & F2 & M2 & X2).
split; [intros r Hr; rewrite (K2 r Hr); exact (K1 r Hr)|]. split; [intros r Hr; rewrite (F2 r Hr); exact (F1 r Hr)|].
split; [intros a Ha; rewrite (M2 a Ha); exact (M1 a Ha)|]. intros a Ha. apply X2. apply X1. exact Ha.
Qed.
Lemma lnp_keep56_5 : forall r : bv 5, In r LNP_KEEP5 -> In r LNP_KEEP56.
Proof. intros r [<- | H]; [left; reflexivity | right; right; exact H]. Qed.
Lemma lnp_slot_kept : forall (mem mem' : word -> option byte) a v,
(forall x, 0 <= x < 2 ^ 64 -> aview trasegs (w_H W) mem' x = aview trasegs (w_H W) mem x) -> 0 <= a -> a + 8 <= 2 ^ 64 ->
val_mem trasegs (mrestrict (w_H W) mem) a 8 v -> val_mem trasegs (mrestrict (w_H W) mem') a 8 v.
Proof. intros mem mem' a v Hm Ha0 Ha1 V. apply (YC04.val_mem_kept trasegs (w_H W) (w_H W) mem mem' a 8 v); [|exact V]. intros j Hj. apply Hm. lia. Qed.
Section g.
Variables (ha fmt i pbef bfmt bb bn : Z).
Hypothesis Hha : 0 <= ha < 2 ^ 64. Hypothesis Hfmt : 0 <= fmt < 2 ^ 29. Hypothesis Hi : 0 <= i < 2 ^ 29.
Hypothesis Ht0 : fmt * i < 2 ^ 29.
Hypothesis Hpbef : 0 <= pbef < 2 ^ 64.
Hypothesis HlenA : ha <> 0 -> 4 * (fmt * i + 3) + 4 <= nF.
Hypothesis HlenC : ha = 0 -> pbef <> 0 -> 4 * (fmt * i + 2) + 4 <= nF.
Hypothesis HBef : ha = 0 -> pbef <> 0 ->
0 <= bfmt <= 4 /\ bfmt * i < 2 ^ 29 /\ In (bb, bn) (ablocks B lyc Sc) /\ bb <= pbef /\ pbef + bfmt * i + 3 <= bb + bn /\ (bb, bn) <> (flt, nF).
Definition lnp_QF (d : bool) (regs' : bvmap 5 word) : Prop := getr regs' 5 = w64 (fmt * i) /\ (d = false -> getr regs' 13 = w64 255).
Lemma lnp_fin : forall fy regs mem (d : bool) (fy1 : FPState) regs1 mem1 (fy2 : FPState) regs2 mem2 md2,
(forall r : bv 5, In r LNP_KEEP -> getr regs1 r = getr regs r) ->
(forall r : bv 5, In r LNP_FKEEP -> reg_get (@fp_regs fy1) r = reg_get (@fp_regs fy) r) ->
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) mem1 a = aview trasegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a) ->
getr regs1 5 = w64 (fmt * i) ->
lnp_rel fy1 regs1 mem1 fy2 regs2 mem2 -> lnp_base fy2 regs2 mem2 md2 -> (d = false -> getr regs2 13 = w64 255) ->
LNP_bpost fy regs mem LNP_DESC LNP_STORE LNP_KEEP lnp_QF W (mkCfg (@mkst fy2 regs2 (Z_to_bv 64 (if d then LNP_DESC else LNP_STORE)) mem2 (seg_rom trasegs)) md2).
Proof.
intros fy regs mem d fy1 regs1 mem1 fy2 regs2 mem2 md2 K1 F1 M1 X1 R5 (K2 & F2 & M2 & X2) HB2 H13.
split; [reflexivity|]. exists d, fy2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HB2|].
split; [split; [rewrite (K2 (5%bv : bv 5) ltac:(left; reflexivity)); exact R5 | exact H13]|].
split; [intros r Hr; rewrite (K2 r ltac:(right; exact Hr)); exact (K1 r Hr)|].
split; [intros r Hr; rewrite (F2 r Hr); exact (F1 r Hr)|].
split; [intros a Ha; rewrite (M2 a Ha); exact (M1 a Ha)|]. intros a Ha. apply X2. apply X1. exact Ha.
Qed.
Lemma LNP_block : forall (fy : FPState) (regs : bvmap 5 word) mem md,
lnp_base fy regs mem md -> getr regs 10 = w64 ha -> getr regs 29 = w64 fmt -> getr regs 14 = w64 i ->
val_mem trasegs (mrestrict (w_H W) mem) (s1v + 176) 8 pbef -> val_mem trasegs (mrestrict (w_H W) mem) (s1v + 256) 8 bfmt ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LNP_HEAD) mem (seg_rom trasegs)) md)
(LNP_bpost fy regs mem LNP_DESC LNP_STORE LNP_KEEP lnp_QF).
Proof.
intros fy regs mem md HB G10 G29 G14 Vp Vb.
pose proof (lnp_env fy regs mem md HB) as (_ & _ & _ & _ & _ & Qs0 & Qs1 & _).
assert (Hfi : 0 <= fmt * i) by (apply Z.mul_nonneg_nonneg; lia).
eapply SRr_bind; [exact (LNP_A0 fy regs mem md ha fmt i HB G10 G29 G14 Hha Hfmt Hi)|].
intros W' c' _ (-> & fy1 & regs1 & mem1 & md1 & -> & HB1 & R5 & HK1 & HF1 & HM1 & HX1).
assert (Vp1 : val_mem trasegs (mrestrict (w_H W) mem1) (s1v + 176) 8 pbef) by (apply (lnp_slot_kept mem mem1 _ _ HM1); [lia | lia | exact Vp]).
assert (Vb1 : val_mem trasegs (mrestrict (w_H W) mem1) (s1v + 256) 8 bfmt) by (apply (lnp_slot_kept mem mem1 _ _ HM1); [lia | lia | exact Vb]).
assert (G14' : getr regs1 14 = w64 i) by (rewrite (HK1 (14%bv : bv 5) ltac:(cbv; tauto)); exact G14).
destruct (ha =? 0) eqn:Eha.
-
apply Z.eqb_eq in Eha.
eapply SRr_bind; [exact (LNP_AN_run fy1 regs1 mem1 md1 pbef HB1 Vp1 Hpbef)|].
intros W2 c2 _ (-> & d & fy2 & regs2 & mem2 & md2 & -> & HB2 & Hd & HK2 & HF2 & HM2 & HX2).
assert (REL2 : lnp_rel fy1 regs1 mem1 fy2 regs2 mem2) by (exact (conj HK2 (conj HF2 (conj HM2 HX2)))).
destruct d.
+ apply SRr_ret. apply (lnp_fin fy regs mem true fy1 regs1 mem1 fy2 regs2 mem2 md2 HK1 HF1 HM1 HX1 R5 REL2 HB2). intros X; discriminate X.
+ symmetry in Hd. apply Z.eqb_neq in Hd.
destruct (HBef Eha Hd) as (Hbf & Hbi & HinB & HB0 & HB1' & HBF). pose proof (HlenC Eha Hd) as Hlc.
assert (Hbi0 : 0 <= bfmt * i) by (apply Z.mul_nonneg_nonneg; lia).
assert (R5b : getr regs2 5 = w64 (fmt * i)) by (rewrite (HK2 (5%bv : bv 5) ltac:(left; reflexivity)); exact R5).
assert (G14b : getr regs2 14 = w64 i) by (rewrite (HK2 (14%bv : bv 5) ltac:(cbv; tauto)); exact G14').
assert (Vp2 : val_mem trasegs (mrestrict (w_H W) mem2) (s1v + 176) 8 pbef) by (apply (lnp_slot_kept mem1 mem2 _ _ HM2); [lia | lia | exact Vp1]).
assert (Vb2 : val_mem trasegs (mrestrict (w_H W) mem2) (s1v + 256) 8 bfmt) by (apply (lnp_slot_kept mem1 mem2 _ _ HM2); [lia | lia | exact Vb1]).
eapply SRr_bind; [exact (LNP_AC0_run (fmt * i) (bfmt * i) pbef bb bn bfmt i ltac:(lia) Hlc ltac:(lia) Hbf Hi eq_refl HinB HB0 HB1' HBF fy2 regs2 mem2 md2 HB2 R5b G14b Vb2 Vp2)|].
intros W3 c3 _ (-> & d3 & fy3 & regs3 & mem3 & md3 & -> & HB3 & R6 & HK3 & HF3 & HM3 & HX3).
assert (REL3 : lnp_rel fy1 regs1 mem1 fy3 regs3 mem3) by (apply (lnp_rel_trans _ _ _ _ _ _ _ _ _ REL2); exact (conj HK3 (conj HF3 (conj HM3 HX3)))).
destruct d3; [apply SRr_ret; apply (lnp_fin fy regs mem true fy1 regs1 mem1 fy3 regs3 mem3 md3 HK1 HF1 HM1 HX1 R5 REL3 HB3); intros X; discriminate X|].
assert (R5c : getr regs3 5 = w64 (fmt * i)) by (rewrite (HK3 (5%bv : bv 5) ltac:(left; reflexivity)); exact R5b).
assert (Vp3 : val_mem trasegs (mrestrict (w_H W) mem3) (s1v + 176) 8 pbef) by (apply (lnp_slot_kept mem2 mem3 _ _ HM3); [lia | lia | exact Vp2]).
eapply SRr_bind; [exact (LNP_AC1_run (fmt * i) (bfmt * i) pbef bb bn ltac:(lia) Hlc ltac:(lia) HinB HB0 HB1' HBF fy3 regs3 mem3 md3 HB3 R5c R6 Vp3)|].
intros W4 c4 _ (-> & d4 & fy4 & regs4 & mem4 & md4 & -> & HB4 & _ & HK4 & HF4 & HM4 & HX4).
assert (REL4 : lnp_rel fy1 regs1 mem1 fy4 regs4 mem4).
{ apply (lnp_rel_trans _ _ _ _ _ _ _ _ _ REL3). split; [intros r Hr; apply HK4; apply lnp_keep56_5; exact Hr|]. exact (conj HF4 (conj HM4 HX4)). }
destruct d4; [apply SRr_ret; apply (lnp_fin fy regs mem true fy1 regs1 mem1 fy4 regs4 mem4 md4 HK1 HF1 HM1 HX1 R5 REL4 HB4); intros X; discriminate X|].
assert (R5d : getr regs4 5 = w64 (fmt * i)) by (rewrite (HK4 (5%bv : bv 5) ltac:(left; reflexivity)); exact R5c).
assert (R6d : getr regs4 6 = w64 (bfmt * i)) by (rewrite (HK4 (6%bv : bv 5) ltac:(right; left; reflexivity)); exact R6).
assert (Vp4 : val_mem trasegs (mrestrict (w_H W) mem4) (s1v + 176) 8 pbef) by (apply (lnp_slot_kept mem3 mem4 _ _ HM4); [lia | lia | exact Vp3]).
eapply SRr_bind; [exact (LNP_AC2_run (fmt * i) (bfmt * i) pbef bb bn ltac:(lia) Hlc ltac:(lia) HinB HB0 HB1' HBF fy4 regs4 mem4 md4 HB4 R5d R6d Vp4)|].
intros W5 c5 _ (-> & d5 & fy5 & regs5 & mem5 & md5 & -> & HB5 & H13 & HK5 & HF5 & HM5 & HX5).
assert (REL5 : lnp_rel fy1 regs1 mem1 fy5 regs5 mem5) by (apply (lnp_rel_trans _ _ _ _ _ _ _ _ _ REL4); exact (conj HK5 (conj HF5 (conj HM5 HX5)))).
apply SRr_ret. exact (lnp_fin fy regs mem d5 fy1 regs1 mem1 fy5 regs5 mem5 md5 HK1 HF1 HM1 HX1 R5 REL5 HB5 H13).
-
apply Z.eqb_neq in Eha. pose proof (HlenA Eha) as Hla.
eapply SRr_bind; [exact (LNP_AA_run (fmt * i) ltac:(lia) Hla fy1 regs1 mem1 md1 HB1 R5)|].
intros W2 c2 _ (-> & d & fy2 & regs2 & mem2 & md2 & -> & HB2 & H13 & HK2 & HF2 & HM2 & HX2).
assert (REL2 : lnp_rel fy1 regs1 mem1 fy2 regs2 mem2) by (exact (conj HK2 (conj HF2 (conj HM2 HX2)))).
apply SRr_ret. exact (lnp_fin fy regs mem d fy1 regs1 mem1 fy2 regs2 mem2 md2 HK1 HF1 HM1 HX1 R5 REL2 HB2 H13).
Qed.
End g.
End b.
Lemma rga_lnd_cmp {rc : YN05.RunCeil} : forall (B : asyms), AR_laws trasegs B ->
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF s1v ha fmt i pbef bfmt bb bn (fy : FPState) (regs : bvmap 5 word) memc mdc,
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
frm_zero (@fp_csr fy) ->
In (flt, nF) (ablocks B lyc Sc) -> sp0 - STK <= s1v -> s1v + 384 <= sp0 ->
0 <= ha < 2 ^ 64 -> 0 <= fmt < 2 ^ 29 -> 0 <= i < 2 ^ 29 -> fmt * i < 2 ^ 29 -> 0 <= pbef < 2 ^ 64 ->
(ha <> 0 -> 4 * (fmt * i + 3) + 4 <= nF) ->
(ha = 0 -> pbef <> 0 -> 4 * (fmt * i + 2) + 4 <= nF) ->
(ha = 0 -> pbef <> 0 ->
0 <= bfmt <= 4 /\ bfmt * i < 2 ^ 29 /\ In (bb, bn) (ablocks B lyc Sc) /\ bb <= pbef /\ pbef + bfmt * i + 3 <= bb + bn /\ (bb, bn) <> (flt, nF)) ->
val_mem trasegs (mrestrict (w_H W) memc) (s1v + 176) 8 pbef -> val_mem trasegs (mrestrict (w_H W) memc) (s1v + 256) 8 bfmt ->
getr regs 10 = w64 ha -> getr regs 29 = w64 fmt -> getr regs 14 = w64 i ->
getr regs 31 = w64 flt -> getr regs 25 = w64 SB -> getr regs 9 = w64 s1v ->
SRr trasegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LNP_HEAD) memc (seg_rom trasegs)) mdc)
(fun W2 c2 => W2 = W /\ exists (d : bool) (fy' : FPState) regs2 mem2 md2,
c2 = mkCfg (@mkst fy' regs2 (Z_to_bv 64 (if d then LNP_DESC else LNP_STORE)) mem2 (seg_rom trasegs)) md2 /\
frm_zero (@fp_csr fy') /\
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
(forall r : bv 5, reg_in r LNP_CLOB = false -> getr regs2 r = getr regs r) /\
(forall r : bv 5, In r LNP_FKEEP -> reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
getr regs2 5 = w64 (fmt * i) /\ (d = false -> getr regs2 13 = w64 255) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trasegs (w_H W) mem2 a = aview trasegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a)).
Proof.
intros B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF s1v ha fmt i pbef bfmt bb bn fy regs memc mdc
HJ Hfrm HinF Hs1lo Hs1hi Hha Hfmt Hi Ht0 Hpbef HlenA HlenC HBef Vp Vb G10 G29 G14 G31 G25 G9.
assert (HB : lnp_base B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt s1v fy regs memc mdc) by (repeat (split; [assumption|]); assumption).
eapply SRr_mono; [exact (LNP_block B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF s1v HinF Hs1lo Hs1hi ha fmt i pbef bfmt bb bn
Hha Hfmt Hi Ht0 Hpbef HlenA HlenC HBef fy regs memc mdc HB G10 G29 G14 Vp Vb)|].
intros W2 c2 _ (HW & d & fy' & regs2 & mem2 & md2 & Hc2 & (HJ2 & Hfrm2 & _) & (R5 & H13) & HK & HF & HM & HX).
split; [exact HW|]. exists d, fy', regs2, mem2, md2. split; [exact Hc2|]. split; [exact Hfrm2|]. split; [exact HJ2|].
split.
{ intros r Hr. destruct (lnp_clob_cases r Hr) as [-> | Hin]; [|exact (HK r Hin)]. rewrite !getr_zero. reflexivity. }
split; [exact HF|]. split; [exact R5|]. split; [exact H13|]. split; [exact HM | exact HX].
Qed.
