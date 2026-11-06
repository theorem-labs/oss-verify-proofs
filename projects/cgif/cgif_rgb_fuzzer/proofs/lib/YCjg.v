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
Definition LNP_HEAD : Z := 0x8450c.
Definition LNP_BR0 : Z := 0x84514.
Definition LNP_AA : Z := 0x84518.
Definition LNP_AN : Z := 0x8458c.
Definition LNP_ANBR : Z := 0x84590.
Definition LNP_AC0 : Z := 0x84594.
Definition LNP_AC1 : Z := 0x845fc.
Definition LNP_AC2 : Z := 0x84664.
Definition LNP_CALL : Z := 0x8470c.
Definition LNP_STORE : Z := 0x84760.
Definition LNP_CLOB : list (bv 5) := [10; 11; 12; 13; 14]%bv.
Definition LNP_KEEPH : list (bv 5) := [1; 2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LNP_KEEP : list (bv 5) := (12%bv : bv 5) :: LNP_KEEPH.
Definition LNP_KEEPC : list (bv 5) := [12; 1; 2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 26; 27; 28; 29; 30; 31]%bv.
Definition LNP_FKEEP : list (bv 5) := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma lnp_clob_cases : forall r : bv 5, reg_in r LNP_CLOB = false -> r = 0%bv \/ In r LNP_KEEPH.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]). destruct Hin.
Qed.
Lemma lnp_keepc_cases : forall r : bv 5, In r LNP_KEEP -> r = 25%bv \/ In r LNP_KEEPC.
Proof. intros r H. cbv [LNP_KEEP LNP_KEEPH In] in H. cbv [LNP_KEEPC In]. repeat (destruct H as [<-|H]; [tauto|]). destruct H. Qed.
Section b.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trbsegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trbsegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)) (k : Z).
Variables (lyc : alayout) (Sc : astate) (W : world trbsegs).
Variables (flt nF s1v : Z).
Hypothesis HinF : In (flt, nF) (ablocks B lyc Sc).
Hypothesis Hs1lo : sp0 - STK <= s1v. Hypothesis Hs1hi : s1v + 416 <= sp0.
Definition lnp_base (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k /\
frm_zero (@fp_csr fy) /\ getr regs 23 = w64 flt /\ getr regs 18 = w64 (2 ^ 64 - 1 - flt) /\ getr regs 27 = w64 SB /\ getr regs 9 = w64 s1v.
Definition LNP_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (pc : Z) (KS : list (bv 5)) (Q : bvmap 5 word -> Prop) : world trbsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 pc) mem' (seg_rom trbsegs)) md' /\
lnp_base fy' regs' mem' md' /\ Q regs' /\
(forall r : bv 5, In r KS -> getr regs' r = getr regs r) /\
(forall r : bv 5, In r LNP_FKEEP -> reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Definition LNP_bpost (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (pcT pcF : Z) (KS : list (bv 5))
(Q : bool -> bvmap 5 word -> Prop) : world trbsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists (d : bool) (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 (if d then pcT else pcF)) mem' (seg_rom trbsegs)) md' /\
lnp_base fy' regs' mem' md' /\ Q d regs' /\
(forall r : bv 5, In r KS -> getr regs' r = getr regs r) /\
(forall r : bv 5, In r LNP_FKEEP -> reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Lemma lnp_env : forall fy regs mem md, lnp_base fy regs mem md ->
4096 <= flt /\ flt + req_size nF <= alloc_ceiling /\ flt mod 16 = 0 /\ nF <= req_size nF /\
140735332483072 <= alloc_ceiling <= 140737479966720 /\
2 ^ 46 <= s1v /\ s1v + 416 <= 2 ^ 47 /\ alloc_ceiling <= s1v.
Proof.
intros fy regs mem md (HJ & _). pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (Hf16 & Hf4096 & Hfceil & _ & _ & _ & Hnf0).
pose proof (req_size_pos nF ltac:(lia)) as [_ HrF]. repeat split; try assumption; lia.
Qed.
Lemma lnp_cell4 : forall x, flt mod 16 = 0 -> (flt + 4 * x) mod 4 = 0.
Proof.
intros x Hf16. replace (flt + 4 * x) with (flt + x * 4) by lia. rewrite Z.mod_add by lia.
pose proof (Z.div_mod flt 16 ltac:(lia)). replace flt with (4 * (4 * (flt / 16))) by lia. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity.
Qed.
Lemma lnp_cell_val : forall fy regs mem md x, lnp_base fy regs mem md -> 0 <= x -> 4 * x + 4 <= nF ->
exists v, 0 <= v < 2 ^ 32 /\ val_mem trbsegs (mrestrict (w_H W) mem) (flt + 4 * x) 4 v.
Proof.
intros fy regs mem md x HB Hx Hlen. pose proof (lnp_env fy regs mem md HB) as (_ & _ & _ & QnF & _).
pose proof HB as (HJ & _). pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (_ & _ & _ & _ & Hfpres & _).
apply (val_mem_of_present4 trbsegs). intros i Hi.
destruct (proj1 (Hfpres (flt + 4 * x + i) ltac:(clear - Hi Hx Hlen QnF; lia))) as (Hhid & bb & Hbb).
exists bb. unfold mbyte, mrestrict. rewrite Hhid, Hbb. reflexivity.
Qed.
Definition lnp_Bx : sv := SOff 27 0.
Definition lnp_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Local Ltac lnp_ro_tac :=
let rr := fresh "rr" in let Hin := fresh "Hin" in
intros rr Hin; cbn [ss_mem add_cond In] in Hin;
repeat (destruct Hin as [<- | Hin]); try contradiction; cbn [YQ0b.r_wlo YQ0b.r_whi]; lia.
Definition lnph_mem : smem := [ YQ0b.mkRegion (Some 9%nat) 168 176 0 0 [YQ0b.mkChunk 168 (CVal 8 (SOff 35 0))] ].
Definition ss_LNPH : sstate := mkSS LNP_HEAD sr_atoms lnph_mem None (mkFacts [ (9%nat, mkAF (2^46) (2^47) 0); (27%nat, mkAF SB SB 0) ] [] []).
Lemma LNP_H : forall (fy : FPState) (regs : bvmap 5 word) mem md (idx ha : Z),
lnp_base fy regs mem md -> getr regs 26 = w64 (idx + 1) -> 0 <= idx < 2 ^ 29 ->
val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 168) 8 ha -> 0 <= ha < 2 ^ 64 ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LNP_HEAD) mem (seg_rom trbsegs)) md)
(LNP_post fy regs mem (if ha =? 0 then LNP_AN else LNP_AA) LNP_KEEPH (fun regs' => getr regs' 12 = w64 idx)).
Proof.
intros fy regs mem md idx ha HB G26 Hidx Vh Hha.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof (lnp_env fy regs mem md HB) as (Qf0 & Qf1 & Qf16 & QnF & C1 & Qs0 & Qs1 & Qs2).
pose proof HB as (HJ & Hfrm & G23 & G18 & G27 & G9).
set (E := Ereg regs (map (Z_to_bv 64) [0; 0; 0; ha] ++ [])).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j x, nth_error [0; 0; 0; ha] j = Some x -> ew E (32 + j) = Z_to_bv 64 x) by (intros j x Hj; subst E; apply Ereg_vals; exact Hj).
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Qs0 Qs1; lia).
assert (U26 : bv_unsigned (ew E 26) = idx + 1) by (rewrite (HE0 26%nat 26%bv eq_refl), G26; apply unsigned_lit_small; clear - Hidx; lia).
assert (A35 : bv_unsigned (ew E 35) = ha) by (pose proof (HV 3%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; exact Hha).
assert (E27 : ew E 27 = w64 SB) by (rewrite (HE0 27%nat 27%bv eq_refl); exact G27).
assert (HS : @st_ok trbsegs fy E ss_LNPH (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LNP_HEAD) mem (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LNPH. apply (entry_st_ok_full trbsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold lnph_mem. apply Forall_cons; [|apply Forall_nil].
unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E. rewrite U9.
split; [clear - Qs0; lia|]. split; [clear - Qs1; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trbsegs E _ s1v 168 8 _ ha); [cbn [sv_denot]; rewrite A35, Z.add_0_r; reflexivity | zside | zside | exact Vh].
- apply pairwise_disjoint_of_extents. cbn. repeat split.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E. rewrite U9, E27. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
rewrite !Z.pow_0_r, !Z.mod_1_r. clear - Qs0 Qs1. unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok trbsegs lnp_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
assert (HAE : env_agree 36 E E) by (apply env_agree_refl).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 LNP_HEAD) mem (seg_rom trbsegs))) in HJ, SHOK.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK lnp_Bspan LNP_BR0. { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr1; rename HG into HGr1; clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msA := msx) in * end.
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAEx : env_agree 36 E Ex) by (env_agree_chain HAE) end.
assert (KW1 : forall x, 0 <= x < 2 ^ 64 -> aview trbsegs (w_H W) (ms_mem msA) x = aview trbsegs (w_H W) mem x) by (exact (lg_kept_ro _ _ _ _ _ HFr1 ltac:(lnp_ro_tac))).
assert (FIN : forall E' ss' ms' md' pc', @st_ok trbsegs fy E' ss' (restrict (w_H W) ms') -> env_agree 36 E E' ->
ss_pc ss' = pc' -> ss_resv ss' = None ->
sr_get (ss_regs ss') 12 = SOff 26 (-1) ->
forallb (fun rr : bv 5 => sv_eqb (sr_get (ss_regs ss') rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) LNP_KEEPH = true ->
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') md' k ->
(forall x, 0 <= x < 2 ^ 64 -> aview trbsegs (w_H W) (ms_mem ms') x = aview trbsegs (w_H W) mem x) ->
(forall x, apresent (w_H W) mem x -> apresent (w_H W) (ms_mem ms') x) ->
SRr trbsegs W (mkCfg ms' md') (LNP_post fy regs mem pc' LNP_KEEPH (fun regs' => getr regs' 12 = w64 idx))).
{ intros E' ss' ms' md' pc' HS' [EA ED] Hpc' Hrv' Q12 QK HJ' Hk' Hp'.
assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) [0; 0; 0; ha] ++ [])) E') by (split; [intros j Hj; rewrite EA by lia; reflexivity | rewrite ED; reflexivity]).
pose proof (regs_kept_of_st_ok trbsegs E' ss' _ regs _ LNP_KEEPH HS' HAE' QK) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trbsegs (w_H W) E' ss' ms' HS' Hrv'), Hpc'. apply SRr_ret.
split; [reflexivity|]. exists fy, (ms_regs ms'), (ms_mem ms'), md'. split; [reflexivity|].
split; [split; [exact HJ'|]; split; [exact Hfrm|]; split; [rewrite (HKR (23%bv : bv 5) ltac:(cbv; tauto)); exact G23|];
split; [rewrite (HKR (18%bv : bv 5) ltac:(cbv; tauto)); exact G18|];
split; [rewrite (HKR (27%bv : bv 5) ltac:(cbv; tauto)); exact G27 | rewrite (HKR (9%bv : bv 5) ltac:(cbv; tauto)); exact G9]|].
split.
{ rewrite (st_ok_restrict_reg trbsegs (w_H W) E' ss' ms' (12%bv : bv 5) HS'), Q12. cbn [sv_denot]. rewrite EA, U26 by lia. unfold w64. f_equal. lia. }
split; [exact HKR|]. split; [intros r Hr; reflexivity|]. split; [exact Hk' | exact Hp']. }
srr_branch_tok trbtbl_lib_ok HS SHOK lnp_Bspan.
- rewrite branch_eq_U, U_SOff, U_SLit in Hc. rewrite ?(proj1 HAEx) in Hc by lia. rewrite A35, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
rewrite Hc.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK lnp_Bspan LNP_AN. { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 36 E Ey) by (env_agree_chain HAEx) end.
apply (FIN _ _ _ _ LNP_AN HS HAEy); [reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | exact HJ | | ].
+ intros x Hx. rewrite (lg_kept_ro _ _ _ _ _ HFr ltac:(lnp_ro_tac) x Hx). exact (KW1 x Hx).
+ intros x Hx. apply (apresent_grows _ _ _ _ HG). exact (apresent_grows _ _ _ _ HGr1 Hx).
- rewrite branch_eq_U, U_SOff, U_SLit in Hc. rewrite ?(proj1 HAEx) in Hc by lia. rewrite A35, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
rewrite Hc.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK lnp_Bspan LNP_AA. { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 36 E Ey) by (env_agree_chain HAEx) end.
apply (FIN _ _ _ _ LNP_AA HS HAEy); [reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | exact HJ | | ].
+ intros x Hx. rewrite (lg_kept_ro _ _ _ _ _ HFr ltac:(lnp_ro_tac) x Hx). exact (KW1 x Hx).
+ intros x Hx. apply (apresent_grows _ _ _ _ HG). exact (apresent_grows _ _ _ _ HGr1 Hx).
Qed.
Definition lnpn_mem : smem := [ YQ0b.mkRegion (Some 9%nat) 184 192 0 0 [YQ0b.mkChunk 184 (CVal 8 (SOff 35 0))] ].
Definition ss_LNPAN : sstate := mkSS LNP_AN sr_atoms lnpn_mem None (mkFacts [ (9%nat, mkAF (2^46) (2^47) 0); (27%nat, mkAF SB SB 0) ] [] []).
Lemma LNP_N : forall (fy : FPState) (regs : bvmap 5 word) mem md (pbef : Z),
lnp_base fy regs mem md -> val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 184) 8 pbef -> 0 <= pbef < 2 ^ 64 ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LNP_AN) mem (seg_rom trbsegs)) md)
(LNP_post fy regs mem (if pbef =? 0 then LNP_CALL else LNP_AC0) LNP_KEEP (fun _ => True)).
Proof.
intros fy regs mem md pbef HB Vp Hpbef.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof (lnp_env fy regs mem md HB) as (Qf0 & Qf1 & Qf16 & QnF & C1 & Qs0 & Qs1 & Qs2).
pose proof HB as (HJ & Hfrm & G23 & G18 & G27 & G9).
set (E := Ereg regs (map (Z_to_bv 64) [0; 0; 0; pbef] ++ [])).
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j x, nth_error [0; 0; 0; pbef] j = Some x -> ew E (32 + j) = Z_to_bv 64 x) by (intros j x Hj; subst E; apply Ereg_vals; exact Hj).
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Qs0 Qs1; lia).
assert (A35 : bv_unsigned (ew E 35) = pbef) by (pose proof (HV 3%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; exact Hpbef).
assert (E27 : ew E 27 = w64 SB) by (rewrite (HE0 27%nat 27%bv eq_refl); exact G27).
assert (HS : @st_ok trbsegs fy E ss_LNPAN (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LNP_AN) mem (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LNPAN. apply (entry_st_ok_full trbsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold lnpn_mem. apply Forall_cons; [|apply Forall_nil].
unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E. rewrite U9.
split; [clear - Qs0; lia|]. split; [clear - Qs1; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trbsegs E _ s1v 184 8 _ pbef); [cbn [sv_denot]; rewrite A35, Z.add_0_r; reflexivity | zside | zside | exact Vp].
- apply pairwise_disjoint_of_extents. cbn. repeat split.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E. rewrite U9, E27. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
rewrite !Z.pow_0_r, !Z.mod_1_r. clear - Qs0 Qs1. unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok trbsegs lnp_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
assert (HAE : env_agree 36 E E) by (apply env_agree_refl).
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 LNP_AN) mem (seg_rom trbsegs))) in HJ, SHOK.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK lnp_Bspan LNP_ANBR. { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr1; rename HG into HGr1; clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msA := msx) in * end.
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAEx : env_agree 36 E Ex) by (env_agree_chain HAE) end.
assert (KW1 : forall x, 0 <= x < 2 ^ 64 -> aview trbsegs (w_H W) (ms_mem msA) x = aview trbsegs (w_H W) mem x) by (exact (lg_kept_ro _ _ _ _ _ HFr1 ltac:(lnp_ro_tac))).
assert (FIN : forall E' ss' ms' md' pc', @st_ok trbsegs fy E' ss' (restrict (w_H W) ms') -> env_agree 36 E E' ->
ss_pc ss' = pc' -> ss_resv ss' = None ->
forallb (fun rr : bv 5 => sv_eqb (sr_get (ss_regs ss') rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) LNP_KEEP = true ->
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms') md' k ->
(forall x, 0 <= x < 2 ^ 64 -> aview trbsegs (w_H W) (ms_mem ms') x = aview trbsegs (w_H W) mem x) ->
(forall x, apresent (w_H W) mem x -> apresent (w_H W) (ms_mem ms') x) ->
SRr trbsegs W (mkCfg ms' md') (LNP_post fy regs mem pc' LNP_KEEP (fun _ => True))).
{ intros E' ss' ms' md' pc' HS' [EA ED] Hpc' Hrv' QK HJ' Hk' Hp'.
assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) [0; 0; 0; pbef] ++ [])) E') by (split; [intros j Hj; rewrite EA by lia; reflexivity | rewrite ED; reflexivity]).
pose proof (regs_kept_of_st_ok trbsegs E' ss' _ regs _ LNP_KEEP HS' HAE' QK) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trbsegs (w_H W) E' ss' ms' HS' Hrv'), Hpc'. apply SRr_ret.
split; [reflexivity|]. exists fy, (ms_regs ms'), (ms_mem ms'), md'. split; [reflexivity|].
split; [split; [exact HJ'|]; split; [exact Hfrm|]; split; [rewrite (HKR (23%bv : bv 5) ltac:(cbv; tauto)); exact G23|];
split; [rewrite (HKR (18%bv : bv 5) ltac:(cbv; tauto)); exact G18|];
split; [rewrite (HKR (27%bv : bv 5) ltac:(cbv; tauto)); exact G27 | rewrite (HKR (9%bv : bv 5) ltac:(cbv; tauto)); exact G9]|].
split; [exact I|]. split; [exact HKR|]. split; [intros r Hr; reflexivity|]. split; [exact Hk' | exact Hp']. }
srr_branch_tok trbtbl_lib_ok HS SHOK lnp_Bspan.
- rewrite branch_eq_U, U_SOff, U_SLit in Hc. rewrite ?(proj1 HAEx) in Hc by lia. rewrite A35, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
rewrite Hc.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK lnp_Bspan LNP_CALL. { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 36 E Ey) by (env_agree_chain HAEx) end.
apply (FIN _ _ _ _ LNP_CALL HS HAEy); [reflexivity | reflexivity | vm_compute; reflexivity | exact HJ | | ].
+ intros x Hx. rewrite (lg_kept_ro _ _ _ _ _ HFr ltac:(lnp_ro_tac) x Hx). exact (KW1 x Hx).
+ intros x Hx. apply (apresent_grows _ _ _ _ HG). exact (apresent_grows _ _ _ _ HGr1 Hx).
- rewrite branch_eq_U, U_SOff, U_SLit in Hc. rewrite ?(proj1 HAEx) in Hc by lia. rewrite A35, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
rewrite Hc.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK lnp_Bspan LNP_AC0. { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 36 E Ey) by (env_agree_chain HAEx) end.
apply (FIN _ _ _ _ LNP_AC0 HS HAEy); [reflexivity | reflexivity | vm_compute; reflexivity | exact HJ | | ].
+ intros x Hx. rewrite (lg_kept_ro _ _ _ _ _ HFr ltac:(lnp_ro_tac) x Hx). exact (KW1 x Hx).
+ intros x Hx. apply (apresent_grows _ _ _ _ HG). exact (apresent_grows _ _ _ _ HGr1 Hx).
Qed.
Definition lnpa_alias : sv := SAlu ALU_ADD (SOff 23 8) (SAlu ALU_SLL (SOff 26 0) (SLit 2)).
Definition lnpa_mem : smem :=
[ YQ0b.mkRegion (Some 33%nat) 0 4 0 0 [YQ0b.mkChunk 0 (CVal 4 (SOff 32 0))];
YQ0b.mkRegion (Some 9%nat) 312 320 0 0 [YQ0b.mkChunk 312 (CVal 8 (SOff 40 0))] ].
Definition lnpa_facts : facts :=
mkFacts [ (9%nat, mkAF (2^46) (2^47) 0); (26%nat, mkAF 1 (2^29 + 1) 0); (18%nat, mkAF (2^64 - 1 - 140737479966720) (2^64 - 1 - 4096) 0);
(23%nat, mkAF 4096 140737479966720 4); (27%nat, mkAF SB SB 0); (24%nat, mkAF 4096 140737479966720 0); (40%nat, mkAF 4096 140737479966720 0);
(32%nat, mkAF 0 (2^32 - 1) 0); (33%nat, mkAF 4096 140737479966720 2) ]
[ mkAC BC_GEU (SOff 24 0) (SOff 40 0) ] [ (lnpa_alias, SOff 33 0) ].
Definition ss_LNPAAx : sstate := mkSS LNP_AA sr_atoms lnpa_mem None lnpa_facts.
Definition lnpa_SH : list shent := [ mkSHE 33 0 4; mkSHE 24 0 1 ].
Definition lnpa_cond : sv := SF2 (FP2_cmp F_EQ FMT_S) (SF1 FP1_nanbox (SOff 32 0)) (SOff 72 0).
Section AA.
Variables (idx cur pimg pg pn : Z).
Hypothesis Hidx : 0 <= idx < 2 ^ 29. Hypothesis Hlen : 4 * (idx + 3) + 4 <= nF.
Hypothesis HinG : In (pg, pn) (ablocks B lyc Sc). Hypothesis HG0 : pg <= pimg. Hypothesis Hcur0 : pimg <= cur. Hypothesis Hcur1 : cur < pg + pn.
Lemma LNP_seedAA : forall (fy : FPState) (regs : bvmap 5 word) mem md (cv : Z),
lnp_base fy regs mem md -> getr regs 26 = w64 (idx + 1) -> getr regs 24 = w64 cur ->
val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 312) 8 pimg ->
val_mem trbsegs (mrestrict (w_H W) mem) (flt + 4 * (idx + 3)) 4 cv -> 0 <= cv < 2 ^ 32 ->
let E0 := Ereg regs (map (Z_to_bv 64) [cv; flt + 4 * (idx + 3); 0; 0; 0; 0; 0; 0; pimg] ++ []) in
let E := ew_fregs E0 64 (@fp_regs fy) in
st_okF trbsegs E (mkSST LNP_AA sr_atoms (sfr_atoms 64) lnpa_mem None lnpa_facts)
(restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LNP_AA) mem (seg_rom trbsegs))) /\
sh_ok trbsegs lnp_Bx lnpa_SH E (mrestrict (w_H W) mem) /\
(forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) /\
(forall r : bv 5, ew E (64 + ridx r)%nat = reg_get (@fp_regs fy) r).
Proof.
intros fy regs mem md cv HB G26 G24 Vpi Vc Hcv E0 E.
pose proof (lnp_env fy regs mem md HB) as (Qf0 & Qf1 & Qf16 & QnF & C1 & Qs0 & Qs1 & Qs2).
pose proof HB as (HJ & Hfrm & G23 & G18 & G27 & G9).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pg pn HAR HinG) as (_ & Qg0 & Qg1 & _ & _ & _ & Hpn0).
pose proof (req_size_pos pn ltac:(lia)) as [_ Qpn].
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E0 j = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall j x, nth_error [cv; flt + 4 * (idx + 3); 0; 0; 0; 0; 0; 0; pimg] j = Some x -> ew E0 (32 + j) = Z_to_bv 64 x) by (intros j x Hj; subst E0; apply Ereg_vals; exact Hj).
assert (HEE : forall j, (j < 64)%nat -> ew E j = ew E0 j) by (intros j Hj; subst E; apply ew_fregs_low; exact Hj).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr).
{ intros j rr Hj. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5. rewrite HEE by lia. apply HE0. exact Hj. }
assert (Rpi : 4096 <= pimg /\ 4096 <= cur /\ cur < 140737479966720 /\ pimg < 140737479966720) by (clear - HG0 Hcur0 Hcur1 Qg0 Qg1 Qpn C1; lia).
assert (U9 : bv_unsigned (ew E0 9) = s1v) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Qs0 Qs1; lia).
assert (U26 : bv_unsigned (ew E0 26) = idx + 1) by (rewrite (HE0 26%nat 26%bv eq_refl), G26; apply unsigned_lit_small; clear - Hidx; lia).
assert (U24 : bv_unsigned (ew E0 24) = cur) by (rewrite (HE0 24%nat 24%bv eq_refl), G24; apply unsigned_lit_small; clear - Rpi; lia).
assert (U23 : bv_unsigned (ew E0 23) = flt) by (rewrite (HE0 23%nat 23%bv eq_refl), G23; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Hidx Hlen; lia).
assert (U18 : bv_unsigned (ew E0 18) = 2 ^ 64 - 1 - flt) by (rewrite (HE0 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Hidx Hlen; lia).
assert (E27 : ew E0 27 = w64 SB) by (rewrite (HE0 27%nat 27%bv eq_refl); exact G27).
assert (A32 : bv_unsigned (ew E0 32) = cv) by (pose proof (HV 0%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hcv; lia).
assert (A33 : bv_unsigned (ew E0 33) = flt + 4 * (idx + 3)) by (pose proof (HV 1%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Hidx Hlen; lia).
assert (A40 : bv_unsigned (ew E0 40) = pimg) by (pose proof (HV 8%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Rpi; lia).
assert (DN : forall j x, bv_unsigned (ew E0 j) = x -> sv_denot E0 (SOff j 0) = Z_to_bv 64 x).
{ intros j x Hj. cbn [sv_denot]. rewrite Hj, Z.add_0_r. reflexivity. }
pose proof (lnp_cell4 (idx + 3) Qf16) as Hf4.
assert (HS0 : @st_ok trbsegs fy E0 ss_LNPAAx (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LNP_AA) mem (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LNPAAx. apply (entry_st_ok_full trbsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold lnpa_mem. repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite A33.
split; [clear - Qf0 Hidx; lia|]. split; [clear - Qf1 QnF C1 Hidx Hlen; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trbsegs E0 _ (flt + 4 * (idx + 3)) 0 4 _ cv); [exact (DN _ _ A32) | zside | zside | rewrite Z.add_0_r; exact Vc].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite U9.
split; [clear - Qs0; lia|]. split; [clear - Qs1; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trbsegs E0 _ s1v 312 8 _ pimg); [exact (DN _ _ A40) | zside | zside | exact Vpi].
- apply pairwise_disjoint_of_extents. unfold lnpa_mem, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. change (Ereg regs _) with E0. rewrite A33, U9.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. clear - Qs2 Qf1 QnF Hidx Hlen. repeat split; lia.
- split; [|split; [split; [|exact I] | split; [|exact I]]].
+ cbn [lnpa_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (Ereg regs _) with E0.
rewrite U9, U26, U18, U23, E27, U24, A40, A32, A33. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - Qs0 Qs1 C1 Hidx Hlen Qf0 Qf1 Qf16 QnF Hcv Hf4 Rpi. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
+ unfold acond_ok. cbn [ac_c ac_a ac_b]. change (Ereg regs _) with E0. rewrite YO3v.branch_geu_U, !U_SOff, U24, A40, !Z.add_0_r.
rewrite !zcanon_id by (unfold M64; clear - Rpi; lia). apply Bool.negb_true_iff, Z.ltb_ge. exact Hcur0.
+ change (Ereg regs _) with E0. unfold lnpa_alias. apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, U23, U26, A33, !Z.add_0_r.
rewrite (zcanon_id (flt + 8)), (zcanon_id (idx + 1)) by (unfold M64; clear - Qf0 Qf1 QnF C1 Hidx Hlen; lia). change (Z.land (zcanon 2) 63) with 2.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite (zcanon_id ((idx + 1) * 4)) by (unfold M64; clear - Hidx; lia). f_equal. lia. }
assert (SHOK0 : sh_ok trbsegs lnp_Bx lnpa_SH E0 (mrestrict (w_H W) mem)).
{ unfold sh_ok, lnpa_SH. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range trbsegs (w_H W) mem E0 lnp_Bx 33 (flt + 4 * (idx + 3)) 4 (flt + 4 * (idx + 3)) 0 4).
+ apply (range_addressable_of_block trbsegs B LAWS lyc Sc W mem md flt nF _ _ HAR HinF); clear - Hidx Hlen QnF; lia.
+ unfold U, lnp_Bx. cbn [sv_denot]. rewrite E27, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A33.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ flt nF HAR HinF) as Hfimg.
revert Hy Hia Hfimg Hidx Hlen QnF Qf0 Qf1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia.
- apply (shent_ok_of_range trbsegs (w_H W) mem E0 lnp_Bx 24 cur 1 cur 0 1).
+ apply (range_addressable_of_block trbsegs B LAWS lyc Sc W mem md pg pn _ _ HAR HinG); clear - HG0 Hcur0 Hcur1 Qpn; lia.
+ unfold U, lnp_Bx. cbn [sv_denot]. rewrite E27, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U24.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ pg pn HAR HinG) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ pg pn HAR HinG) as Hgimg.
revert Hy Hia Hgimg HG0 Hcur0 Hcur1 Qpn Qg0 Qg1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia. }
split; [exact (st_ok_enterF trbsegs fy 64 E0 ss_LNPAAx _ HS0 ltac:(vm_compute; reflexivity) Hfrm)|].
split; [exact (sh_ok_agree trbsegs lnp_Bx lnpa_SH 64 E0 E _ (env_agree_ew_fregs E0 64 _) ltac:(vm_compute; reflexivity) SHOK0)|].
split; [exact HE|]. intros r; subst E; apply ew_fregs_at.
Qed.
Lemma LNP_A : forall (fy : FPState) (regs : bvmap 5 word) mem md,
lnp_base fy regs mem md -> getr regs 26 = w64 (idx + 1) -> getr regs 24 = w64 cur ->
val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 312) 8 pimg ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LNP_AA) mem (seg_rom trbsegs)) md)
(LNP_bpost fy regs mem LNP_CALL LNP_STORE LNP_KEEP (fun d regs' => d = false -> getr regs' 10 = w64 (2 ^ 64 - 1))).
Proof.
intros fy regs mem md HB G26 G24 Vpi.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof HB as (HJ & Hfrm & G23 & G18 & G27 & G9).
destruct (lnp_cell_val fy regs mem md (idx + 3) HB ltac:(lia) Hlen) as (cv & Hcv & Vc).
destruct (LNP_seedAA fy regs mem md cv HB G26 G24 Vpi Vc Hcv) as (HS & SHOK & HE & HEF).
set (E := ew_fregs _ 64 _) in HS, SHOK, HE, HEF.
assert (HAE96 : env_agree 96 E E) by (apply env_agree_refl).
apply (st_okF_branch trbsegs E _ _ _ BC_EQ lnpa_cond (SLit 0) HS); clear HS; intros Hcnd HS; unfold lnpa_cond in HS; cbn [neg_bc] in HS.
all: lazymatch type of Hcnd with
| _ = true => aj_run_to_tokF trbtbl_lib_ok HS HJ SHOK lnp_Bspan LNP_CALL
| _ = false => aj_run_to_tokF trbtbl_lib_ok HS HJ SHOK lnp_Bspan LNP_STORE end;
[ cbn [ss_mem add_cond]; unfold lnpa_mem; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil | ].
all: lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
all: lazymatch type of HS with st_okF _ ?Ex ?ssx ?msx =>
assert (HFK : forall r : bv 5, In r LNP_FKEEP -> reg_get (ms_fregs msx) r = reg_get (@fp_regs fy) r)
by (apply (st_okF_fregs_kept trbsegs Ex ssx msx 64 (@fp_regs fy) LNP_FKEEP HS);
[ intros r; first [ apply HEF | rewrite (proj1 HAEx) by (pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5; unfold ridx; lia); apply HEF ]
| vm_compute; reflexivity ]) end.
all: pose proof (st_okF_frm trbsegs _ _ _ HS) as Hfrm'; pose proof (st_okF_to_legacy trbsegs _ _ _ HS) as HSL; clear HS.
all: lazymatch type of HSL with st_ok _ ?Ex _ _ =>
assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) [cv; flt + 4 * (idx + 3); 0; 0; 0; 0; 0; 0; pimg] ++ [])) Ex)
by (destruct HAEx as [EA ED]; split; [intros j Hj; rewrite ?EA by lia; subst E; rewrite ew_fregs_low by lia; reflexivity | rewrite ?ED; reflexivity]) end.
all: pose proof (regs_kept_of_st_ok trbsegs _ _ _ regs _ LNP_KEEP HSL HAE' ltac:(vm_compute; reflexivity)) as HKR; cbn [ms_regs restrict] in HKR.
all: rreg HSL (10%bv : bv 5) R10.
all: rewrite (st_ok_restrict_mkst trbsegs (w_H W) _ _ ms HSL eq_refl); cbn [ss_pc]; apply SRr_ret.
all: split; [reflexivity|].
1: exists true, (fp_of (restrict (w_H W) ms)), (ms_regs ms), (ms_mem ms); eexists; split; [reflexivity|].
2: exists false, (fp_of (restrict (w_H W) ms)), (ms_regs ms), (ms_mem ms); eexists; split; [reflexivity|].
all: (split; [split; [exact HJ|]; split; [exact Hfrm'|]; split; [rewrite (HKR (23%bv : bv 5) ltac:(cbv; tauto)); exact G23|];
split; [rewrite (HKR (18%bv : bv 5) ltac:(cbv; tauto)); exact G18|];
split; [rewrite (HKR (27%bv : bv 5) ltac:(cbv; tauto)); exact G27 | rewrite (HKR (9%bv : bv 5) ltac:(cbv; tauto)); exact G9]|]).
1: split; [intros X; discriminate X|].
2: split; [intros _; exact R10|].
all: split; [exact HKR|]; split; [exact HFK|];
split; [exact (lg_kept_ro _ _ _ _ _ HFr ltac:(lnp_ro_tac)) | intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)].
Qed.
End AA.
Definition lnpc0_mem : smem :=
[ YQ0b.mkRegion (Some 33%nat) 0 4 0 0 [YQ0b.mkChunk 0 (CVal 4 (SOff 32 0))];
YQ0b.mkRegion (Some 9%nat) 184 416 0 0 [YQ0b.mkChunk 184 (CVal 8 (SOff 36 0)); YQ0b.mkChunk 312 (CVal 8 (SOff 40 0)); YQ0b.mkChunk 408 (CVal 8 (SOff 37 0))];
YQ0b.mkRegion (Some 35%nat) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SOff 34 0))] ].
Definition lnpc0_alias : list (sv * sv) := [ (SAlu ALU_ADD (SAlu ALU_SLL (SOff 12 0) (SLit 2)) (SOff 23 0), SOff 33 0); (SAlu ALU_ADD (SOff 36 0) (SOff 38 0), SOff 35 0) ].
Definition lnpc0_facts : facts :=
mkFacts [ (9%nat, mkAF (2^46) (2^47) 0); (12%nat, mkAF 0 (2^29) 0); (38%nat, mkAF 0 (2^29) 0);
(18%nat, mkAF (2^64 - 1 - 140737479966720) (2^64 - 1 - 4096) 0); (23%nat, mkAF 4096 140737479966720 4); (27%nat, mkAF SB SB 0);
(24%nat, mkAF 4096 140737479966720 0); (40%nat, mkAF 4096 140737479966720 0);
(32%nat, mkAF 0 (2^32 - 1) 0); (33%nat, mkAF 4096 140737479966720 2); (34%nat, mkAF 0 255 0); (35%nat, mkAF 4096 140737479966720 0);
(36%nat, mkAF 4096 140737479966720 0); (37%nat, mkAF (2^64 - 1 - 140737479966720) (2^64 - 1 - 4096) 0) ]
[ mkAC BC_GEU (SOff 24 0) (SOff 40 0) ] lnpc0_alias.
Definition lnpc0_regs := sr_set sr_atoms 25%bv (SOff 38 2).
Definition ss_LNPC0x : sstate := mkSS LNP_AC0 lnpc0_regs lnpc0_mem None lnpc0_facts.
Definition lnpc_SH0 : list shent := [ mkSHE 33 0 4; mkSHE 35 0 1; mkSHE 24 0 1 ].
Definition lnpc0_cond : sv := SF2 (FP2_cmp F_EQ FMT_S) (SF1 FP1_nanbox (SOff 32 0)) (SF1 (FP1_cvt FC_S FC_WU RNE) (SOff 34 0)).
Section c.
Variables (idx bidx pbef bb bn cur pimg pg pn : Z).
Hypothesis Hidx : 0 <= idx < 2 ^ 29. Hypothesis Hlen : 4 * (idx + 2) + 4 <= nF.
Hypothesis Hbidx : 0 <= bidx < 2 ^ 29.
Hypothesis HinB : In (bb, bn) (ablocks B lyc Sc). Hypothesis HB0 : bb <= pbef. Hypothesis HB1 : pbef + bidx + 3 <= bb + bn.
Hypothesis HBF : (bb, bn) <> (flt, nF).
Hypothesis HinG : In (pg, pn) (ablocks B lyc Sc). Hypothesis HG0 : pg <= pimg. Hypothesis Hcur0 : pimg <= cur. Hypothesis Hcur1 : cur < pg + pn.
Lemma LNP_seedC0 : forall (fy : FPState) (regs : bvmap 5 word) mem md (cv byv : Z),
lnp_base fy regs mem md -> getr regs 12 = w64 (idx) -> getr regs 25 = w64 (bidx + 2) -> getr regs 24 = w64 cur ->
val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 184) 8 pbef -> val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 408) 8 (2 ^ 64 - 1 - pbef) ->
val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 312) 8 pimg ->
val_mem trbsegs (mrestrict (w_H W) mem) (flt + 4 * (idx + 0)) 4 cv -> 0 <= cv < 2 ^ 32 ->
mbyte trbsegs (mrestrict (w_H W) mem) (pbef + bidx + 0) = Some (Z_to_bv 8 byv) -> 0 <= byv < 256 ->
let E0 := Ereg regs (map (Z_to_bv 64) [cv; flt + 4 * (idx + 0); byv; pbef + bidx + 0; pbef; 2 ^ 64 - 1 - pbef; bidx; 0; pimg] ++ []) in
let E := ew_fregs E0 64 (@fp_regs fy) in
st_okF trbsegs E (mkSST LNP_AC0 lnpc0_regs (sfr_atoms 64) lnpc0_mem None lnpc0_facts)
(restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LNP_AC0) mem (seg_rom trbsegs))) /\
sh_ok trbsegs lnp_Bx lnpc_SH0 E (mrestrict (w_H W) mem) /\
(forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) /\
(forall r : bv 5, ew E (64 + ridx r)%nat = reg_get (@fp_regs fy) r) /\
bv_unsigned (ew E 38) = bidx.
Proof.
intros fy regs mem md cv byv HB GI G25 G24 Vp Vn Vpi Vc Hcv Hbvb Hbv E0 E.
pose proof (lnp_env fy regs mem md HB) as (Qf0 & Qf1 & Qf16 & QnF & C1 & Qs0 & Qs1 & Qs2).
pose proof HB as (HJ & Hfrm & G23 & G18 & G27 & G9).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb bn HAR HinB) as (_ & Hb4096 & Hbceil & _ & _ & _ & Hbn0).
pose proof (req_size_pos bn ltac:(lia)) as [_ Hrb].
pose proof (sep_blocks trbsegs _ LAWS lyc Sc _ _ _ bb bn flt nF HAR HinB HinF HBF) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pg pn HAR HinG) as (_ & Qg0 & Qg1 & _ & _ & _ & Hpn0).
pose proof (req_size_pos pn ltac:(lia)) as [_ Qpn].
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E0 j = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall j x, nth_error [cv; flt + 4 * (idx + 0); byv; pbef + bidx + 0; pbef; 2 ^ 64 - 1 - pbef; bidx; 0; pimg] j = Some x -> ew E0 (32 + j) = Z_to_bv 64 x) by (intros j x Hj; subst E0; apply Ereg_vals; exact Hj).
assert (HEE : forall j, (j < 64)%nat -> ew E j = ew E0 j) by (intros j Hj; subst E; apply ew_fregs_low; exact Hj).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr).
{ intros j rr Hj. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5. rewrite HEE by lia. apply HE0. exact Hj. }
assert (Rpb : 4096 <= pbef /\ pbef + bidx + 3 <= 140737479966720) by (clear - HB0 HB1 Hb4096 Hbceil Hrb C1 Hbidx; lia).
assert (Rpi : 4096 <= pimg /\ 4096 <= cur /\ cur < 140737479966720 /\ pimg < 140737479966720) by (clear - HG0 Hcur0 Hcur1 Qg0 Qg1 Qpn C1; lia).
assert (U9 : bv_unsigned (ew E0 9) = s1v) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Qs0 Qs1; lia).
assert (UI : bv_unsigned (ew E0 12) = idx) by (rewrite (HE0 12%nat 12%bv eq_refl), GI; apply unsigned_lit_small; clear - Hidx; lia).
assert (U24 : bv_unsigned (ew E0 24) = cur) by (rewrite (HE0 24%nat 24%bv eq_refl), G24; apply unsigned_lit_small; clear - Rpi; lia).
assert (U23 : bv_unsigned (ew E0 23) = flt) by (rewrite (HE0 23%nat 23%bv eq_refl), G23; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Hidx Hlen; lia).
assert (U18 : bv_unsigned (ew E0 18) = 2 ^ 64 - 1 - flt) by (rewrite (HE0 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Hidx Hlen; lia).
assert (E27 : ew E0 27 = w64 SB) by (rewrite (HE0 27%nat 27%bv eq_refl); exact G27).
assert (A32 : bv_unsigned (ew E0 32) = cv) by (pose proof (HV 0%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hcv; lia).
assert (A33 : bv_unsigned (ew E0 33) = flt + 4 * (idx + 0)) by (pose proof (HV 1%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Hidx Hlen; lia).
assert (A34 : bv_unsigned (ew E0 34) = byv) by (pose proof (HV 2%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hbv; lia).
assert (A35 : bv_unsigned (ew E0 35) = pbef + bidx + 0) by (pose proof (HV 3%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Rpb Hbidx; lia).
assert (A36 : bv_unsigned (ew E0 36) = pbef) by (pose proof (HV 4%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Rpb Hbidx; lia).
assert (A37 : bv_unsigned (ew E0 37) = 2 ^ 64 - 1 - pbef) by (pose proof (HV 5%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Rpb Hbidx; lia).
assert (A38 : bv_unsigned (ew E0 38) = bidx) by (pose proof (HV 6%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hbidx; lia).
assert (A40 : bv_unsigned (ew E0 40) = pimg) by (pose proof (HV 8%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Rpi; lia).
assert (DN : forall j x, bv_unsigned (ew E0 j) = x -> sv_denot E0 (SOff j 0) = Z_to_bv 64 x).
{ intros j x Hj. cbn [sv_denot]. rewrite Hj, Z.add_0_r. reflexivity. }
pose proof (lnp_cell4 (idx + 0) Qf16) as Hf4.
assert (HS0 : @st_ok trbsegs fy E0 ss_LNPC0x (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LNP_AC0) mem (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LNPC0x, lnpc0_regs. apply (entry_st_ok_full trbsegs).
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X |]. rewrite G25. cbn [sv_denot]. change (Ereg regs _) with E0. rewrite A38. reflexivity.
- vm_compute. reflexivity.
- unfold lnpc0_mem. repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite A33.
split; [clear - Qf0 Hidx; lia|]. split; [clear - Qf1 QnF C1 Hidx Hlen; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trbsegs E0 _ (flt + 4 * (idx + 0)) 0 4 _ cv); [exact (DN _ _ A32) | zside | zside | rewrite Z.add_0_r; exact Vc].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite U9.
split; [clear - Qs0; lia|]. split; [clear - Qs1; lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
* apply (chunk_ok_val trbsegs E0 _ s1v 184 8 _ pbef); [exact (DN _ _ A36) | zside | zside | exact Vp].
* apply (chunk_ok_val trbsegs E0 _ s1v 312 8 _ pimg); [exact (DN _ _ A40) | zside | zside | exact Vpi].
* apply (chunk_ok_val trbsegs E0 _ s1v 408 8 _ (2 ^ 64 - 1 - pbef)); [exact (DN _ _ A37) | zside | zside | exact Vn].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite A35.
split; [clear - Rpb Hbidx; lia|]. split; [clear - Rpb; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trbsegs E0 _ (pbef + bidx + 0) 0 1 _ byv); [exact (DN _ _ A34) | zside | zside |].
apply (val_mem_byte trbsegs); [rewrite Z.add_0_r; exact Hbvb | exact Hbv].
- apply pairwise_disjoint_of_extents. unfold lnpc0_mem, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. change (Ereg regs _) with E0. rewrite A33, U9, A35.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
clear - Qs2 Qf1 QnF Hidx Hlen Hbidx HB0 HB1 Hrb Hbceil Hd. repeat split; lia.
- split; [|split; [split; [|exact I] | ]].
+ cbn [lnpc0_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (Ereg regs _) with E0.
rewrite U9, UI, A38, U18, U23, E27, U24, A40, A32, A33, A34, A35, A36, A37. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - Qs0 Qs1 C1 Hidx Hlen Hbidx Qf0 Qf1 Qf16 QnF Hcv Hbv Rpb Rpi Hf4. unfold SB.
repeat match goal with |- _ /\ _ => split end; lia.
+ unfold acond_ok. cbn [ac_c ac_a ac_b]. change (Ereg regs _) with E0. rewrite YO3v.branch_geu_U, !U_SOff, U24, A40, !Z.add_0_r.
rewrite !zcanon_id by (unfold M64; clear - Rpi; lia). apply Bool.negb_true_iff, Z.ltb_ge. exact Hcur0.
+ cbn [lnpc0_facts f_alias alias_ok lnpc0_alias]. change (Ereg regs _) with E0.
repeat match goal with |- _ /\ _ => split end; try exact I.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, UI, U23, A33, ?Z.add_0_r.
rewrite ?(zcanon_id flt), ?(zcanon_id (flt + 4)), (zcanon_id (idx)) by (unfold M64; clear - Qf0 Qf1 QnF C1 Hidx Hlen; lia). change (Z.land (zcanon 2) 63) with 2.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite (zcanon_id ((idx) * 4)) by (unfold M64; clear - Hidx; lia).
f_equal; lia.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, A36, A38, A35, ?Z.add_0_r.
rewrite ?(zcanon_id pbef), ?(zcanon_id (pbef + 0)), (zcanon_id bidx) by (unfold M64; clear - Rpb Hbidx; lia). f_equal; lia. }
assert (SHOK0 : sh_ok trbsegs lnp_Bx lnpc_SH0 E0 (mrestrict (w_H W) mem)).
{ unfold sh_ok, lnpc_SH0. constructor; [|constructor; [|constructor; [|constructor]]].
- apply (shent_ok_of_range trbsegs (w_H W) mem E0 lnp_Bx 33 (flt + 4 * (idx + 0)) 4 (flt + 4 * (idx + 0)) 0 4).
+ apply (range_addressable_of_block trbsegs B LAWS lyc Sc W mem md flt nF _ _ HAR HinF); clear - Hidx Hlen QnF; lia.
+ unfold U, lnp_Bx. cbn [sv_denot]. rewrite E27, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A33.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ flt nF HAR HinF) as Hfimg.
revert Hy Hia Hfimg Hidx Hlen QnF Qf0 Qf1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia.
- apply (shent_ok_of_range trbsegs (w_H W) mem E0 lnp_Bx 35 (pbef + bidx + 0) 1 (pbef + bidx + 0) 0 1).
+ apply (range_addressable_of_block trbsegs B LAWS lyc Sc W mem md bb bn _ _ HAR HinB); clear - HB0 HB1 Hrb Hbidx; lia.
+ unfold U, lnp_Bx. cbn [sv_denot]. rewrite E27, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A35.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ bb bn HAR HinB) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ bb bn HAR HinB) as Hbimg.
revert Hy Hia Hbimg HB0 HB1 Hrb Hbidx Hb4096 Hbceil C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia.
- apply (shent_ok_of_range trbsegs (w_H W) mem E0 lnp_Bx 24 cur 1 cur 0 1).
+ apply (range_addressable_of_block trbsegs B LAWS lyc Sc W mem md pg pn _ _ HAR HinG); clear - HG0 Hcur0 Hcur1 Qpn; lia.
+ unfold U, lnp_Bx. cbn [sv_denot]. rewrite E27, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U24.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ pg pn HAR HinG) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ pg pn HAR HinG) as Hgimg.
revert Hy Hia Hgimg HG0 Hcur0 Hcur1 Qpn Qg0 Qg1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia. }
split; [exact (st_ok_enterF trbsegs fy 64 E0 ss_LNPC0x _ HS0 ltac:(vm_compute; reflexivity) Hfrm)|].
split; [exact (sh_ok_agree trbsegs lnp_Bx lnpc_SH0 64 E0 E _ (env_agree_ew_fregs E0 64 _) ltac:(vm_compute; reflexivity) SHOK0)|].
split; [exact HE|]. split; [intros r; subst E; apply ew_fregs_at|]. rewrite HEE by lia. exact A38.
Qed.
Lemma LNP_C0 : forall (fy : FPState) (regs : bvmap 5 word) mem md,
lnp_base fy regs mem md -> getr regs 12 = w64 (idx) -> getr regs 25 = w64 (bidx + 2) -> getr regs 24 = w64 cur ->
val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 184) 8 pbef -> val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 408) 8 (2 ^ 64 - 1 - pbef) ->
val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 312) 8 pimg ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LNP_AC0) mem (seg_rom trbsegs)) md)
(LNP_bpost fy regs mem LNP_CALL LNP_AC1 LNP_KEEP
(fun d regs' => True)).
Proof.
intros fy regs mem md HB GI G25 G24 Vp Vn Vpi.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof HB as (HJ & Hfrm & G23 & G18 & G27 & G9).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb bn HAR HinB) as (_ & _ & _ & _ & Hbpres & _ & Hbn0).
pose proof (req_size_pos bn ltac:(lia)) as [_ Hrb].
destruct (proj1 (Hbpres (pbef + bidx + 0) ltac:(clear - HB0 HB1 Hrb Hbidx; lia))) as (Hhid & pp & Hpp).
assert (Hbvb : mbyte trbsegs (mrestrict (w_H W) mem) (pbef + bidx + 0) = Some (Z_to_bv 8 (bv_unsigned pp))).
{ unfold mbyte, mrestrict. rewrite Hhid, Hpp, Z_to_bv_bv_unsigned. reflexivity. }
pose proof (bv_unsigned_in_range 8 pp) as Hbv. change (bv_modulus 8) with 256 in Hbv.
destruct (lnp_cell_val fy regs mem md (idx + 0) HB ltac:(lia) ltac:(lia)) as (cv & Hcv & Vc).
destruct (LNP_seedC0 fy regs mem md cv _ HB GI G25 G24 Vp Vn Vpi Vc Hcv Hbvb Hbv) as (HS & SHOK & HE & HEF & HU38).
set (E := ew_fregs _ 64 _) in HS, SHOK, HE, HEF, HU38.
assert (HAE96 : env_agree 96 E E) by (apply env_agree_refl).
apply (st_okF_branch trbsegs E _ _ _ BC_EQ lnpc0_cond (SLit 0) HS); clear HS; intros Hcnd HS; unfold lnpc0_cond in HS; cbn [neg_bc] in HS.
all: lazymatch type of Hcnd with
| _ = true => aj_run_to_tokF trbtbl_lib_ok HS HJ SHOK lnp_Bspan LNP_CALL
| _ => aj_run_to_tokF trbtbl_lib_ok HS HJ SHOK lnp_Bspan LNP_AC1 end;
[ cbn [ss_mem add_cond]; unfold lnpc0_mem; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil | ].
all: lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
all: lazymatch type of HS with st_okF _ ?Ex ?ssx ?msx =>
assert (HFK : forall r : bv 5, In r LNP_FKEEP -> reg_get (ms_fregs msx) r = reg_get (@fp_regs fy) r)
by (apply (st_okF_fregs_kept trbsegs Ex ssx msx 64 (@fp_regs fy) LNP_FKEEP HS);
[ intros r; first [ apply HEF | rewrite (proj1 HAEx) by (pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5; unfold ridx; lia); apply HEF ]
| vm_compute; reflexivity ]) end.
all: pose proof (st_okF_frm trbsegs _ _ _ HS) as Hfrm'; pose proof (st_okF_to_legacy trbsegs _ _ _ HS) as HSL; clear HS.
all: lazymatch type of HSL with st_ok _ ?Ex _ _ =>
assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) [cv; flt + 4 * (idx + 0); bv_unsigned pp; pbef + bidx + 0; pbef; 2 ^ 64 - 1 - pbef; bidx; 0; pimg] ++ [])) Ex)
by (destruct HAEx as [EA ED]; split; [intros j Hj; rewrite ?EA by lia; subst E; rewrite ew_fregs_low by lia; reflexivity | rewrite ?ED; reflexivity]) end.
all: pose proof (regs_kept_of_st_ok trbsegs _ _ _ regs _ LNP_KEEPC HSL HAE' ltac:(vm_compute; reflexivity)) as HKR0; cbn [ms_regs restrict] in HKR0.
all: assert (R25 : getr (ms_regs ms) 25 = getr regs 25)
by (rewrite (st_ok_restrict_reg trbsegs (w_H W) _ _ ms (25%bv : bv 5) HSL);
lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
cbn [sv_denot]; rewrite (proj1 HAEx), HU38, G25 by lia; reflexivity).
all: assert (HKR : forall r : bv 5, In r LNP_KEEP -> getr (ms_regs ms) r = getr regs r)
by (intros r Hr; destruct (lnp_keepc_cases r Hr) as [-> | Hr0]; [exact R25 | exact (HKR0 r Hr0)]).
all: rewrite (st_ok_restrict_mkst trbsegs (w_H W) _ _ ms HSL eq_refl); cbn [ss_pc]; apply SRr_ret.
all: split; [reflexivity|].
1: exists true, (fp_of (restrict (w_H W) ms)), (ms_regs ms), (ms_mem ms); eexists; split; [reflexivity|].
2: exists false, (fp_of (restrict (w_H W) ms)), (ms_regs ms), (ms_mem ms); eexists; split; [reflexivity|].
all: (split; [split; [exact HJ|]; split; [exact Hfrm'|]; split; [rewrite (HKR (23%bv : bv 5) ltac:(cbv; tauto)); exact G23|];
split; [rewrite (HKR (18%bv : bv 5) ltac:(cbv; tauto)); exact G18|];
split; [rewrite (HKR (27%bv : bv 5) ltac:(cbv; tauto)); exact G27 | rewrite (HKR (9%bv : bv 5) ltac:(cbv; tauto)); exact G9]|]).
all: split; [exact I|].
all: split; [exact HKR|]; split; [exact HFK|];
split; [exact (lg_kept_ro _ _ _ _ _ HFr ltac:(lnp_ro_tac)) | intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)].
Qed.
End c.
Definition lnpc1_mem : smem :=
[ YQ0b.mkRegion (Some 33%nat) 0 4 0 0 [YQ0b.mkChunk 0 (CVal 4 (SOff 32 0))];
YQ0b.mkRegion (Some 9%nat) 184 416 0 0 [YQ0b.mkChunk 184 (CVal 8 (SOff 36 0)); YQ0b.mkChunk 312 (CVal 8 (SOff 40 0)); YQ0b.mkChunk 408 (CVal 8 (SOff 37 0))];
YQ0b.mkRegion (Some 35%nat) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SOff 34 0))] ].
Definition lnpc1_alias : list (sv * sv) := [ (SAlu ALU_ADD (SOff 23 0) (SAlu ALU_SLL (SOff 26 0) (SLit 2)), SOff 33 0); (SAlu ALU_ADD (SOff 36 1) (SOff 38 0), SOff 35 0) ].
Definition lnpc1_facts : facts :=
mkFacts [ (9%nat, mkAF (2^46) (2^47) 0); (26%nat, mkAF 1 (2^29 + 1) 0); (38%nat, mkAF 0 (2^29) 0);
(18%nat, mkAF (2^64 - 1 - 140737479966720) (2^64 - 1 - 4096) 0); (23%nat, mkAF 4096 140737479966720 4); (27%nat, mkAF SB SB 0);
(24%nat, mkAF 4096 140737479966720 0); (40%nat, mkAF 4096 140737479966720 0);
(32%nat, mkAF 0 (2^32 - 1) 0); (33%nat, mkAF 4096 140737479966720 2); (34%nat, mkAF 0 255 0); (35%nat, mkAF 4096 140737479966720 0);
(36%nat, mkAF 4096 140737479966720 0); (37%nat, mkAF (2^64 - 1 - 140737479966720) (2^64 - 1 - 4096) 0) ]
[ mkAC BC_GEU (SOff 24 0) (SOff 40 0) ] lnpc1_alias.
Definition lnpc1_regs := sr_set sr_atoms 25%bv (SOff 38 2).
Definition ss_LNPC1x : sstate := mkSS LNP_AC1 lnpc1_regs lnpc1_mem None lnpc1_facts.
Definition lnpc_SH1 : list shent := [ mkSHE 33 0 4; mkSHE 35 0 1; mkSHE 24 0 1 ].
Definition lnpc1_cond : sv := SF2 (FP2_cmp F_EQ FMT_S) (SF1 FP1_nanbox (SOff 32 0)) (SF1 (FP1_cvt FC_S FC_WU RNE) (SOff 34 0)).
Section e.
Variables (idx bidx pbef bb bn cur pimg pg pn : Z).
Hypothesis Hidx : 0 <= idx < 2 ^ 29. Hypothesis Hlen : 4 * (idx + 2) + 4 <= nF.
Hypothesis Hbidx : 0 <= bidx < 2 ^ 29.
Hypothesis HinB : In (bb, bn) (ablocks B lyc Sc). Hypothesis HB0 : bb <= pbef. Hypothesis HB1 : pbef + bidx + 3 <= bb + bn.
Hypothesis HBF : (bb, bn) <> (flt, nF).
Hypothesis HinG : In (pg, pn) (ablocks B lyc Sc). Hypothesis HG0 : pg <= pimg. Hypothesis Hcur0 : pimg <= cur. Hypothesis Hcur1 : cur < pg + pn.
Lemma LNP_seedC1 : forall (fy : FPState) (regs : bvmap 5 word) mem md (cv byv : Z),
lnp_base fy regs mem md -> getr regs 26 = w64 (idx + 1) -> getr regs 25 = w64 (bidx + 2) -> getr regs 24 = w64 cur ->
val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 184) 8 pbef -> val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 408) 8 (2 ^ 64 - 1 - pbef) ->
val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 312) 8 pimg ->
val_mem trbsegs (mrestrict (w_H W) mem) (flt + 4 * (idx + 1)) 4 cv -> 0 <= cv < 2 ^ 32 ->
mbyte trbsegs (mrestrict (w_H W) mem) (pbef + bidx + 1) = Some (Z_to_bv 8 byv) -> 0 <= byv < 256 ->
let E0 := Ereg regs (map (Z_to_bv 64) [cv; flt + 4 * (idx + 1); byv; pbef + bidx + 1; pbef; 2 ^ 64 - 1 - pbef; bidx; 0; pimg] ++ []) in
let E := ew_fregs E0 64 (@fp_regs fy) in
st_okF trbsegs E (mkSST LNP_AC1 lnpc1_regs (sfr_atoms 64) lnpc1_mem None lnpc1_facts)
(restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LNP_AC1) mem (seg_rom trbsegs))) /\
sh_ok trbsegs lnp_Bx lnpc_SH1 E (mrestrict (w_H W) mem) /\
(forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) /\
(forall r : bv 5, ew E (64 + ridx r)%nat = reg_get (@fp_regs fy) r) /\
bv_unsigned (ew E 38) = bidx.
Proof.
intros fy regs mem md cv byv HB GI G25 G24 Vp Vn Vpi Vc Hcv Hbvb Hbv E0 E.
pose proof (lnp_env fy regs mem md HB) as (Qf0 & Qf1 & Qf16 & QnF & C1 & Qs0 & Qs1 & Qs2).
pose proof HB as (HJ & Hfrm & G23 & G18 & G27 & G9).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb bn HAR HinB) as (_ & Hb4096 & Hbceil & _ & _ & _ & Hbn0).
pose proof (req_size_pos bn ltac:(lia)) as [_ Hrb].
pose proof (sep_blocks trbsegs _ LAWS lyc Sc _ _ _ bb bn flt nF HAR HinB HinF HBF) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pg pn HAR HinG) as (_ & Qg0 & Qg1 & _ & _ & _ & Hpn0).
pose proof (req_size_pos pn ltac:(lia)) as [_ Qpn].
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E0 j = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall j x, nth_error [cv; flt + 4 * (idx + 1); byv; pbef + bidx + 1; pbef; 2 ^ 64 - 1 - pbef; bidx; 0; pimg] j = Some x -> ew E0 (32 + j) = Z_to_bv 64 x) by (intros j x Hj; subst E0; apply Ereg_vals; exact Hj).
assert (HEE : forall j, (j < 64)%nat -> ew E j = ew E0 j) by (intros j Hj; subst E; apply ew_fregs_low; exact Hj).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr).
{ intros j rr Hj. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5. rewrite HEE by lia. apply HE0. exact Hj. }
assert (Rpb : 4096 <= pbef /\ pbef + bidx + 3 <= 140737479966720) by (clear - HB0 HB1 Hb4096 Hbceil Hrb C1 Hbidx; lia).
assert (Rpi : 4096 <= pimg /\ 4096 <= cur /\ cur < 140737479966720 /\ pimg < 140737479966720) by (clear - HG0 Hcur0 Hcur1 Qg0 Qg1 Qpn C1; lia).
assert (U9 : bv_unsigned (ew E0 9) = s1v) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Qs0 Qs1; lia).
assert (UI : bv_unsigned (ew E0 26) = idx + 1) by (rewrite (HE0 26%nat 26%bv eq_refl), GI; apply unsigned_lit_small; clear - Hidx; lia).
assert (U24 : bv_unsigned (ew E0 24) = cur) by (rewrite (HE0 24%nat 24%bv eq_refl), G24; apply unsigned_lit_small; clear - Rpi; lia).
assert (U23 : bv_unsigned (ew E0 23) = flt) by (rewrite (HE0 23%nat 23%bv eq_refl), G23; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Hidx Hlen; lia).
assert (U18 : bv_unsigned (ew E0 18) = 2 ^ 64 - 1 - flt) by (rewrite (HE0 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Hidx Hlen; lia).
assert (E27 : ew E0 27 = w64 SB) by (rewrite (HE0 27%nat 27%bv eq_refl); exact G27).
assert (A32 : bv_unsigned (ew E0 32) = cv) by (pose proof (HV 0%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hcv; lia).
assert (A33 : bv_unsigned (ew E0 33) = flt + 4 * (idx + 1)) by (pose proof (HV 1%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Hidx Hlen; lia).
assert (A34 : bv_unsigned (ew E0 34) = byv) by (pose proof (HV 2%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hbv; lia).
assert (A35 : bv_unsigned (ew E0 35) = pbef + bidx + 1) by (pose proof (HV 3%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Rpb Hbidx; lia).
assert (A36 : bv_unsigned (ew E0 36) = pbef) by (pose proof (HV 4%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Rpb Hbidx; lia).
assert (A37 : bv_unsigned (ew E0 37) = 2 ^ 64 - 1 - pbef) by (pose proof (HV 5%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Rpb Hbidx; lia).
assert (A38 : bv_unsigned (ew E0 38) = bidx) by (pose proof (HV 6%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hbidx; lia).
assert (A40 : bv_unsigned (ew E0 40) = pimg) by (pose proof (HV 8%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Rpi; lia).
assert (DN : forall j x, bv_unsigned (ew E0 j) = x -> sv_denot E0 (SOff j 0) = Z_to_bv 64 x).
{ intros j x Hj. cbn [sv_denot]. rewrite Hj, Z.add_0_r. reflexivity. }
pose proof (lnp_cell4 (idx + 1) Qf16) as Hf4.
assert (HS0 : @st_ok trbsegs fy E0 ss_LNPC1x (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LNP_AC1) mem (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LNPC1x, lnpc1_regs. apply (entry_st_ok_full trbsegs).
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X |]. rewrite G25. cbn [sv_denot]. change (Ereg regs _) with E0. rewrite A38. reflexivity.
- vm_compute. reflexivity.
- unfold lnpc1_mem. repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite A33.
split; [clear - Qf0 Hidx; lia|]. split; [clear - Qf1 QnF C1 Hidx Hlen; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trbsegs E0 _ (flt + 4 * (idx + 1)) 0 4 _ cv); [exact (DN _ _ A32) | zside | zside | rewrite Z.add_0_r; exact Vc].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite U9.
split; [clear - Qs0; lia|]. split; [clear - Qs1; lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
* apply (chunk_ok_val trbsegs E0 _ s1v 184 8 _ pbef); [exact (DN _ _ A36) | zside | zside | exact Vp].
* apply (chunk_ok_val trbsegs E0 _ s1v 312 8 _ pimg); [exact (DN _ _ A40) | zside | zside | exact Vpi].
* apply (chunk_ok_val trbsegs E0 _ s1v 408 8 _ (2 ^ 64 - 1 - pbef)); [exact (DN _ _ A37) | zside | zside | exact Vn].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite A35.
split; [clear - Rpb Hbidx; lia|]. split; [clear - Rpb; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trbsegs E0 _ (pbef + bidx + 1) 0 1 _ byv); [exact (DN _ _ A34) | zside | zside |].
apply (val_mem_byte trbsegs); [rewrite Z.add_0_r; exact Hbvb | exact Hbv].
- apply pairwise_disjoint_of_extents. unfold lnpc1_mem, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. change (Ereg regs _) with E0. rewrite A33, U9, A35.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
clear - Qs2 Qf1 QnF Hidx Hlen Hbidx HB0 HB1 Hrb Hbceil Hd. repeat split; lia.
- split; [|split; [split; [|exact I] | ]].
+ cbn [lnpc1_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (Ereg regs _) with E0.
rewrite U9, UI, A38, U18, U23, E27, U24, A40, A32, A33, A34, A35, A36, A37. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - Qs0 Qs1 C1 Hidx Hlen Hbidx Qf0 Qf1 Qf16 QnF Hcv Hbv Rpb Rpi Hf4. unfold SB.
repeat match goal with |- _ /\ _ => split end; lia.
+ unfold acond_ok. cbn [ac_c ac_a ac_b]. change (Ereg regs _) with E0. rewrite YO3v.branch_geu_U, !U_SOff, U24, A40, !Z.add_0_r.
rewrite !zcanon_id by (unfold M64; clear - Rpi; lia). apply Bool.negb_true_iff, Z.ltb_ge. exact Hcur0.
+ cbn [lnpc1_facts f_alias alias_ok lnpc1_alias]. change (Ereg regs _) with E0.
repeat match goal with |- _ /\ _ => split end; try exact I.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, UI, U23, A33, ?Z.add_0_r.
rewrite ?(zcanon_id flt), ?(zcanon_id (flt + 4)), (zcanon_id (idx + 1)) by (unfold M64; clear - Qf0 Qf1 QnF C1 Hidx Hlen; lia). change (Z.land (zcanon 2) 63) with 2.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite (zcanon_id ((idx + 1) * 4)) by (unfold M64; clear - Hidx; lia).
f_equal; lia.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, A36, A38, A35, ?Z.add_0_r.
rewrite ?(zcanon_id pbef), ?(zcanon_id (pbef + 1)), (zcanon_id bidx) by (unfold M64; clear - Rpb Hbidx; lia). f_equal; lia. }
assert (SHOK0 : sh_ok trbsegs lnp_Bx lnpc_SH1 E0 (mrestrict (w_H W) mem)).
{ unfold sh_ok, lnpc_SH1. constructor; [|constructor; [|constructor; [|constructor]]].
- apply (shent_ok_of_range trbsegs (w_H W) mem E0 lnp_Bx 33 (flt + 4 * (idx + 1)) 4 (flt + 4 * (idx + 1)) 0 4).
+ apply (range_addressable_of_block trbsegs B LAWS lyc Sc W mem md flt nF _ _ HAR HinF); clear - Hidx Hlen QnF; lia.
+ unfold U, lnp_Bx. cbn [sv_denot]. rewrite E27, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A33.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ flt nF HAR HinF) as Hfimg.
revert Hy Hia Hfimg Hidx Hlen QnF Qf0 Qf1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia.
- apply (shent_ok_of_range trbsegs (w_H W) mem E0 lnp_Bx 35 (pbef + bidx + 1) 1 (pbef + bidx + 1) 0 1).
+ apply (range_addressable_of_block trbsegs B LAWS lyc Sc W mem md bb bn _ _ HAR HinB); clear - HB0 HB1 Hrb Hbidx; lia.
+ unfold U, lnp_Bx. cbn [sv_denot]. rewrite E27, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A35.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ bb bn HAR HinB) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ bb bn HAR HinB) as Hbimg.
revert Hy Hia Hbimg HB0 HB1 Hrb Hbidx Hb4096 Hbceil C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia.
- apply (shent_ok_of_range trbsegs (w_H W) mem E0 lnp_Bx 24 cur 1 cur 0 1).
+ apply (range_addressable_of_block trbsegs B LAWS lyc Sc W mem md pg pn _ _ HAR HinG); clear - HG0 Hcur0 Hcur1 Qpn; lia.
+ unfold U, lnp_Bx. cbn [sv_denot]. rewrite E27, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U24.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ pg pn HAR HinG) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ pg pn HAR HinG) as Hgimg.
revert Hy Hia Hgimg HG0 Hcur0 Hcur1 Qpn Qg0 Qg1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia. }
split; [exact (st_ok_enterF trbsegs fy 64 E0 ss_LNPC1x _ HS0 ltac:(vm_compute; reflexivity) Hfrm)|].
split; [exact (sh_ok_agree trbsegs lnp_Bx lnpc_SH1 64 E0 E _ (env_agree_ew_fregs E0 64 _) ltac:(vm_compute; reflexivity) SHOK0)|].
split; [exact HE|]. split; [intros r; subst E; apply ew_fregs_at|]. rewrite HEE by lia. exact A38.
Qed.
Lemma LNP_C1 : forall (fy : FPState) (regs : bvmap 5 word) mem md,
lnp_base fy regs mem md -> getr regs 26 = w64 (idx + 1) -> getr regs 25 = w64 (bidx + 2) -> getr regs 24 = w64 cur ->
val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 184) 8 pbef -> val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 408) 8 (2 ^ 64 - 1 - pbef) ->
val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 312) 8 pimg ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LNP_AC1) mem (seg_rom trbsegs)) md)
(LNP_bpost fy regs mem LNP_CALL LNP_AC2 LNP_KEEP
(fun d regs' => True)).
Proof.
intros fy regs mem md HB GI G25 G24 Vp Vn Vpi.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof HB as (HJ & Hfrm & G23 & G18 & G27 & G9).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb bn HAR HinB) as (_ & _ & _ & _ & Hbpres & _ & Hbn0).
pose proof (req_size_pos bn ltac:(lia)) as [_ Hrb].
destruct (proj1 (Hbpres (pbef + bidx + 1) ltac:(clear - HB0 HB1 Hrb Hbidx; lia))) as (Hhid & pp & Hpp).
assert (Hbvb : mbyte trbsegs (mrestrict (w_H W) mem) (pbef + bidx + 1) = Some (Z_to_bv 8 (bv_unsigned pp))).
{ unfold mbyte, mrestrict. rewrite Hhid, Hpp, Z_to_bv_bv_unsigned. reflexivity. }
pose proof (bv_unsigned_in_range 8 pp) as Hbv. change (bv_modulus 8) with 256 in Hbv.
destruct (lnp_cell_val fy regs mem md (idx + 1) HB ltac:(lia) ltac:(lia)) as (cv & Hcv & Vc).
destruct (LNP_seedC1 fy regs mem md cv _ HB GI G25 G24 Vp Vn Vpi Vc Hcv Hbvb Hbv) as (HS & SHOK & HE & HEF & HU38).
set (E := ew_fregs _ 64 _) in HS, SHOK, HE, HEF, HU38.
assert (HAE96 : env_agree 96 E E) by (apply env_agree_refl).
apply (st_okF_branch trbsegs E _ _ _ BC_EQ lnpc1_cond (SLit 0) HS); clear HS; intros Hcnd HS; unfold lnpc1_cond in HS; cbn [neg_bc] in HS.
all: lazymatch type of Hcnd with
| _ = true => aj_run_to_tokF trbtbl_lib_ok HS HJ SHOK lnp_Bspan LNP_CALL
| _ => aj_run_to_tokF trbtbl_lib_ok HS HJ SHOK lnp_Bspan LNP_AC2 end;
[ cbn [ss_mem add_cond]; unfold lnpc1_mem; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil | ].
all: lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
all: lazymatch type of HS with st_okF _ ?Ex ?ssx ?msx =>
assert (HFK : forall r : bv 5, In r LNP_FKEEP -> reg_get (ms_fregs msx) r = reg_get (@fp_regs fy) r)
by (apply (st_okF_fregs_kept trbsegs Ex ssx msx 64 (@fp_regs fy) LNP_FKEEP HS);
[ intros r; first [ apply HEF | rewrite (proj1 HAEx) by (pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5; unfold ridx; lia); apply HEF ]
| vm_compute; reflexivity ]) end.
all: pose proof (st_okF_frm trbsegs _ _ _ HS) as Hfrm'; pose proof (st_okF_to_legacy trbsegs _ _ _ HS) as HSL; clear HS.
all: lazymatch type of HSL with st_ok _ ?Ex _ _ =>
assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) [cv; flt + 4 * (idx + 1); bv_unsigned pp; pbef + bidx + 1; pbef; 2 ^ 64 - 1 - pbef; bidx; 0; pimg] ++ [])) Ex)
by (destruct HAEx as [EA ED]; split; [intros j Hj; rewrite ?EA by lia; subst E; rewrite ew_fregs_low by lia; reflexivity | rewrite ?ED; reflexivity]) end.
all: pose proof (regs_kept_of_st_ok trbsegs _ _ _ regs _ LNP_KEEPC HSL HAE' ltac:(vm_compute; reflexivity)) as HKR0; cbn [ms_regs restrict] in HKR0.
all: assert (R25 : getr (ms_regs ms) 25 = getr regs 25)
by (rewrite (st_ok_restrict_reg trbsegs (w_H W) _ _ ms (25%bv : bv 5) HSL);
lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
cbn [sv_denot]; rewrite (proj1 HAEx), HU38, G25 by lia; reflexivity).
all: assert (HKR : forall r : bv 5, In r LNP_KEEP -> getr (ms_regs ms) r = getr regs r)
by (intros r Hr; destruct (lnp_keepc_cases r Hr) as [-> | Hr0]; [exact R25 | exact (HKR0 r Hr0)]).
all: rewrite (st_ok_restrict_mkst trbsegs (w_H W) _ _ ms HSL eq_refl); cbn [ss_pc]; apply SRr_ret.
all: split; [reflexivity|].
1: exists true, (fp_of (restrict (w_H W) ms)), (ms_regs ms), (ms_mem ms); eexists; split; [reflexivity|].
2: exists false, (fp_of (restrict (w_H W) ms)), (ms_regs ms), (ms_mem ms); eexists; split; [reflexivity|].
all: (split; [split; [exact HJ|]; split; [exact Hfrm'|]; split; [rewrite (HKR (23%bv : bv 5) ltac:(cbv; tauto)); exact G23|];
split; [rewrite (HKR (18%bv : bv 5) ltac:(cbv; tauto)); exact G18|];
split; [rewrite (HKR (27%bv : bv 5) ltac:(cbv; tauto)); exact G27 | rewrite (HKR (9%bv : bv 5) ltac:(cbv; tauto)); exact G9]|]).
all: split; [exact I|].
all: split; [exact HKR|]; split; [exact HFK|];
split; [exact (lg_kept_ro _ _ _ _ _ HFr ltac:(lnp_ro_tac)) | intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)].
Qed.
End e.
Definition lnpc2_mem : smem :=
[ YQ0b.mkRegion (Some 33%nat) 0 4 0 0 [YQ0b.mkChunk 0 (CVal 4 (SOff 32 0))];
YQ0b.mkRegion (Some 9%nat) 184 416 0 0 [YQ0b.mkChunk 184 (CVal 8 (SOff 36 0)); YQ0b.mkChunk 312 (CVal 8 (SOff 40 0)); YQ0b.mkChunk 408 (CVal 8 (SOff 37 0))];
YQ0b.mkRegion (Some 35%nat) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SOff 34 0))] ].
Definition lnpc2_alias : list (sv * sv) := [ (SAlu ALU_ADD (SOff 23 4) (SAlu ALU_SLL (SOff 26 0) (SLit 2)), SOff 33 0); (SAlu ALU_ADD (SOff 36 2) (SOff 38 0), SOff 35 0) ].
Definition lnpc2_facts : facts :=
mkFacts [ (9%nat, mkAF (2^46) (2^47) 0); (26%nat, mkAF 1 (2^29 + 1) 0); (38%nat, mkAF 0 (2^29) 0);
(18%nat, mkAF (2^64 - 1 - 140737479966720) (2^64 - 1 - 4096) 0); (23%nat, mkAF 4096 140737479966720 4); (27%nat, mkAF SB SB 0);
(24%nat, mkAF 4096 140737479966720 0); (40%nat, mkAF 4096 140737479966720 0);
(32%nat, mkAF 0 (2^32 - 1) 0); (33%nat, mkAF 4096 140737479966720 2); (34%nat, mkAF 0 255 0); (35%nat, mkAF 4096 140737479966720 0);
(36%nat, mkAF 4096 140737479966720 0); (37%nat, mkAF (2^64 - 1 - 140737479966720) (2^64 - 1 - 4096) 0) ]
[ mkAC BC_GEU (SOff 24 0) (SOff 40 0) ] lnpc2_alias.
Definition lnpc2_regs := sr_set sr_atoms 25%bv (SOff 38 2).
Definition ss_LNPC2x : sstate := mkSS LNP_AC2 lnpc2_regs lnpc2_mem None lnpc2_facts.
Definition lnpc_SH2 : list shent := [ mkSHE 33 0 4; mkSHE 35 0 1; mkSHE 24 0 1 ].
Definition lnpc2_cond : sv := SF2 (FP2_cmp F_EQ FMT_S) (SF1 FP1_nanbox (SOff 32 0)) (SF1 (FP1_cvt FC_S FC_WU RNE) (SOff 34 0)).
Section f.
Variables (idx bidx pbef bb bn cur pimg pg pn : Z).
Hypothesis Hidx : 0 <= idx < 2 ^ 29. Hypothesis Hlen : 4 * (idx + 2) + 4 <= nF.
Hypothesis Hbidx : 0 <= bidx < 2 ^ 29.
Hypothesis HinB : In (bb, bn) (ablocks B lyc Sc). Hypothesis HB0 : bb <= pbef. Hypothesis HB1 : pbef + bidx + 3 <= bb + bn.
Hypothesis HBF : (bb, bn) <> (flt, nF).
Hypothesis HinG : In (pg, pn) (ablocks B lyc Sc). Hypothesis HG0 : pg <= pimg. Hypothesis Hcur0 : pimg <= cur. Hypothesis Hcur1 : cur < pg + pn.
Lemma LNP_seedC2 : forall (fy : FPState) (regs : bvmap 5 word) mem md (cv byv : Z),
lnp_base fy regs mem md -> getr regs 26 = w64 (idx + 1) -> getr regs 25 = w64 (bidx + 2) -> getr regs 24 = w64 cur ->
val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 184) 8 pbef -> val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 408) 8 (2 ^ 64 - 1 - pbef) ->
val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 312) 8 pimg ->
val_mem trbsegs (mrestrict (w_H W) mem) (flt + 4 * (idx + 2)) 4 cv -> 0 <= cv < 2 ^ 32 ->
mbyte trbsegs (mrestrict (w_H W) mem) (pbef + bidx + 2) = Some (Z_to_bv 8 byv) -> 0 <= byv < 256 ->
let E0 := Ereg regs (map (Z_to_bv 64) [cv; flt + 4 * (idx + 2); byv; pbef + bidx + 2; pbef; 2 ^ 64 - 1 - pbef; bidx; 0; pimg] ++ []) in
let E := ew_fregs E0 64 (@fp_regs fy) in
st_okF trbsegs E (mkSST LNP_AC2 lnpc2_regs (sfr_atoms 64) lnpc2_mem None lnpc2_facts)
(restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LNP_AC2) mem (seg_rom trbsegs))) /\
sh_ok trbsegs lnp_Bx lnpc_SH2 E (mrestrict (w_H W) mem) /\
(forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) /\
(forall r : bv 5, ew E (64 + ridx r)%nat = reg_get (@fp_regs fy) r) /\
bv_unsigned (ew E 38) = bidx.
Proof.
intros fy regs mem md cv byv HB GI G25 G24 Vp Vn Vpi Vc Hcv Hbvb Hbv E0 E.
pose proof (lnp_env fy regs mem md HB) as (Qf0 & Qf1 & Qf16 & QnF & C1 & Qs0 & Qs1 & Qs2).
pose proof HB as (HJ & Hfrm & G23 & G18 & G27 & G9).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb bn HAR HinB) as (_ & Hb4096 & Hbceil & _ & _ & _ & Hbn0).
pose proof (req_size_pos bn ltac:(lia)) as [_ Hrb].
pose proof (sep_blocks trbsegs _ LAWS lyc Sc _ _ _ bb bn flt nF HAR HinB HinF HBF) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pg pn HAR HinG) as (_ & Qg0 & Qg1 & _ & _ & _ & Hpn0).
pose proof (req_size_pos pn ltac:(lia)) as [_ Qpn].
assert (HE0 : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E0 j = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall j x, nth_error [cv; flt + 4 * (idx + 2); byv; pbef + bidx + 2; pbef; 2 ^ 64 - 1 - pbef; bidx; 0; pimg] j = Some x -> ew E0 (32 + j) = Z_to_bv 64 x) by (intros j x Hj; subst E0; apply Ereg_vals; exact Hj).
assert (HEE : forall j, (j < 64)%nat -> ew E j = ew E0 j) by (intros j Hj; subst E; apply ew_fregs_low; exact Hj).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr).
{ intros j rr Hj. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5. rewrite HEE by lia. apply HE0. exact Hj. }
assert (Rpb : 4096 <= pbef /\ pbef + bidx + 3 <= 140737479966720) by (clear - HB0 HB1 Hb4096 Hbceil Hrb C1 Hbidx; lia).
assert (Rpi : 4096 <= pimg /\ 4096 <= cur /\ cur < 140737479966720 /\ pimg < 140737479966720) by (clear - HG0 Hcur0 Hcur1 Qg0 Qg1 Qpn C1; lia).
assert (U9 : bv_unsigned (ew E0 9) = s1v) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Qs0 Qs1; lia).
assert (UI : bv_unsigned (ew E0 26) = idx + 1) by (rewrite (HE0 26%nat 26%bv eq_refl), GI; apply unsigned_lit_small; clear - Hidx; lia).
assert (U24 : bv_unsigned (ew E0 24) = cur) by (rewrite (HE0 24%nat 24%bv eq_refl), G24; apply unsigned_lit_small; clear - Rpi; lia).
assert (U23 : bv_unsigned (ew E0 23) = flt) by (rewrite (HE0 23%nat 23%bv eq_refl), G23; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Hidx Hlen; lia).
assert (U18 : bv_unsigned (ew E0 18) = 2 ^ 64 - 1 - flt) by (rewrite (HE0 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Hidx Hlen; lia).
assert (E27 : ew E0 27 = w64 SB) by (rewrite (HE0 27%nat 27%bv eq_refl); exact G27).
assert (A32 : bv_unsigned (ew E0 32) = cv) by (pose proof (HV 0%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hcv; lia).
assert (A33 : bv_unsigned (ew E0 33) = flt + 4 * (idx + 2)) by (pose proof (HV 1%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Qf0 Qf1 QnF C1 Hidx Hlen; lia).
assert (A34 : bv_unsigned (ew E0 34) = byv) by (pose proof (HV 2%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hbv; lia).
assert (A35 : bv_unsigned (ew E0 35) = pbef + bidx + 2) by (pose proof (HV 3%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Rpb Hbidx; lia).
assert (A36 : bv_unsigned (ew E0 36) = pbef) by (pose proof (HV 4%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Rpb Hbidx; lia).
assert (A37 : bv_unsigned (ew E0 37) = 2 ^ 64 - 1 - pbef) by (pose proof (HV 5%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Rpb Hbidx; lia).
assert (A38 : bv_unsigned (ew E0 38) = bidx) by (pose proof (HV 6%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Hbidx; lia).
assert (A40 : bv_unsigned (ew E0 40) = pimg) by (pose proof (HV 8%nat _ eq_refl) as X; cbn [Nat.add] in X; rewrite X; apply unsigned_lit_small; clear - Rpi; lia).
assert (DN : forall j x, bv_unsigned (ew E0 j) = x -> sv_denot E0 (SOff j 0) = Z_to_bv 64 x).
{ intros j x Hj. cbn [sv_denot]. rewrite Hj, Z.add_0_r. reflexivity. }
pose proof (lnp_cell4 (idx + 2) Qf16) as Hf4.
assert (HS0 : @st_ok trbsegs fy E0 ss_LNPC2x (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 LNP_AC2) mem (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_LNPC2x, lnpc2_regs. apply (entry_st_ok_full trbsegs).
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X |]. rewrite G25. cbn [sv_denot]. change (Ereg regs _) with E0. rewrite A38. reflexivity.
- vm_compute. reflexivity.
- unfold lnpc2_mem. repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite A33.
split; [clear - Qf0 Hidx; lia|]. split; [clear - Qf1 QnF C1 Hidx Hlen; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trbsegs E0 _ (flt + 4 * (idx + 2)) 0 4 _ cv); [exact (DN _ _ A32) | zside | zside | rewrite Z.add_0_r; exact Vc].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite U9.
split; [clear - Qs0; lia|]. split; [clear - Qs1; lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
* apply (chunk_ok_val trbsegs E0 _ s1v 184 8 _ pbef); [exact (DN _ _ A36) | zside | zside | exact Vp].
* apply (chunk_ok_val trbsegs E0 _ s1v 312 8 _ pimg); [exact (DN _ _ A40) | zside | zside | exact Vpi].
* apply (chunk_ok_val trbsegs E0 _ s1v 408 8 _ (2 ^ 64 - 1 - pbef)); [exact (DN _ _ A37) | zside | zside | exact Vn].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. change (Ereg regs _) with E0. rewrite A35.
split; [clear - Rpb Hbidx; lia|]. split; [clear - Rpb; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trbsegs E0 _ (pbef + bidx + 2) 0 1 _ byv); [exact (DN _ _ A34) | zside | zside |].
apply (val_mem_byte trbsegs); [rewrite Z.add_0_r; exact Hbvb | exact Hbv].
- apply pairwise_disjoint_of_extents. unfold lnpc2_mem, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. change (Ereg regs _) with E0. rewrite A33, U9, A35.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
clear - Qs2 Qf1 QnF Hidx Hlen Hbidx HB0 HB1 Hrb Hbceil Hd. repeat split; lia.
- split; [|split; [split; [|exact I] | ]].
+ cbn [lnpc2_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (Ereg regs _) with E0.
rewrite U9, UI, A38, U18, U23, E27, U24, A40, A32, A33, A34, A35, A36, A37. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - Qs0 Qs1 C1 Hidx Hlen Hbidx Qf0 Qf1 Qf16 QnF Hcv Hbv Rpb Rpi Hf4. unfold SB.
repeat match goal with |- _ /\ _ => split end; lia.
+ unfold acond_ok. cbn [ac_c ac_a ac_b]. change (Ereg regs _) with E0. rewrite YO3v.branch_geu_U, !U_SOff, U24, A40, !Z.add_0_r.
rewrite !zcanon_id by (unfold M64; clear - Rpi; lia). apply Bool.negb_true_iff, Z.ltb_ge. exact Hcur0.
+ cbn [lnpc2_facts f_alias alias_ok lnpc2_alias]. change (Ereg regs _) with E0.
repeat match goal with |- _ /\ _ => split end; try exact I.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, UI, U23, A33, ?Z.add_0_r.
rewrite ?(zcanon_id flt), ?(zcanon_id (flt + 4)), (zcanon_id (idx + 1)) by (unfold M64; clear - Qf0 Qf1 QnF C1 Hidx Hlen; lia). change (Z.land (zcanon 2) 63) with 2.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite (zcanon_id ((idx + 1) * 4)) by (unfold M64; clear - Hidx; lia).
f_equal; lia.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, A36, A38, A35, ?Z.add_0_r.
rewrite ?(zcanon_id pbef), ?(zcanon_id (pbef + 2)), (zcanon_id bidx) by (unfold M64; clear - Rpb Hbidx; lia). f_equal; lia. }
assert (SHOK0 : sh_ok trbsegs lnp_Bx lnpc_SH2 E0 (mrestrict (w_H W) mem)).
{ unfold sh_ok, lnpc_SH2. constructor; [|constructor; [|constructor; [|constructor]]].
- apply (shent_ok_of_range trbsegs (w_H W) mem E0 lnp_Bx 33 (flt + 4 * (idx + 2)) 4 (flt + 4 * (idx + 2)) 0 4).
+ apply (range_addressable_of_block trbsegs B LAWS lyc Sc W mem md flt nF _ _ HAR HinF); clear - Hidx Hlen QnF; lia.
+ unfold U, lnp_Bx. cbn [sv_denot]. rewrite E27, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A33.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ flt nF HAR HinF) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ flt nF HAR HinF) as Hfimg.
revert Hy Hia Hfimg Hidx Hlen QnF Qf0 Qf1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia.
- apply (shent_ok_of_range trbsegs (w_H W) mem E0 lnp_Bx 35 (pbef + bidx + 2) 1 (pbef + bidx + 2) 0 1).
+ apply (range_addressable_of_block trbsegs B LAWS lyc Sc W mem md bb bn _ _ HAR HinB); clear - HB0 HB1 Hrb Hbidx; lia.
+ unfold U, lnp_Bx. cbn [sv_denot]. rewrite E27, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A35.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ bb bn HAR HinB) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ bb bn HAR HinB) as Hbimg.
revert Hy Hia Hbimg HB0 HB1 Hrb Hbidx Hb4096 Hbceil C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia.
- apply (shent_ok_of_range trbsegs (w_H W) mem E0 lnp_Bx 24 cur 1 cur 0 1).
+ apply (range_addressable_of_block trbsegs B LAWS lyc Sc W mem md pg pn _ _ HAR HinG); clear - HG0 Hcur0 Hcur1 Qpn; lia.
+ unfold U, lnp_Bx. cbn [sv_denot]. rewrite E27, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U24.
+ lia.
+ lia.
+ intros y Hy. destruct (al_blocks _ _ LAWS _ _ _ _ _ pg pn HAR HinG) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ pg pn HAR HinG) as Hgimg.
revert Hy Hia Hgimg HG0 Hcur0 Hcur1 Qpn Qg0 Qg1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia. }
split; [exact (st_ok_enterF trbsegs fy 64 E0 ss_LNPC2x _ HS0 ltac:(vm_compute; reflexivity) Hfrm)|].
split; [exact (sh_ok_agree trbsegs lnp_Bx lnpc_SH2 64 E0 E _ (env_agree_ew_fregs E0 64 _) ltac:(vm_compute; reflexivity) SHOK0)|].
split; [exact HE|]. split; [intros r; subst E; apply ew_fregs_at|]. rewrite HEE by lia. exact A38.
Qed.
Lemma LNP_C2 : forall (fy : FPState) (regs : bvmap 5 word) mem md,
lnp_base fy regs mem md -> getr regs 26 = w64 (idx + 1) -> getr regs 25 = w64 (bidx + 2) -> getr regs 24 = w64 cur ->
val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 184) 8 pbef -> val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 408) 8 (2 ^ 64 - 1 - pbef) ->
val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 312) 8 pimg ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LNP_AC2) mem (seg_rom trbsegs)) md)
(LNP_bpost fy regs mem LNP_CALL LNP_STORE LNP_KEEP
(fun d regs' => d = false -> getr regs' 10 = w64 (2 ^ 64 - 1))).
Proof.
intros fy regs mem md HB GI G25 G24 Vp Vn Vpi.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof HB as (HJ & Hfrm & G23 & G18 & G27 & G9).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb bn HAR HinB) as (_ & _ & _ & _ & Hbpres & _ & Hbn0).
pose proof (req_size_pos bn ltac:(lia)) as [_ Hrb].
destruct (proj1 (Hbpres (pbef + bidx + 2) ltac:(clear - HB0 HB1 Hrb Hbidx; lia))) as (Hhid & pp & Hpp).
assert (Hbvb : mbyte trbsegs (mrestrict (w_H W) mem) (pbef + bidx + 2) = Some (Z_to_bv 8 (bv_unsigned pp))).
{ unfold mbyte, mrestrict. rewrite Hhid, Hpp, Z_to_bv_bv_unsigned. reflexivity. }
pose proof (bv_unsigned_in_range 8 pp) as Hbv. change (bv_modulus 8) with 256 in Hbv.
destruct (lnp_cell_val fy regs mem md (idx + 2) HB ltac:(lia) ltac:(lia)) as (cv & Hcv & Vc).
destruct (LNP_seedC2 fy regs mem md cv _ HB GI G25 G24 Vp Vn Vpi Vc Hcv Hbvb Hbv) as (HS & SHOK & HE & HEF & HU38).
set (E := ew_fregs _ 64 _) in HS, SHOK, HE, HEF, HU38.
assert (HAE96 : env_agree 96 E E) by (apply env_agree_refl).
apply (st_okF_branch trbsegs E _ _ _ BC_EQ lnpc2_cond (SLit 0) HS); clear HS; intros Hcnd HS; unfold lnpc2_cond in HS; cbn [neg_bc] in HS.
all: lazymatch type of Hcnd with
| _ = true => aj_run_to_tokF trbtbl_lib_ok HS HJ SHOK lnp_Bspan LNP_CALL
| _ => aj_run_to_tokF trbtbl_lib_ok HS HJ SHOK lnp_Bspan LNP_STORE end;
[ cbn [ss_mem add_cond]; unfold lnpc2_mem; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil | ].
all: lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
all: lazymatch type of HS with st_okF _ ?Ex ?ssx ?msx =>
assert (HFK : forall r : bv 5, In r LNP_FKEEP -> reg_get (ms_fregs msx) r = reg_get (@fp_regs fy) r)
by (apply (st_okF_fregs_kept trbsegs Ex ssx msx 64 (@fp_regs fy) LNP_FKEEP HS);
[ intros r; first [ apply HEF | rewrite (proj1 HAEx) by (pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5; unfold ridx; lia); apply HEF ]
| vm_compute; reflexivity ]) end.
all: pose proof (st_okF_frm trbsegs _ _ _ HS) as Hfrm'; pose proof (st_okF_to_legacy trbsegs _ _ _ HS) as HSL; clear HS.
all: lazymatch type of HSL with st_ok _ ?Ex _ _ =>
assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) [cv; flt + 4 * (idx + 2); bv_unsigned pp; pbef + bidx + 2; pbef; 2 ^ 64 - 1 - pbef; bidx; 0; pimg] ++ [])) Ex)
by (destruct HAEx as [EA ED]; split; [intros j Hj; rewrite ?EA by lia; subst E; rewrite ew_fregs_low by lia; reflexivity | rewrite ?ED; reflexivity]) end.
all: pose proof (regs_kept_of_st_ok trbsegs _ _ _ regs _ LNP_KEEPC HSL HAE' ltac:(vm_compute; reflexivity)) as HKR0; cbn [ms_regs restrict] in HKR0.
all: assert (R25 : getr (ms_regs ms) 25 = getr regs 25)
by (rewrite (st_ok_restrict_reg trbsegs (w_H W) _ _ ms (25%bv : bv 5) HSL);
lazymatch goal with |- sv_denot ?Ex (sr_get ?rs ?r) = _ => let v := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with v end;
cbn [sv_denot]; rewrite (proj1 HAEx), HU38, G25 by lia; reflexivity).
all: assert (HKR : forall r : bv 5, In r LNP_KEEP -> getr (ms_regs ms) r = getr regs r)
by (intros r Hr; destruct (lnp_keepc_cases r Hr) as [-> | Hr0]; [exact R25 | exact (HKR0 r Hr0)]).
2: rreg HSL (10%bv : bv 5) R10.
all: rewrite (st_ok_restrict_mkst trbsegs (w_H W) _ _ ms HSL eq_refl); cbn [ss_pc]; apply SRr_ret.
all: split; [reflexivity|].
1: exists true, (fp_of (restrict (w_H W) ms)), (ms_regs ms), (ms_mem ms); eexists; split; [reflexivity|].
2: exists false, (fp_of (restrict (w_H W) ms)), (ms_regs ms), (ms_mem ms); eexists; split; [reflexivity|].
all: (split; [split; [exact HJ|]; split; [exact Hfrm'|]; split; [rewrite (HKR (23%bv : bv 5) ltac:(cbv; tauto)); exact G23|];
split; [rewrite (HKR (18%bv : bv 5) ltac:(cbv; tauto)); exact G18|];
split; [rewrite (HKR (27%bv : bv 5) ltac:(cbv; tauto)); exact G27 | rewrite (HKR (9%bv : bv 5) ltac:(cbv; tauto)); exact G9]|]).
1: split; [intros X; discriminate X|].
2: split; [intros _; exact R10|].
all: split; [exact HKR|]; split; [exact HFK|];
split; [exact (lg_kept_ro _ _ _ _ _ HFr ltac:(lnp_ro_tac)) | intros a Ha; exact (apresent_grows _ _ _ _ HG Ha)].
Qed.
End f.
Definition lnp_rel (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (fy' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
(forall r : bv 5, In r LNP_KEEP -> getr regs' r = getr regs r) /\
(forall r : bv 5, In r LNP_FKEEP -> reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Lemma lnp_rel_trans : forall fy regs mem fy1 regs1 mem1 fy2 regs2 mem2,
lnp_rel fy regs mem fy1 regs1 mem1 -> lnp_rel fy1 regs1 mem1 fy2 regs2 mem2 -> lnp_rel fy regs mem fy2 regs2 mem2.
Proof.
intros fy regs mem fy1 regs1 mem1 fy2 regs2 mem2 (K1 & F1 & M1 & X1) (K2 & F2 & M2 & X2).
split; [intros r Hr; rewrite (K2 r Hr); exact (K1 r Hr)|]. split; [intros r Hr; rewrite (F2 r Hr); exact (F1 r Hr)|].
split; [intros a Ha; rewrite (M2 a Ha); exact (M1 a Ha)|]. intros a Ha. apply X2. apply X1. exact Ha.
Qed.
Lemma lnp_slot_kept : forall (mem mem' : word -> option byte) a v,
(forall x, 0 <= x < 2 ^ 64 -> aview trbsegs (w_H W) mem' x = aview trbsegs (w_H W) mem x) -> 0 <= a -> a + 8 <= 2 ^ 64 ->
val_mem trbsegs (mrestrict (w_H W) mem) a 8 v -> val_mem trbsegs (mrestrict (w_H W) mem') a 8 v.
Proof. intros mem mem' a v Hm Ha0 Ha1 V. apply (YCcz.val_mem_kept trbsegs (w_H W) (w_H W) mem mem' a 8 v); [|exact V]. intros j Hj. apply Hm. lia. Qed.
Section g.
Variables (ha idx bidx pbef bb bn cur pimg pg pn : Z).
Hypothesis Hha : 0 <= ha < 2 ^ 64. Hypothesis Hidx : 0 <= idx < 2 ^ 29. Hypothesis Hpbef : 0 <= pbef < 2 ^ 64.
Hypothesis HlenA : ha <> 0 -> 4 * (idx + 3) + 4 <= nF.
Hypothesis HlenC : ha = 0 -> pbef <> 0 -> 4 * (idx + 2) + 4 <= nF.
Hypothesis HBef : ha = 0 -> pbef <> 0 ->
0 <= bidx < 2 ^ 29 /\ In (bb, bn) (ablocks B lyc Sc) /\ bb <= pbef /\ pbef + bidx + 3 <= bb + bn /\ (bb, bn) <> (flt, nF).
Hypothesis HinG : In (pg, pn) (ablocks B lyc Sc). Hypothesis HG0 : pg <= pimg. Hypothesis Hcur0 : pimg <= cur. Hypothesis Hcur1 : cur < pg + pn.
Definition lnp_QF (d : bool) (regs' : bvmap 5 word) : Prop := getr regs' 12 = w64 idx /\ (d = false -> getr regs' 10 = w64 (2 ^ 64 - 1)).
Lemma lnp_fin : forall fy regs mem (d : bool) (fy1 : FPState) regs1 mem1 (fy2 : FPState) regs2 mem2 md2,
(forall r : bv 5, In r LNP_KEEPH -> getr regs1 r = getr regs r) ->
(forall r : bv 5, In r LNP_FKEEP -> reg_get (@fp_regs fy1) r = reg_get (@fp_regs fy) r) ->
(forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) mem1 a = aview trbsegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a) ->
getr regs1 12 = w64 idx ->
lnp_rel fy1 regs1 mem1 fy2 regs2 mem2 -> lnp_base fy2 regs2 mem2 md2 -> (d = false -> getr regs2 10 = w64 (2 ^ 64 - 1)) ->
LNP_bpost fy regs mem LNP_CALL LNP_STORE LNP_KEEPH lnp_QF W (mkCfg (@mkst fy2 regs2 (Z_to_bv 64 (if d then LNP_CALL else LNP_STORE)) mem2 (seg_rom trbsegs)) md2).
Proof.
intros fy regs mem d fy1 regs1 mem1 fy2 regs2 mem2 md2 K1 F1 M1 X1 R12 (K2 & F2 & M2 & X2) HB2 H10.
split; [reflexivity|]. exists d, fy2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HB2|].
split; [split; [rewrite (K2 (12%bv : bv 5) ltac:(left; reflexivity)); exact R12 | exact H10]|].
split; [intros r Hr; rewrite (K2 r ltac:(right; exact Hr)); exact (K1 r Hr)|].
split; [intros r Hr; rewrite (F2 r Hr); exact (F1 r Hr)|].
split; [intros a Ha; rewrite (M2 a Ha); exact (M1 a Ha)|]. intros a Ha. apply X2. apply X1. exact Ha.
Qed.
Lemma LNP_block : forall (fy : FPState) (regs : bvmap 5 word) mem md,
lnp_base fy regs mem md -> getr regs 26 = w64 (idx + 1) -> getr regs 25 = w64 (bidx + 2) -> getr regs 24 = w64 cur ->
val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 168) 8 ha -> val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 184) 8 pbef ->
val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 312) 8 pimg -> val_mem trbsegs (mrestrict (w_H W) mem) (s1v + 408) 8 (2 ^ 64 - 1 - pbef) ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LNP_HEAD) mem (seg_rom trbsegs)) md)
(LNP_bpost fy regs mem LNP_CALL LNP_STORE LNP_KEEPH lnp_QF).
Proof.
intros fy regs mem md HB G26 G25 G24 Vh Vp Vpi Vn.
pose proof (lnp_env fy regs mem md HB) as (_ & _ & _ & _ & _ & Qs0 & Qs1 & _).
eapply SRr_bind; [exact (LNP_H fy regs mem md idx ha HB G26 Hidx Vh Hha)|].
intros W' c' _ (-> & fy1 & regs1 & mem1 & md1 & -> & HB1 & R12 & HK1 & HF1 & HM1 & HX1).
assert (Vp1 : val_mem trbsegs (mrestrict (w_H W) mem1) (s1v + 184) 8 pbef) by (apply (lnp_slot_kept mem mem1 _ _ HM1); [clear - Qs0 Qs1; lia | clear - Qs0 Qs1; lia | exact Vp]).
assert (Vpi1 : val_mem trbsegs (mrestrict (w_H W) mem1) (s1v + 312) 8 pimg) by (apply (lnp_slot_kept mem mem1 _ _ HM1); [clear - Qs0 Qs1; lia | clear - Qs0 Qs1; lia | exact Vpi]).
assert (Vn1 : val_mem trbsegs (mrestrict (w_H W) mem1) (s1v + 408) 8 (2 ^ 64 - 1 - pbef)) by (apply (lnp_slot_kept mem mem1 _ _ HM1); [clear - Qs0 Qs1; lia | clear - Qs0 Qs1; lia | exact Vn]).
assert (G26a : getr regs1 26 = w64 (idx + 1)) by (rewrite (HK1 (26%bv : bv 5) ltac:(cbv; tauto)); exact G26).
assert (G25a : getr regs1 25 = w64 (bidx + 2)) by (rewrite (HK1 (25%bv : bv 5) ltac:(cbv; tauto)); exact G25).
assert (G24a : getr regs1 24 = w64 cur) by (rewrite (HK1 (24%bv : bv 5) ltac:(cbv; tauto)); exact G24).
destruct (ha =? 0) eqn:Eha.
-
apply Z.eqb_eq in Eha.
eapply SRr_bind; [exact (LNP_N fy1 regs1 mem1 md1 pbef HB1 Vp1 Hpbef)|].
intros W2 c2 _ (-> & fy2 & regs2 & mem2 & md2 & -> & HB2 & _ & HK2 & HF2 & HM2 & HX2).
assert (REL2 : lnp_rel fy1 regs1 mem1 fy2 regs2 mem2) by (exact (conj HK2 (conj HF2 (conj HM2 HX2)))).
destruct (pbef =? 0) eqn:Epb.
+ apply SRr_ret. apply (lnp_fin fy regs mem true fy1 regs1 mem1 fy2 regs2 mem2 md2 HK1 HF1 HM1 HX1 R12 REL2 HB2). intros X; discriminate X.
+ apply Z.eqb_neq in Epb.
destruct (HBef Eha Epb) as (Hbi & HinB & HB0 & HB1' & HBF). pose proof (HlenC Eha Epb) as Hlc.
assert (R12b : getr regs2 12 = w64 idx) by (rewrite (HK2 (12%bv : bv 5) ltac:(left; reflexivity)); exact R12).
assert (G26b : getr regs2 26 = w64 (idx + 1)) by (rewrite (HK2 (26%bv : bv 5) ltac:(cbv; tauto)); exact G26a).
assert (G25b : getr regs2 25 = w64 (bidx + 2)) by (rewrite (HK2 (25%bv : bv 5) ltac:(cbv; tauto)); exact G25a).
assert (G24b : getr regs2 24 = w64 cur) by (rewrite (HK2 (24%bv : bv 5) ltac:(cbv; tauto)); exact G24a).
assert (Vp2 : val_mem trbsegs (mrestrict (w_H W) mem2) (s1v + 184) 8 pbef) by (apply (lnp_slot_kept mem1 mem2 _ _ HM2); [clear - Qs0 Qs1; lia | clear - Qs0 Qs1; lia | exact Vp1]).
assert (Vpi2 : val_mem trbsegs (mrestrict (w_H W) mem2) (s1v + 312) 8 pimg) by (apply (lnp_slot_kept mem1 mem2 _ _ HM2); [clear - Qs0 Qs1; lia | clear - Qs0 Qs1; lia | exact Vpi1]).
assert (Vn2 : val_mem trbsegs (mrestrict (w_H W) mem2) (s1v + 408) 8 (2 ^ 64 - 1 - pbef)) by (apply (lnp_slot_kept mem1 mem2 _ _ HM2); [clear - Qs0 Qs1; lia | clear - Qs0 Qs1; lia | exact Vn1]).
eapply SRr_bind; [exact (LNP_C0 idx bidx pbef bb bn cur pimg pg pn Hidx Hlc Hbi HinB HB0 HB1' HBF HinG HG0 Hcur0 Hcur1 fy2 regs2 mem2 md2 HB2 R12b G25b G24b Vp2 Vn2 Vpi2)|].
intros W3 c3 _ (-> & d3 & fy3 & regs3 & mem3 & md3 & -> & HB3 & _ & HK3 & HF3 & HM3 & HX3).
assert (REL3 : lnp_rel fy1 regs1 mem1 fy3 regs3 mem3) by (apply (lnp_rel_trans _ _ _ _ _ _ _ _ _ REL2); exact (conj HK3 (conj HF3 (conj HM3 HX3)))).
destruct d3; [apply SRr_ret; apply (lnp_fin fy regs mem true fy1 regs1 mem1 fy3 regs3 mem3 md3 HK1 HF1 HM1 HX1 R12 REL3 HB3); intros X; discriminate X|].
assert (G26c : getr regs3 26 = w64 (idx + 1)) by (rewrite (HK3 (26%bv : bv 5) ltac:(cbv; tauto)); exact G26b).
assert (G25c : getr regs3 25 = w64 (bidx + 2)) by (rewrite (HK3 (25%bv : bv 5) ltac:(cbv; tauto)); exact G25b).
assert (G24c : getr regs3 24 = w64 cur) by (rewrite (HK3 (24%bv : bv 5) ltac:(cbv; tauto)); exact G24b).
assert (Vp3 : val_mem trbsegs (mrestrict (w_H W) mem3) (s1v + 184) 8 pbef) by (apply (lnp_slot_kept mem2 mem3 _ _ HM3); [clear - Qs0 Qs1; lia | clear - Qs0 Qs1; lia | exact Vp2]).
assert (Vpi3 : val_mem trbsegs (mrestrict (w_H W) mem3) (s1v + 312) 8 pimg) by (apply (lnp_slot_kept mem2 mem3 _ _ HM3); [clear - Qs0 Qs1; lia | clear - Qs0 Qs1; lia | exact Vpi2]).
assert (Vn3 : val_mem trbsegs (mrestrict (w_H W) mem3) (s1v + 408) 8 (2 ^ 64 - 1 - pbef)) by (apply (lnp_slot_kept mem2 mem3 _ _ HM3); [clear - Qs0 Qs1; lia | clear - Qs0 Qs1; lia | exact Vn2]).
eapply SRr_bind; [exact (LNP_C1 idx bidx pbef bb bn cur pimg pg pn Hidx Hlc Hbi HinB HB0 HB1' HBF HinG HG0 Hcur0 Hcur1 fy3 regs3 mem3 md3 HB3 G26c G25c G24c Vp3 Vn3 Vpi3)|].
intros W4 c4 _ (-> & d4 & fy4 & regs4 & mem4 & md4 & -> & HB4 & _ & HK4 & HF4 & HM4 & HX4).
assert (REL4 : lnp_rel fy1 regs1 mem1 fy4 regs4 mem4) by (apply (lnp_rel_trans _ _ _ _ _ _ _ _ _ REL3); exact (conj HK4 (conj HF4 (conj HM4 HX4)))).
destruct d4; [apply SRr_ret; apply (lnp_fin fy regs mem true fy1 regs1 mem1 fy4 regs4 mem4 md4 HK1 HF1 HM1 HX1 R12 REL4 HB4); intros X; discriminate X|].
assert (G26d : getr regs4 26 = w64 (idx + 1)) by (rewrite (HK4 (26%bv : bv 5) ltac:(cbv; tauto)); exact G26c).
assert (G25d : getr regs4 25 = w64 (bidx + 2)) by (rewrite (HK4 (25%bv : bv 5) ltac:(cbv; tauto)); exact G25c).
assert (G24d : getr regs4 24 = w64 cur) by (rewrite (HK4 (24%bv : bv 5) ltac:(cbv; tauto)); exact G24c).
assert (Vp4 : val_mem trbsegs (mrestrict (w_H W) mem4) (s1v + 184) 8 pbef) by (apply (lnp_slot_kept mem3 mem4 _ _ HM4); [clear - Qs0 Qs1; lia | clear - Qs0 Qs1; lia | exact Vp3]).
assert (Vpi4 : val_mem trbsegs (mrestrict (w_H W) mem4) (s1v + 312) 8 pimg) by (apply (lnp_slot_kept mem3 mem4 _ _ HM4); [clear - Qs0 Qs1; lia | clear - Qs0 Qs1; lia | exact Vpi3]).
assert (Vn4 : val_mem trbsegs (mrestrict (w_H W) mem4) (s1v + 408) 8 (2 ^ 64 - 1 - pbef)) by (apply (lnp_slot_kept mem3 mem4 _ _ HM4); [clear - Qs0 Qs1; lia | clear - Qs0 Qs1; lia | exact Vn3]).
eapply SRr_bind; [exact (LNP_C2 idx bidx pbef bb bn cur pimg pg pn Hidx Hlc Hbi HinB HB0 HB1' HBF HinG HG0 Hcur0 Hcur1 fy4 regs4 mem4 md4 HB4 G26d G25d G24d Vp4 Vn4 Vpi4)|].
intros W5 c5 _ (-> & d5 & fy5 & regs5 & mem5 & md5 & -> & HB5 & H10 & HK5 & HF5 & HM5 & HX5).
assert (REL5 : lnp_rel fy1 regs1 mem1 fy5 regs5 mem5) by (apply (lnp_rel_trans _ _ _ _ _ _ _ _ _ REL4); exact (conj HK5 (conj HF5 (conj HM5 HX5)))).
apply SRr_ret. exact (lnp_fin fy regs mem d5 fy1 regs1 mem1 fy5 regs5 mem5 md5 HK1 HF1 HM1 HX1 R12 REL5 HB5 H10).
-
apply Z.eqb_neq in Eha. pose proof (HlenA Eha) as Hla.
eapply SRr_bind; [exact (LNP_A idx cur pimg pg pn Hidx Hla HinG HG0 Hcur0 Hcur1 fy1 regs1 mem1 md1 HB1 G26a G24a Vpi1)|].
intros W2 c2 _ (-> & d & fy2 & regs2 & mem2 & md2 & -> & HB2 & H10 & HK2 & HF2 & HM2 & HX2).
assert (REL2 : lnp_rel fy1 regs1 mem1 fy2 regs2 mem2) by (exact (conj HK2 (conj HF2 (conj HM2 HX2)))).
apply SRr_ret. exact (lnp_fin fy regs mem d fy1 regs1 mem1 fy2 regs2 mem2 md2 HK1 HF1 HM1 HX1 R12 REL2 HB2 H10).
Qed.
End g.
End b.
Lemma rga_lnd_cmp {rc : YN05.RunCeil} : forall (B : asyms), AR_laws trbsegs B ->
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF s1v ha idx bidx pbef bb bn cur pimg pg pn (fy : FPState) (regs : bvmap 5 word) memc mdc,
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
frm_zero (@fp_csr fy) ->
In (flt, nF) (ablocks B lyc Sc) -> sp0 - STK <= s1v -> s1v + 416 <= sp0 ->
0 <= ha < 2 ^ 64 -> 0 <= idx < 2 ^ 29 -> 0 <= pbef < 2 ^ 64 ->
(ha <> 0 -> 4 * (idx + 3) + 4 <= nF) ->
(ha = 0 -> pbef <> 0 -> 4 * (idx + 2) + 4 <= nF) ->
(ha = 0 -> pbef <> 0 ->
0 <= bidx < 2 ^ 29 /\ In (bb, bn) (ablocks B lyc Sc) /\ bb <= pbef /\ pbef + bidx + 3 <= bb + bn /\ (bb, bn) <> (flt, nF)) ->
In (pg, pn) (ablocks B lyc Sc) -> pg <= pimg -> pimg <= cur -> cur < pg + pn ->
val_mem trbsegs (mrestrict (w_H W) memc) (s1v + 168) 8 ha -> val_mem trbsegs (mrestrict (w_H W) memc) (s1v + 184) 8 pbef ->
val_mem trbsegs (mrestrict (w_H W) memc) (s1v + 312) 8 pimg -> val_mem trbsegs (mrestrict (w_H W) memc) (s1v + 408) 8 (2 ^ 64 - 1 - pbef) ->
getr regs 26 = w64 (idx + 1) -> getr regs 25 = w64 (bidx + 2) -> getr regs 24 = w64 cur ->
getr regs 23 = w64 flt -> getr regs 18 = w64 (2 ^ 64 - 1 - flt) -> getr regs 27 = w64 SB -> getr regs 9 = w64 s1v ->
SRr trbsegs W (mkCfg (@mkst fy regs (Z_to_bv 64 LNP_HEAD) memc (seg_rom trbsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists (d : bool) (fy' : FPState) regs2 mem2 md2,
c2 = mkCfg (@mkst fy' regs2 (Z_to_bv 64 (if d then LNP_CALL else LNP_STORE)) mem2 (seg_rom trbsegs)) md2 /\
frm_zero (@fp_csr fy') /\
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
(forall r : bv 5, reg_in r LNP_CLOB = false -> getr regs2 r = getr regs r) /\
(forall r : bv 5, In r LNP_FKEEP -> reg_get (@fp_regs fy') r = reg_get (@fp_regs fy) r) /\
getr regs2 12 = w64 idx /\ (d = false -> getr regs2 10 = w64 (2 ^ 64 - 1)) /\
(forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) mem2 a = aview trbsegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a)).
Proof.
intros B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF s1v ha idx bidx pbef bb bn cur pimg pg pn fy regs memc mdc
HJ Hfrm HinF Hs1lo Hs1hi Hha Hidx Hpbef HlenA HlenC HBef HinG HG0 Hcur0 Hcur1 Vh Vp Vpi Vn G26 G25 G24 G23 G18 G27 G9.
assert (HB : lnp_base B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt s1v fy regs memc mdc) by (repeat (split; [assumption|]); assumption).
eapply SRr_mono; [exact (LNP_block B LAWS STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W flt nF s1v HinF Hs1lo Hs1hi ha idx bidx pbef bb bn cur pimg pg pn
Hha Hidx Hpbef HlenA HlenC HBef HinG HG0 Hcur0 Hcur1 fy regs memc mdc HB G26 G25 G24 Vh Vp Vpi Vn)|].
intros W2 c2 _ (HW & d & fy' & regs2 & mem2 & md2 & Hc2 & (HJ2 & Hfrm2 & _) & (R12 & H10) & HK & HF & HM & HX).
split; [exact HW|]. exists d, fy', regs2, mem2, md2. split; [exact Hc2|]. split; [exact Hfrm2|]. split; [exact HJ2|].
split.
{ intros r Hr. destruct (lnp_clob_cases r Hr) as [-> | Hin]; [|exact (HK r Hin)]. rewrite !getr_zero. reflexivity. }
split; [exact HF|]. split; [exact R12|]. split; [exact H10|]. split; [exact HM | exact HX].
Qed.
