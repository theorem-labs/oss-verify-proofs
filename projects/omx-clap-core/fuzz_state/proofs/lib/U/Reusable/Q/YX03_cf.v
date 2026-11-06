From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK15 YK0n YP0n YM06 YK0s YM02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0a YO0b YO0c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YH00 YH03 YH02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0g YO0w YO0s YO0u YO15 YO10 YO0t YO0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YN03 YN02_cf YN2b.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YN0b_cf YN07_cf YN0a_cf YN1q_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable.Q Require Import YW0e_cf YX00_cf YX01_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import AllocRealloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM06_cf YO0d_cf YN2b_cf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac reg_numX := match goal with FP : free_pre _ _ _ _ |- _ =>
unfold extent_disjoint; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_hdr reg_grp reg_meta reg_area reg_ctx reg_nl reg_stk reg_tq reg_end1 reg_end5 reg_pn
reg_hdr0 reg_meta0 reg_stkR];
rewrite ?(base_val_EV (xvf _) (xvf_range _ _ _ _ FP)); cbn [base_val];
unfold aP, aSP, aTP, aG, aMEM, aOFF, aH3, aIDX, aRSV, aBITS, aAV, aFR, aAREA, aSC, aTQ, aSCL, aLAST, aML, aMP, aEND, aPN, aEP, aSEC;
cbn [xvf Nat.ltb Nat.leb nat_to_reg] end.
Ltac denS1 XR := unfold STR16; cbn [sv_denot]; unfold ES; rewrite ?(ew_EV _ XR).
Ltac denS2 := unfold aP, aSP, aTP, aG, aMEM, aOFF, aH3, aIDX, aRSV, aBITS, aAV, aFR, aAREA, aSC, aTQ, aSCL, aLAST, aML, aMP, aEND, aPN, aEP, aSEC;
unfold xvS; cbn [xvf Nat.ltb Nat.leb nat_to_reg]; rewrite ?Z.add_0_r.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition headS : smem := [reg_hdr0; reg_grp; reg_meta0; reg_area; reg_ctx; reg_nl; reg_stkR].
Lemma rokS_ro E0 m0 r0 : region_ok src0segs E0 m0 r0 -> region_ok src0segs E0 m0 (YP09.mkRegion (r_base r0) (r_lo r0) (r_hi r0) 0 0 (r_chunks r0)).
Proof. intros (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split; [cbn [r_wlo r_whi]; intros o Ho; lia | exact H4]. Qed.
Section g.
Variables (k : kcase) (r : rcase) (v : fvals) (m : word -> option byte).
Hypothesis FP : free_pre k r v m.
Hypothesis HSP : CEIL + 8256 <= fv_sp v.
Hypothesis HSW : forall x, fv_sp v - 8256 <= x < fv_sp v -> writable_at src0segs m x.
Lemma rokS_stk : region_ok src0segs (EV (xvf v)) m reg_stkR.
Proof using FP HSP HSW.
apply region_ok_intro; reg_numX; [lin | lin | intros o Ho; apply HSW; lin | apply Forall_nil].
Qed.
Lemma rokS_all : Forall (region_ok src0segs (EV (xvf v)) m) (entry_memS k r).
Proof using FP HSP HSW.
pose proof rokS_stk as ST.
pose proof (rok_end1 _ _ _ _ FP) as E1. pose proof (rok_end5 _ _ _ _ FP) as E5. pose proof (rok_pn _ _ _ _ FP) as PN. pose proof (rok_tq _ _ _ _ FP) as TQ.
pose proof (rokS_ro _ _ _ (rok_hdr _ _ _ _ FP)) as H0. pose proof (rokS_ro _ _ _ (rok_meta _ _ _ _ FP)) as M0.
pose proof (rok_grp _ _ _ _ FP) as G0. pose proof (rok_area _ _ _ _ FP) as A0. pose proof (rok_ctx _ _ _ _ FP) as C0. pose proof (rok_nl _ _ _ _ FP) as N0.
unfold entry_memS. destruct k, r; cbn [k_mem r_mem app] in *; repeat (apply Forall_cons || apply Forall_nil);
first [exact H0 | exact M0 | exact G0 | exact A0 | exact C0 | exact N0 | exact ST | exact E1 | exact E5 | exact PN | apply TQ; discriminate].
Qed.
Lemma pdS_head : pairwise_disjoint (EV (xvf v)) headS.
Proof using FP HSP.
unfold headS. cbn [pairwise_disjoint all_disjoint].
repeat match goal with |- _ /\ _ => split | |- True => exact I end; reg_numX; lin.
Qed.
Lemma pdS_tail : pairwise_disjoint (EV (xvf v)) (k_mem k ++ r_mem r).
Proof using FP.
pose proof (fp_pn6 _ _ _ _ FP) as P6. pose proof (fp_c_end5 _ _ _ _ FP) as E5.
destruct k, r; cbn [k_mem r_mem app pairwise_disjoint all_disjoint] in *;
repeat match goal with |- _ /\ _ => split | |- True => exact I end; try (destruct E5 as (_ & _ & E5)); reg_numX; lin.
Qed.
Lemma crS_tq : Forall (fun x => extent_disjoint (EV (xvf v)) x reg_tq) headS.
Proof using FP HSP. unfold headS. repeat (apply Forall_cons || apply Forall_nil); reg_numX; lin. Qed.
Lemma crS_end1 : Forall (fun x => extent_disjoint (EV (xvf v)) x reg_end1) headS.
Proof using FP HSP. unfold headS. repeat (apply Forall_cons || apply Forall_nil); reg_numX; lin. Qed.
Lemma crS_end5 : match r with R5 | R6 => Forall (fun x => extent_disjoint (EV (xvf v)) x reg_end5) headS | _ => True end.
Proof using FP HSP.
pose proof (fp_c_end5 _ _ _ _ FP) as E5. destruct r; try exact I; destruct E5 as (_ & _ & E5);
unfold headS; repeat (apply Forall_cons || apply Forall_nil); reg_numX; lin.
Qed.
Lemma crS_pn : match r with R14 | R6 => Forall (fun x => extent_disjoint (EV (xvf v)) x reg_pn) headS | _ => True end.
Proof using FP HSP.
destruct r; try exact I; unfold headS; repeat (apply Forall_cons || apply Forall_nil); reg_numX; lin.
Qed.
Lemma crS_all : forall y, In y (k_mem k ++ r_mem r) -> Forall (fun x => extent_disjoint (EV (xvf v)) x y) headS.
Proof using FP HSP.
pose proof crS_tq as CT. pose proof crS_end1 as C1. pose proof crS_end5 as C5. pose proof crS_pn as CP.
intros y Hy. destruct k, r; cbn [k_mem r_mem app] in Hy, C5, CP;
repeat (destruct Hy as [<-|Hy]; [assumption|]); destruct Hy.
Qed.
Lemma memS_ok : mem_ok src0segs (EV (xvf v)) m (entry_memS k r).
Proof using FP HSP HSW.
split; [destruct k, r; vm_compute; reflexivity|]. split; [exact rokS_all|].
unfold entry_memS. apply pairwise_disjoint_app; [exact pdS_head | exact pdS_tail | exact crS_all].
Qed.
End g.
Section b.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (g : sptr) (am : ameta) (idx : Z) (fr : frame) (n : Z) (a : sptr) (ka : Z) (rg : YO0i.region).
Hypothesis HC : small_ctx L A regs mem md g am idx fr n a ka rg.
Local Abbreviation V := (vS L regs g am idx fr a rg).
Local Abbreviation XV := (xvS L regs g am idx fr a rg n).
Local Abbreviation E := (ES L regs g am idx fr a rg n).
Lemma XR3 : forall k, 0 <= XV k < 2 ^ 64.
Proof using HC. exact (XS _ _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma ewS k : bv_unsigned (ew E k) = XV k.
Proof using HC. unfold ES. apply (ew_EV _ XR3). Qed.
Lemma SPS : CEIL_MIN + 8256 <= spZ regs < 2 ^ 63 /\ spZ regs mod 16 = 0 /\ CEIL + 8256 <= fv_sp V /\
(forall x, fv_sp V - 8256 <= x < fv_sp V -> writable_at src0segs mem x).
Proof using HC.
pose proof (sx_pre _ _ _ _ _ _ _ _ _ _ _ _ _ HC) as (_ & _ & _ & _ & Hal & Hceil & Hsp63 & Hstk & _).
pose proof (proj1 alloc_ceiling_val) as ACV. change (fv_sp V) with (spZ regs). unfold CEIL. unfold REALLOC_STACK, ALLOC_STACK in *.
split; [lia|]. split; [exact Hal|]. split; [lia|]. intros x Hx. apply Hstk. lia.
Qed.
Lemma ENDS : fv_end V = fv_mem V + 12 + stride_of am * (fv_idx V + 1).
Proof using.
change (fv_end V) with (ptr_addr L (slot_end am idx)). change (fv_mem V) with (ptr_addr L (am_mem am)). change (fv_idx V) with idx.
unfold slot_end, slot_start. rewrite !ptr_addr_padd'. unfold UNIT, IB. lia.
Qed.
Lemma EK12 k r : free_pre k r V mem -> k = K1 \/ k = K2 -> fv_end V = fv_mem V + 12 + 16 * fv_scl V * (fv_idx V + 1).
Proof using.
intros FP [-> | ->]; pose proof (fp_k _ _ _ _ FP) as K; [destruct K as (_ & _ & _ & _ & EK) | destruct K as (_ & _ & _ & _ & _ & _ & EK)]; exact EK.
Qed.
Lemma K3S k r : free_pre k r V mem -> k = K3a \/ k = K3b -> 1 <= fv_ml V /\ fv_idx V = 0 /\ fv_end V = fv_mem V + 4096 * fv_ml V - 4.
Proof using.
intros FP [-> | ->]; pose proof (fp_k _ _ _ _ FP) as K;
[destruct K as (M1 & _ & _ & _ & _ & I0 & _ & EK) | destruct K as (M1 & _ & _ & I0 & _ & EK)]; auto.
Qed.
Lemma ST12 k r : free_pre k r V mem -> k = K1 \/ k = K2 -> stride_of am = 16 * fv_scl V.
Proof using.
intros FP Hk. pose proof (EK12 _ _ FP Hk) as EK. pose proof ENDS as EE. pose proof (lin_facts _ _ _ _ FP) as LF; cbn zeta in LF.
apply (Z.mul_reg_r _ _ (fv_idx V + 1)); lia.
Qed.
Lemma atomsS_kR k r : free_pre k r V mem -> atoms_ok E (k_atomsR k).
Proof using HC.
intros FP. pose proof (lin_facts _ _ _ _ FP) as LF; cbn zeta in LF. pose proof (proj1 alloc_ceiling_val) as ACV. unfold CEIL in LF.
assert (B1 : 0 <= fv_scl V <= 8191) by lia. assert (B2 : 0 <= fv_idx V <= 31) by lia.
assert (SI : 0 <= fv_scl V * fv_idx V <= 8191 * 31) by (clear -B1 B2; nia).
destruct k; cbn [k_atomsR atoms_ok]; try exact I;
(assert (ST : stride_of am = 16 * fv_scl V) by (apply (ST12 _ _ FP); first [left; reflexivity | right; reflexivity]));
(split; [|exact I]); unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite ewS;
change (XV aST) with (fv_mem V + stride_of am * fv_idx V); rewrite ST; change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia.
Qed.
Lemma al12_1 k r : free_pre k r V mem -> k = K1 \/ k = K2 ->
sv_denot E (SAlu ALU_ADD (SOff aMEM 0) (SMd M_MUL STR16 (SOff aIDX 0))) = sv_denot E (SOff aST 0).
Proof using HC.
intros FP Hk. pose proof XR3 as XR. pose proof (ST12 _ _ FP Hk) as ST. pose proof (lin_facts _ _ _ _ FP) as LF; cbn zeta in LF.
pose proof (proj1 alloc_ceiling_val) as ACV. unfold CEIL in LF.
assert (B1 : 0 <= fv_scl V <= 8191) by lia. assert (B2 : 0 <= fv_idx V <= 31) by lia.
assert (SI : 0 <= fv_scl V * fv_idx V <= 8191 * 31) by (clear -B1 B2; nia).
assert (XST : XV aST = fv_mem V + stride_of am * fv_idx V) by reflexivity.
weq. denS1 XR. rewrite XST. denS2. rewrite ST.
rewrite alu64_add, mul64_unsigned, alu64_sll, !lit64_small by lia. change (4 mod 64) with 4.
unfold sll64, mul64, add64. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
rewrite (Z.mod_small (fv_scl V * 16)) by lia. rewrite (Z.mod_small (fv_scl V * 16 * fv_idx V)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma al12_2 k r : free_pre k r V mem -> k = K1 \/ k = K2 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD STR16 (SLit 16)) (SOff aST 0)) = sv_denot E (SOff aEND 4).
Proof using HC.
intros FP Hk. pose proof XR3 as XR. pose proof (ST12 _ _ FP Hk) as ST. pose proof (EK12 _ _ FP Hk) as EK.
pose proof (lin_facts _ _ _ _ FP) as LF; cbn zeta in LF.
pose proof (proj1 alloc_ceiling_val) as ACV. unfold CEIL in LF.
assert (B1 : 0 <= fv_scl V <= 8191) by lia. assert (B2 : 0 <= fv_idx V <= 31) by lia.
assert (SI : 0 <= fv_scl V * fv_idx V <= 8191 * 31) by (clear -B1 B2; nia).
assert (XST : XV aST = fv_mem V + stride_of am * fv_idx V) by reflexivity.
weq. denS1 XR. rewrite XST. denS2. rewrite ST.
rewrite !alu64_add, alu64_sll, !lit64_small by lia. change (4 mod 64) with 4. unfold sll64, add64.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
rewrite (Z.mod_small (fv_scl V * 16)) by lia. rewrite (Z.mod_small (fv_scl V * 16 + 16)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma al3_1 k r : free_pre k r V mem -> k = K3a \/ k = K3b ->
sv_denot E (SAlu ALU_ADD (SOff aMEM 0) (SMd M_MUL (SOff aMP (-16)) (SOff aIDX 0))) = sv_denot E (SOff aMEM 0).
Proof using HC.
intros FP Hk. pose proof XR3 as XR. pose proof (K3S _ _ FP Hk) as (M1 & I0 & EK). pose proof (lin_facts _ _ _ _ FP) as LF; cbn zeta in LF.
pose proof (proj1 alloc_ceiling_val) as ACV. unfold CEIL in LF.
weq. denS1 XR. denS2. rewrite alu64_add, mul64_unsigned, !lit64_small by lia. rewrite I0.
unfold mul64, add64. rewrite Z.mul_0_r, Z.mod_0_l, Z.add_0_r by lia. apply Z.mod_small. lia.
Qed.
Lemma al3_2 k r : free_pre k r V mem -> k = K3a \/ k = K3b ->
sv_denot E (SAlu ALU_ADD (SOff aMEM 0) (SOff aMP 0)) = sv_denot E (SOff aEND 4).
Proof using HC.
intros FP Hk. pose proof XR3 as XR. pose proof (K3S _ _ FP Hk) as (M1 & I0 & EK). pose proof (lin_facts _ _ _ _ FP) as LF; cbn zeta in LF.
pose proof (proj1 alloc_ceiling_val) as ACV. unfold CEIL in LF.
weq. denS1 XR. denS2. rewrite alu64_add, !lit64_small by lia. unfold add64. rewrite Z.mod_small by lia. lia.
Qed.
Lemma aliasS_kR k r : free_pre k r V mem -> alias_ok E (k_aliasR k).
Proof using HC.
intros FP. destruct k; unfold k_aliasR; cbn [alias_ok]; (split; [|split; [|exact I]]);
first [apply (al12_1 _ _ FP) | apply (al12_2 _ _ FP) | apply (al3_1 _ _ FP) | apply (al3_2 _ _ FP)];
first [left; reflexivity | right; reflexivity].
Qed.
Lemma entryS_gen k r nc : free_pre k r V mem -> nc_lo nc <= n <= nc_hi nc -> facts_ok E (nc_facts nc) ->
st_ok src0segs E (S0s k r nc) (mkst regs (Z_to_bv 64 src0_A_realloc) mem (seg_rom src0segs)).
Proof using HC.
intros FP Hn HN. pose proof SPS as (SP1 & SP2 & SP3 & SP4).
assert (EA : env_agree 96 (EV (xvf V)) E) by apply ES_agree.
assert (FAL : facts_atoms_lt 96 (free_facts k r) = true) by (destruct k, r; vm_compute; reflexivity).
assert (MAL : mem_atoms_lt 96 (entry_memS k r) = true) by (destruct k, r; vm_compute; reflexivity).
pose proof (facts_ok_agree 96 (EV (xvf V)) E (free_facts k r) EA FAL (st_ok_facts_ok _ _ _ _ (free_entry_st_ok _ _ _ _ FP))) as (FA & FC & FL).
unfold free_facts in FA, FC, FL. cbn [f_atoms f_conds f_alias] in FA, FC, FL.
unfold nc_facts in HN. destruct HN as (NA & NC & NL). cbn [f_atoms f_conds f_alias] in NA, NC, NL.
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_resv ss_regs ss_mem ss_facts S0s resv_denot].
repeat (split; [reflexivity|]). split; [|split].
- eapply (regs_ok_agree 96 (EV (xvf V)) E); [exact EA | reflexivity | exact (free_regs_ok V)].
- exact (mem_ok_agree src0segs 96 (EV (xvf V)) E mem _ EA MAL (memS_ok k r V mem FP SP3 SP4)).
- unfold entry_factsS. split; [|split]; cbn [f_atoms f_conds f_alias].
+ unfold entry_atomsS. cbn [atoms_ok]. split; [|split].
* unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite ewS, (XS_N _ _ _ _ _ _ _ _ _ _ _ _ _ HC). change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
* unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite ewS, XS_SP. change (2 ^ 4) with 16. split; [lia | split; [exact SP2 | lia]].
* apply atoms_ok_app; [exact NA|]. apply atoms_ok_app; [exact (atomsS_kR _ _ FP) | exact FA].
+ apply conds_ok_app; [exact NC | exact FC].
+ apply alias_ok_app; [exact NL|]. apply alias_ok_app; [exact (aliasS_kR _ _ FP) | exact FL].
Qed.
Theorem entry_st_okS nc : nc_lo nc <= n <= nc_hi nc -> facts_ok (ES L regs g am idx fr a rg n) (nc_facts nc) ->
st_ok src0segs (ES L regs g am idx fr a rg n) (S0s (kcase_of am) (rcase_of (reserved_of am fr)) nc)
(mkst regs (Z_to_bv 64 src0_A_realloc) mem (seg_rom src0segs)).
Proof using HC. exact (entryS_gen _ _ nc (FPS _ _ _ _ _ _ _ _ _ _ _ _ _ HC)). Qed.
End b.
End a.
