(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0c YP0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK00 YK0i YK14 YK1b YK15 YK0l YK18 YK0q YQ0k YK0s YN02
YQ0j YQ0b YQ03 YQ0i YQ0h YQ09 YQ0a YQ04 YQ0e YQ0c YO3p YO3v YI00 YL08 YL07 YL02 YL03
YK05 YA0i YA0l YA0m YA0n YA0k YK0a YA0e
YG00 YG01 YG0m YG0h YG10 YG0u YG0d YC04 YB0z YB06 YF8z YB0l
YB07 YF90 YD15 YD14 YD0f YD0l YD0g YD0j YD0r YD0p YE20   YC1a.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0p YCcx YCcd YD0x YD0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0n YG0o YG0p YG0r.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YD0m YD0q YD0o YD13 YD0h YD11 YD0w YD12 YD0e YD0y YD0z YD0u YD10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP07 YP01.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Lemma st_ok_fx : forall (fx1 fx2 : YK11.FPState) E ss (H : word -> bool) regs pc mem,
@st_ok trasegs fx1 E ss (restrict H (@mkst fx1 regs pc mem (seg_rom trasegs))) ->
@st_ok trasegs fx2 E ss (restrict H (@mkst fx2 regs pc mem (seg_rom trasegs))).
Proof.
intros fx1 fx2 E ss H regs pc mem HS. rewrite (@restrict_mkst_fx fx2). rewrite (@restrict_mkst_fx fx1) in HS.
destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
split; [reflexivity|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
split; [reflexivity|]. split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. exact H9.
Qed.
Section c.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis HB : TraSyms B.
Hypothesis ARL : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis LIB : forall fx : YK11.FPState, @lib_site_rgb fx rc B.
Hypothesis PF1 : forall fx : YK11.FPState, @printf_first_tfa fx rc B xst.
Hypothesis PFN : forall fx : YK11.FPState, @printf_next_tfa fx rc B xst.
Hypothesis FREE : forall fx : YK11.FPState, @free_site_tfa fx rc B.
Hypothesis FREEN : forall fx : YK11.FPState, @free_null_site_tfa fx rc B.
Hypothesis EXITL : forall fx : YK11.FPState, @exit_leaf_tfa fx rc B xst.
Hypothesis XFR : xst_frame_tfa xst.
Variables (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (a0 p : list byte).
Hypothesis Hargv : in_argv inp = [a0; p].
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv [a0; p].
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hvfs : valid_fs (in_fs inp).
Hypothesis RUNIV : forall data, fs_lookup (in_fs inp) p = Some data -> rrfc_universe B (payload_len data).
#[local] Notation EL := (YQ0a.E0 sp [a0; p] (in_envp inp) xw xd).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation envp := (in_envp inp).
#[local] Notation EL6 := (YD0c.EL6 sp inp xw xd a0 p Hsp Hva Hve).
#[local] Notation arodata_keep := (YD0c.arodata_keep B).
#[local] Notation arodata_frame := (YD0c.arodata_frame B).
#[local] Notation lib_reseat := (YD0c.lib_reseat B HB sp Hsp).
#[local] Notation rdword_vararg := (YD0c.rdword_vararg sp).
#[local] Notation vp_reseat := (YD0c.vp_reseat sp Hsp).
#[local] Notation blocks_bytes_ablocks := (YD0c.blocks_bytes_ablocks B).
#[local] Notation STDOUT_static := (YD0c.STDOUT_static B HB).
#[local] Notation in_ro_static := (YD0c.in_ro_static sp Hsp).
Theorem calls_loop : forall (r : nat) (fx : YK11.FPState) (j : nat) E (W : world trasegs) ms md ly S data (buf cap q : Z) (LK : list (Z * Z)),
fs_lookup (in_fs inp) p = Some data -> 6 + config_len data <= dlen data ->
(forall k, (k < K_M1)%nat -> ew E k = ew EL k) -> ed E 2 = data ->
bv_unsigned (ew E A_BUF) = buf ->
bv_unsigned (ew E 162) = payload_len data -> bv_unsigned (ew E 163) = (if payload_len data =? 0 then A_EMPTY_tfa else q) ->
bv_unsigned (ew E 164) = q -> bv_unsigned (ew E 166) = Z.of_nat r ->
st_ok trasegs E S_L (restrict (w_H W) ms) ->
(1 <= r)%nat -> (j + r <= 4)%nat ->
((payload_len data = 0 /\ q = 0 /\ Permutation (ablocks B ly S) (LK ++ [(buf, cap)]))
\/ (0 < payload_len data /\ Permutation (ablocks B ly S) (LK ++ [(buf, cap); (q, payload_len data)]))) ->
0 <= bsum LK -> bsum LK + 3 * 2 ^ 16 * Z.of_nat r <= 2 ^ 20 ->
frames S = [] -> qtightB S ->
AI trasegs (w_H W) (w_A W) md -> AR trasegs B ly S W (ms_mem ms) md -> top_ok usp ly ->
rbud S (Z.of_nat r) 3 -> 65536 <= cap <= 2 ^ 26 -> dlen data < cap -> (2 <= length data)%nat ->
so_state xst j (w_H W) (ms_mem ms) -> arodata_ok B (aview trasegs (w_H W) (ms_mem ms)) ->
m_fs md = in_fs inp -> m_fds md = APSG.fds_std -> frm_zero (@fp_csr fx) ->
srealizes trasegs (mkCfg ms md) (wr ch_stdout (concat (repeat line0 (r + (j - 1)))) (ex 0 (in_fs inp))).
Proof.
induction r as [|r IH]; [intros; lia|].
intros fx j E W ms md ly S data buf cap q LK Hlk Hok HEE HEd E41 E61 E62 E63 E65 HS _ Hjr HBL HLK0 HLK Hfr HQT HAI HAR HTOP Hnev Hcap HLc Hlen HSO HRO Hfs Hfds Hfrm.
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp. pose proof (proj1 (@YN05.alloc_ceiling_value rc)) as CV.
pose proof (top_ok_ceil _ _ HTOP) as HCT. pose proof (YN05.ceil_le_top _ HCT) as CLE. unfold stack_max_size in CLE.
pose proof (config_len_bound data) as Hcl.
assert (Hpl : 0 <= payload_len data < cap) by (unfold payload_len, HDR_MIN in *; lia).
assert (E0 : bv_unsigned (ew E 0) = usp) by (rewrite HEE by (unfold K_M1; lia); reflexivity).
assert (E6 : usp <= bv_unsigned (ew E 6)) by (rewrite HEE by (unfold K_M1; lia); exact EL6).
pose proof calls_pcs as (PCV & PCB & PCL2 & PCF & PCX & PCLR & PCVr & PCFr & RVV & RVL2 & RVF & RVX & RVB & RVL).
pose proof (st_ok_restrict_mkst trasegs (w_H W) E S_L ms HS RVL) as Hshape.
set (regs := ms_regs ms) in *. set (mem := ms_mem ms) in *.
pose proof S_L_regs as (Q1 & Q2 & Q3 & Q4 & Q8 & Q10 & Q11).
assert (R1 : getr regs 1%bv = w64 RA_LLVMF) by (subst regs; rewrite (st_ok_restrict_reg trasegs (w_H W) E S_L ms 1%bv HS), Q1; reflexivity).
assert (R2 : getr regs 2%bv = Z_to_bv 64 (usp + -208)) by (subst regs; rewrite (st_ok_restrict_reg trasegs (w_H W) E S_L ms 2%bv HS), Q2; cbn [sv_denot]; rewrite E0; reflexivity).
assert (R3 : getr regs 3%bv = w64 TRA_GP) by (subst regs; rewrite (st_ok_restrict_reg trasegs (w_H W) E S_L ms 3%bv HS), Q3; reflexivity).
assert (R4 : getr regs 4%bv = w64 TRA_TP) by (subst regs; rewrite (st_ok_restrict_reg trasegs (w_H W) E S_L ms 4%bv HS), Q4; reflexivity).
assert (R8 : getr regs 8%bv = w64 (payload_len data)).
{ subst regs. rewrite (st_ok_restrict_reg trasegs (w_H W) E S_L ms 8%bv HS), Q8. cbn [sv_denot]. rewrite Z.add_0_r, <- E61. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (R10 : getr regs 10%bv = w64 (if payload_len data =? 0 then A_EMPTY_tfa else q)).
{ subst regs. rewrite (st_ok_restrict_reg trasegs (w_H W) E S_L ms 10%bv HS), Q10. cbn [sv_denot]. rewrite Z.add_0_r, <- E62. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (R11 : getr regs 11%bv = w64 (payload_len data)).
{ subst regs. rewrite (st_ok_restrict_reg trasegs (w_H W) E S_L ms 11%bv HS), Q11. cbn [sv_denot]. rewrite Z.add_0_r, <- E61. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (Hsp' : spZ regs = usp - 208) by (unfold spZ; rewrite R2; rewrite u64_lit by (unfold sp_window_lo in Ulo; lia); lia).
assert (Hra : raZ regs = RA_LLVMF) by (unfold raZ; rewrite R1; apply u64_lit; unfold RA_LLVMF; lia).
assert (Hs0 : s0Z regs = payload_len data) by (unfold s0Z; rewrite R8; apply u64_lit; lia).
pose proof (st_ok_mem_ok trasegs E S_L _ HS) as HM. cbn [restrict ms_mem] in HM. fold mem in HM.
assert (Hwin : forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a).
{ intros a Ha. destruct (Z.lt_ge_cases a (usp - 208)); [| destruct (Z.lt_ge_cases a (usp - 128))].
- eapply (win_present sp Hsp E (w_H W) mem L_mem); [exact HM | left; reflexivity | exact E0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E (w_H W) mem L_mem); [exact HM | right; left; reflexivity | exact E0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E (w_H W) mem L_mem); [exact HM | right; right; left; reflexivity | exact E0 | lia | lia | cbn; lia]. }
assert (Hbb : blocks_bytes S <= cap + payload_len data + bsum LK).
{ rewrite (blocks_bytes_ablocks ly S). destruct HBL as [(_ & _ & HP) | (_ & HP)]; rewrite (bsum_perm _ _ HP), bsum_app; cbn; lia. }
rewrite Hshape, PCL2 || rewrite Hshape. fold regs mem.
replace (Z_to_bv 64 (ss_pc S_L)) with (w64 A_LLVMF) by reflexivity.
change (mkCfg (mkst regs (w64 A_LLVMF) mem (seg_rom trasegs)) md) with (cfg_at trasegs A_LLVMF regs mem md).
assert (PRE : lib_pre B ly S W regs mem md).
{ split; [exact HAR|]. split; [rewrite R1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity|]. split; [exact Hra|].
split; [rewrite (ts_gp B HB); exact R3|]. split; [rewrite (ts_tp B HB); exact R4|].
split; [rewrite Hsp'; replace (usp - 208) with (usp + (-13) * 16) by lia; rewrite Z.mod_add by lia; exact U16|].
split; [rewrite Hsp'; lia|]. split; [rewrite Hsp'; unfold top_ok in HTOP; lia|].
split; [exact (proj1 (proj2 HTOP))|]. split; [exact (proj1 (proj2 (proj2 HTOP)))|].
split; [rewrite Hsp'; intros a Ha; apply Hwin; unfold LLVMF_STK in Ha; lia|].
split; [| exact HQT]. rewrite Hs0. lia. }
eapply (SRr_srealizes trasegs W (cfg_at trasegs A_LLVMF regs mem md)); [| exact HAI |].
{ apply (LIB fx ly S W regs mem md (if payload_len data =? 0 then A_EMPTY_tfa else q) (payload_len data) PRE R10 R11).
- destruct HBL as [(Hz & Hq & HP) | (Hp & HP)].
+ left. rewrite Hz. split; reflexivity.
+ right. replace (payload_len data =? 0) with false by (symmetry; apply Z.eqb_neq; lia). split; [lia|].
apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. right. left. reflexivity.
- exact Hfr.
- apply (rbud_lib_pre _ _ _ Hnev); lia.
- unfold LIVE_LIB, LIVE_MAX. clear - Hbb HLK HLK0 Hcap Hpl. lia.
- exact HRO.
- exact Hfrm.
- exact (RUNIV data Hlk). }
cbv beta. intros W' c' _ HAI' (fx' & ly' & S' & regs' & mem' & md' & k & -> & Hfrm' & HJ & Hk & HP & Ha0' & HPERM0 & HBUD). cbn [cfg_model] in HAI'.
assert (exists leak : list (Z * Z), Permutation (ablocks B ly' S') (leak ++ ablocks B ly S) /\ (leak = [] \/ exists a m, leak = [(a, m)] /\ 0 <= m < 3 * 2 ^ 16))
as (leak & HPERM & Hleak) by (exists []; split; [exact HPERM0 | left; reflexivity]).
set (LK' := leak ++ LK).
assert (HLK'0 : 0 <= bsum LK') by (subst LK'; rewrite bsum_app; destruct Hleak as [-> | (la & lm & -> & Hlm)]; cbn; lia).
assert (HLK' : bsum LK' + 3 * 2 ^ 16 * Z.of_nat r <= 2 ^ 20) by (subst LK'; rewrite bsum_app; destruct Hleak as [-> | (la & lm & -> & Hlm)]; cbn; lia).
unfold cfg_at.
pose proof HJ as (HAR' & Hlyle & Hsecs & Hwle & Hio & Hfrs & Hnev' & Hk0 & F1 & F2 & F3 & F4 & Hgone & HpresJ & Hstk & HQT').
assert (Hnev1 : rbud S' (Z.of_nat r) 3) by (apply (rbud_lib_post S S'); [replace (Z.of_nat r + 1) with (Z.of_nat (Datatypes.S r)) by lia; exact Hnev | exact HBUD]).
rewrite Hfr in Hfrs. cbn [app] in Hfrs.
destruct (same_io_fs_fds _ _ Hio) as [Efs Efds].
assert (HTOP' : top_ok usp ly') by exact (top_ok_le _ _ _ _ Hlyle HTOP).
assert (HBL' : (payload_len data = 0 /\ q = 0 /\ Permutation (ablocks B ly' S') (LK' ++ [(buf, cap)]))
\/ (0 < payload_len data /\ Permutation (ablocks B ly' S') (LK' ++ [(buf, cap); (q, payload_len data)]))).
{ subst LK'. destruct HBL as [(Hz & Hq & HPm) | (Hp & HPm)]; [left | right]; repeat split; try assumption;
rewrite <- app_assoc; exact (Permutation_trans HPERM (Permutation_app_head leak HPm)). }
assert (HSO' : so_state xst j (w_H W') mem').
{ apply (so_state_keep xst XFR j (w_H W) (w_H W') mem mem'); [| exact HSO]. intros a Ha. destruct (STDOUT_static a Ha) as (H1 & H2 & H3). exact (F3 a H1 H2 H3). }
assert (HRO' : arodata_ok B (aview trasegs (w_H W') mem')).
{ apply (arodata_keep (w_H W) (w_H W') mem mem'); [| exact HRO]. intros a H1 H2 H3. apply F3; [| exact H2 | exact H3]. apply in_img_hull. pose proof (in_ro_range a H1). lia. }
rewrite Hshape, restrict_mkst_fx in HS. fold regs mem in HS.
pose proof (lib_reseat E W W' regs mem regs' mem' ly S md ly' S' md' k HS E0 E6 ltac:(rewrite <- Hsp'; exact HJ) HAR HP Ha0' HCT) as HS2.
set (E2 := havoc E K_LR (map (getr regs') CLOB')) in HS2.
assert (E2old : forall i, (i < K_LR)%nat -> ew E2 i = ew E i) by (intros i Hi; subst E2; apply ew_havoc_old; exact Hi).
assert (E2_0 : bv_unsigned (ew E2 0) = usp) by (rewrite E2old by (unfold K_LR, A_BUF, A_LEN, K_PP; lia); exact E0).
assert (E2_6 : usp <= bv_unsigned (ew E2 6)) by (rewrite E2old by (unfold K_LR, A_BUF, A_LEN, K_PP; lia); exact E6).
rewrite <- restrict_mkst_fx in HS2.
apply (st_ok_fx fx fx') in HS2.
apply (SRr_srealizes trasegs W' _ _ _ (vp_run E2 W' regs' mem' md' HS2) HAI').
intros W1 c1 _ HAI3 (-> & msV & matV & -> & HSV & HFV & HFrV). cbn [cfg_model] in HAI3.
set (mdV := with_vm_backing (m_vm_lazy md') matV md') in *.
pose proof (st_ok_restrict_mkst trasegs (w_H W') E2 S_VP msV HSV RVV) as HshapeV.
set (regsV := ms_regs msV) in *. set (memV := ms_mem msV) in *.
pose proof S_VP_regs as (V1 & V2 & V3 & V4 & V10 & V11).
assert (RV1 : getr regsV 1%bv = w64 RA_EMIT) by (subst regsV; rewrite (st_ok_restrict_reg trasegs (w_H W') E2 S_VP msV 1%bv HSV), V1; reflexivity).
assert (RV2 : getr regsV 2%bv = Z_to_bv 64 (usp + -288)) by (subst regsV; rewrite (st_ok_restrict_reg trasegs (w_H W') E2 S_VP msV 2%bv HSV), V2; cbn [sv_denot]; rewrite E2_0; reflexivity).
assert (RV3 : getr regsV 3%bv = w64 TRA_GP) by (subst regsV; rewrite (st_ok_restrict_reg trasegs (w_H W') E2 S_VP msV 3%bv HSV), V3; reflexivity).
assert (RV4 : getr regsV 4%bv = w64 TRA_TP) by (subst regsV; rewrite (st_ok_restrict_reg trasegs (w_H W') E2 S_VP msV 4%bv HSV), V4; reflexivity).
assert (RV10 : getr regsV 10%bv = w64 A_FMT_D) by (subst regsV; rewrite (st_ok_restrict_reg trasegs (w_H W') E2 S_VP msV 10%bv HSV), V10; reflexivity).
assert (RV11 : getr regsV 11%bv = Z_to_bv 64 (usp + -264)) by (subst regsV; rewrite (st_ok_restrict_reg trasegs (w_H W') E2 S_VP msV 11%bv HSV), V11; cbn [sv_denot]; rewrite E2_0; reflexivity).
assert (HspV : spZ regsV = usp - 288) by (unfold spZ; rewrite RV2; rewrite u64_lit by (unfold sp_window_lo in Ulo; lia); lia).
assert (HraV : raZ regsV = RA_EMIT) by (unfold raZ; rewrite RV1; apply u64_lit; unfold RA_EMIT; lia).
pose proof (st_ok_mem_ok trasegs E2 S_VP _ HSV) as HMV. cbn [restrict ms_mem] in HMV. fold memV in HMV.
assert (HwinV : forall a, usp - 65536 <= a < usp -> apresent (w_H W') memV a).
{ intros a Ha. destruct (Z.lt_ge_cases a (usp - 208)); [| destruct (Z.lt_ge_cases a (usp - 128))].
- eapply (win_present sp Hsp E2 (w_H W') memV (ss_mem S_VP)); [exact HMV | left; reflexivity | exact E2_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E2 (w_H W') memV (ss_mem S_VP)); [exact HMV | right; left; reflexivity | exact E2_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E2 (w_H W') memV (ss_mem S_VP)); [exact HMV | right; right; left; reflexivity | exact E2_0 | lia | lia | cbn; lia]. }
assert (HARV : AR trasegs B ly' S' W' memV mdV).
{ apply (AR_after_run B HB ARL ly' S' W' E2 L_mem mem' memV md' matV HAR' (proj2 (proj2 (proj2 L_mem_wf)))); [rewrite E2_0; exact Ulo | rewrite E2_0; exact HCT | exact HFV |].
rewrite E2_0. intros a Ha. exact (apresent_some' _ _ _ (HwinV a Ha)). }
assert (HSOV : so_state xst j (w_H W') memV).
{ exact (so_state_frame xst XFR j (w_H W') E2 L_mem _ _ HFrV (proj2 (proj2 CM_so_ok)) ltac:(rewrite E2_0; exact Ulo) ltac:(rewrite E2_0; exact E2_6) HSO'). }
assert (HROV : arodata_ok B (aview trasegs (w_H W') memV)).
{ exact (arodata_frame (w_H W') E2 L_mem _ _ HFrV (proj2 (proj2 (proj2 L_mem_wf))) ltac:(rewrite E2_0; exact Ulo) HRO'). }
assert (HRD : rdword (aview trasegs (w_H W') memV) (spZ regsV + 24) = Some 0) by (rewrite HspV; exact (rdword_vararg E2 (w_H W') memV HMV E2_0)).
assert (PREV : printf_pre B ly' S' W' regsV memV mdV).
{ split; [exact HARV|]. split; [exact HraV|].
split; [rewrite HspV; replace (usp - 288) with (usp + (-18) * 16) by lia; rewrite Z.mod_add by lia; exact U16|].
split; [rewrite HspV; lia|]. split; [rewrite HspV; unfold top_ok in HTOP'; lia|].
split; [rewrite HspV; lia|]. split; [unfold top_ok in HTOP'; tauto|]. split; [unfold top_ok in HTOP'; tauto|]. split; [exact HROV|].
split; [rewrite HspV; intros a Ha; apply HwinV; unfold PF_STK in Ha; lia|].
split; [rewrite (ts_gp B HB); exact RV3|]. split; [rewrite (ts_tp B HB); exact RV4|].
split; [exact RV10|]. split; [rewrite RV11, HspV; unfold w64; f_equal; lia | exact HRD]. }
assert (POST : printf_post B xst ly' S' W' regsV memV mdV (Datatypes.S j) (wr ch_stdout (concat (repeat line0 (r + (Datatypes.S j - 1)))) (ex 0 (in_fs inp)))).
2:{ rewrite HshapeV, PCV. fold regsV memV.
change (mkCfg (mkst regsV (Z_to_bv 64 A_icpt_vprintf) memV (seg_rom trasegs)) mdV) with (cfg_at trasegs A_icpt_vprintf regsV memV mdV).
assert (HfdsV : m_fds mdV = APSG.fds_std) by (subst mdV; rewrite wvb_fds', Efds; exact Hfds).
destruct j as [|j'].
-
replace (Datatypes.S r + (0 - 1))%nat with (Datatypes.S r) by lia. cbn [repeat concat].
apply (srz_conseq trasegs _ (wr ch_stdout line0 (wr ch_stdout (concat (repeat line0 r)) (ex 0 (in_fs inp))))); [| apply wr_app].
apply (PF1 _ ly' S' W' regsV memV mdV _ PREV ltac:(rdrv_lia) ltac:(destruct HSOV as [[_ X]|[X _]]; [exact X | exfalso; lia]) HfdsV HAI3).
replace (r + (1 - 1))%nat with r in POST by lia. exact POST.
-
apply (PFN _ ly' S' W' regsV memV mdV _ (Datatypes.S j') PREV ltac:(rdrv_lia) ltac:(destruct HSOV as [[X _]|[_ X]]; [exfalso; lia | exact X]) ltac:(lia) HfdsV HAI3).
replace (Datatypes.S r + (Datatypes.S j' - 1))%nat with (r + (Datatypes.S (Datatypes.S j') - 1))%nat by lia. exact POST. }
intros regs4 mem4 md4 HAR4 HP4 Hs4 Ha04 HX4 Hfr4 Hpres4 HAI4. unfold cfg_at. rewrite HraV. rewrite HspV in Hfr4.
pose proof (same_but_materialized_frame _ _ Hs4) as (_ & _ & _ & _ & _ & _ & _ & _ & Hfds4 & _ & _ & Hfs4 & _).
rewrite HshapeV, restrict_mkst_fx in HSV. fold regsV memV in HSV. rewrite PCV in HSV.
pose proof (vp_reseat E2 W' regsV memV regs4 mem4 HSV E2_0 E2_6 HP4 Ha04 Hfr4 Hpres4) as HS5.
set (E4 := havoc E2 K_VP (map (getr regs4) CLOB')) in HS5.
assert (E4old : forall i, (i < K_VP)%nat -> ew E4 i = ew E2 i) by (intros i Hi; subst E4; apply ew_havoc_old; exact Hi).
assert (E4_0 : bv_unsigned (ew E4 0) = usp) by (rewrite E4old by (unfold K_VP, A_BUF, A_LEN, K_PP; lia); exact E2_0).
assert (E4_6 : usp <= bv_unsigned (ew E4 6)) by (rewrite E4old by (unfold K_VP, A_BUF, A_LEN, K_PP; lia); exact E2_6).
assert (E4_65 : bv_unsigned (ew E4 166) = Z.of_nat (Datatypes.S r)) by (rewrite E4old by (unfold K_VP, A_BUF, A_LEN, K_PP; lia); rewrite E2old by (unfold K_LR, A_BUF, A_LEN, K_PP; lia); exact E65).
assert (HSO4 : so_state xst (Datatypes.S j) (w_H W') mem4) by (right; split; [lia | exact HX4]).
assert (HRO4 : arodata_ok B (aview trasegs (w_H W') mem4)).
{ apply (arodata_keep (w_H W') (w_H W') memV mem4); [| exact HROV]. intros a H1 _ _. destruct (in_ro_static a H1) as [Y1 Y2]. pose proof (in_ro_range a H1).
apply Hfr4; [lia | unfold PF_STK; lia | exact Y2]. }
assert (Hwin4 : forall a, usp - 65536 <= a < usp -> apresent (w_H W') mem4 a)
by (intros a Ha; apply Hpres4; [unfold sp_window_lo, sp_window_hi in *; lia | unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI; unfold sp_window_lo in Ulo; lia | apply HwinV; exact Ha]).
rewrite <- restrict_mkst_fx in HS5.
apply (SRr_srealizes trasegs W' _ _ _ (br_run E4 W' regs4 mem4 md4 HS5) HAI4).
intros W2 c2 _ HAI5 (-> & msB & matB & -> & HSB & HFB & HFrB). cbn [cfg_model] in HAI5.
set (mdB := with_vm_backing (m_vm_lazy md4) matB md4) in *.
pose proof (st_ok_mem_ok trasegs E4 S_BR _ HSB) as HMB. cbn [restrict ms_mem] in HMB.
rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 rsFQ_eq)))))))) in HMB.
assert (HwinB : forall a, usp - 65536 <= a < usp -> apresent (w_H W') (ms_mem msB) a).
{ intros a Ha. destruct (Z.lt_ge_cases a (usp - 208)); [| destruct (Z.lt_ge_cases a (usp - 128))].
- eapply (win_present sp Hsp E4 (w_H W') (ms_mem msB) (ss_mem S_VP)); [exact HMB | left; reflexivity | exact E4_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E4 (w_H W') (ms_mem msB) (ss_mem S_VP)); [exact HMB | right; left; reflexivity | exact E4_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E4 (w_H W') (ms_mem msB) (ss_mem S_VP)); [exact HMB | right; right; left; reflexivity | exact E4_0 | lia | lia | cbn; lia]. }
pose proof calls_checks as (_ & _ & _ & _ & CKF & WFF & NCF & MAF & KPF & WOKV & SOKV & WOKF & SOKF & _).
assert (HARB : AR trasegs B ly' S' W' (ms_mem msB) mdB).
{ apply (AR_after_run B HB ARL ly' S' W' E4 (ss_mem S_VP) mem4 (ms_mem msB) md4 matB HAR4 WOKV); [rewrite E4_0; exact Ulo | rewrite E4_0; exact HCT | exact HFB |].
rewrite E4_0. intros a Ha. exact (apresent_some' _ _ _ (HwinB a Ha)). }
assert (HSOB : so_state xst (Datatypes.S j) (w_H W') (ms_mem msB)).
{ exact (so_state_frame xst XFR (Datatypes.S j) (w_H W') E4 (ss_mem S_VP) _ _ HFrB SOKV ltac:(rewrite E4_0; exact Ulo) ltac:(rewrite E4_0; exact E4_6) HSO4). }
assert (HROB : arodata_ok B (aview trasegs (w_H W') (ms_mem msB))).
{ exact (arodata_frame (w_H W') E4 (ss_mem S_VP) _ _ HFrB WOKV ltac:(rewrite E4_0; exact Ulo) HRO4). }
assert (HfsB : m_fs mdB = in_fs inp) by (subst mdB; rewrite wvb_fs', Hfs4; subst mdV; rewrite wvb_fs', Efs; exact Hfs).
assert (HfdsB : m_fds mdB = APSG.fds_std) by (subst mdB; rewrite wvb_fds', Hfds4; subst mdV; rewrite wvb_fds', Efds; exact Hfds).
destruct (Nat.eq_dec r 0) as [Hr0 | Hr1].
-
assert (HSB' : st_ok trasegs E4 (add_cond S_BR cond_BRf) (restrict (w_H W') msB)).
{ apply (st_ok_add_cond trasegs E4 S_BR _ BC_EQ (SOff 166 (-1)) (SLit 0) HSB). cbn [ac_c ac_a ac_b sv_denot Sem.branch_taken].
rewrite E4_65, Hr0. reflexivity. }
apply (SRr_srealizes trasegs W' _ _ _ (fq_run E4 W' msB mdB HSB') HAI5).
intros W3 c3 _ HAI6 (-> & msF & matF & -> & HSF & HFF & HFrF). cbn [cfg_model] in HAI6.
set (mdF := with_vm_backing (m_vm_lazy mdB) matF mdB) in *.
pose proof (st_ok_restrict_mkst trasegs (w_H W') E4 S_FQ msF HSF RVF) as HshapeF.
set (regsF := ms_regs msF) in *. set (memF := ms_mem msF) in *.
pose proof S_FQ_regs as (F1r & F2r & F3r & F4r & F8r & F10r).
assert (RF1 : getr regsF 1%bv = w64 RA_FQ) by (subst regsF; rewrite (st_ok_restrict_reg trasegs (w_H W') E4 S_FQ msF 1%bv HSF), F1r; reflexivity).
assert (RF2 : getr regsF 2%bv = Z_to_bv 64 (usp + -208)) by (subst regsF; rewrite (st_ok_restrict_reg trasegs (w_H W') E4 S_FQ msF 2%bv HSF), F2r; cbn [sv_denot]; rewrite E4_0; reflexivity).
assert (RF3 : getr regsF 3%bv = w64 TRA_GP) by (subst regsF; rewrite (st_ok_restrict_reg trasegs (w_H W') E4 S_FQ msF 3%bv HSF), F3r; reflexivity).
assert (RF4 : getr regsF 4%bv = w64 TRA_TP) by (subst regsF; rewrite (st_ok_restrict_reg trasegs (w_H W') E4 S_FQ msF 4%bv HSF), F4r; reflexivity).
assert (RF8 : getr regsF 8%bv = w64 (payload_len data)).
{ subst regsF. rewrite (st_ok_restrict_reg trasegs (w_H W') E4 S_FQ msF 8%bv HSF), F8r. cbn [sv_denot].
rewrite Z.add_0_r, E4old by (unfold K_VP, A_BUF, A_LEN, K_PP; lia). rewrite E2old by (unfold K_LR, A_BUF, A_LEN, K_PP; lia). rewrite <- E61. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (RF10 : getr regsF 10%bv = w64 q).
{ subst regsF. rewrite (st_ok_restrict_reg trasegs (w_H W') E4 S_FQ msF 10%bv HSF), F10r. cbn [sv_denot].
rewrite Z.add_0_r, E4old by (unfold K_VP, A_BUF, A_LEN, K_PP; lia). rewrite E2old by (unfold K_LR, A_BUF, A_LEN, K_PP; lia). rewrite <- E63. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (HspF : spZ regsF = usp + -208) by (unfold spZ; rewrite RF2; apply u64_lit; unfold sp_window_lo in Ulo; lia).
assert (HraF : raZ regsF = RA_FQ) by (unfold raZ; rewrite RF1; apply u64_lit; unfold RA_FQ; lia).
pose proof (st_ok_mem_ok trasegs E4 S_FQ _ HSF) as HMF. cbn [restrict ms_mem] in HMF. fold memF in HMF.
rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 rsFQ_eq))))))))) in HMF.
assert (HwinF : forall a, usp - 65536 <= a < usp -> apresent (w_H W') memF a).
{ intros a Ha. destruct (Z.lt_ge_cases a (usp - 208)); [| destruct (Z.lt_ge_cases a (usp - 128))].
- eapply (win_present sp Hsp E4 (w_H W') memF (ss_mem S_VP)); [exact HMF | left; reflexivity | exact E4_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E4 (w_H W') memF (ss_mem S_VP)); [exact HMF | right; left; reflexivity | exact E4_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E4 (w_H W') memF (ss_mem S_VP)); [exact HMF | right; right; left; reflexivity | exact E4_0 | lia | lia | cbn; lia]. }
assert (HARF : AR trasegs B ly' S' W' memF mdF).
{ apply (AR_after_run B HB ARL ly' S' W' E4 (ss_mem S_VP) (ms_mem msB) memF mdB matF HARB WOKV); [rewrite E4_0; exact Ulo | rewrite E4_0; exact HCT | exact HFF |].
rewrite E4_0. intros a Ha. exact (apresent_some' _ _ _ (HwinF a Ha)). }
assert (HSOF : so_state xst (Datatypes.S j) (w_H W') memF).
{ exact (so_state_frame xst XFR (Datatypes.S j) (w_H W') E4 (ss_mem S_VP) _ _ HFrF SOKV ltac:(rewrite E4_0; exact Ulo) ltac:(rewrite E4_0; exact E4_6) HSOB). }
assert (HWF' : Wf (as_universe B) S') by exact (am_wf _ _ _ _ (proj1 HARF)).
assert (PREF : drv_pre B ly' S' W' regsF memF mdF).
{ split; [exact HARF|]. split; [unfold top_ok in *; tauto|]. split; [rdrv_lia|].
split; [rewrite RF1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity|]. split; [rewrite HraF; unfold RA_FQ; lia|].
split; [rewrite HspF; rewrite <- Zplus_mod_idemp_l, U16; reflexivity|].
split; [rewrite HspF; unfold sp_window_lo in *; lia|]. split; [rewrite HspF; unfold top_ok in HTOP'; lia|].
split; [rewrite HspF; intros a Ha; apply HwinF; unfold ASTACK in Ha; lia|].
split; [rewrite (ts_gp B HB); exact RF3|]. split; [rewrite (ts_tp B HB); exact RF4|].
split; [| exact HQT']. unfold s0Z. rewrite RF8. unfold w64. rewrite u64_lit by lia. lia. }
assert (Hinb : In (buf, cap) (ablocks B ly' S')) by (destruct HBL' as [(_ & _ & HPm) | (_ & HPm)]; apply (Permutation_in _ (Permutation_sym HPm)); apply in_or_app; right; left; reflexivity).
assert (Hbuf : 4096 <= buf).
{ pose proof (al_blocks _ _ ARL ly' S' W' memF mdF _ _ HARF Hinb) as (_ & X & _). exact X. }
rewrite HshapeF, PCF. fold regsF memF. replace (Z_to_bv 64 A_wrap_free) with (w64 (pc_wrap_free (as_code B))) by (rewrite (ts_code B HB); reflexivity).
change (mkCfg (mkst regsF (w64 (pc_wrap_free (as_code B))) memF (seg_rom trasegs)) mdF) with (cfg_at trasegs (pc_wrap_free (as_code B)) regsF memF mdF).
assert (FSITE : exists (pf : sptr) (nf : Z) (Eb : Z -> Prop),
(pf = PNull \/ In (pf, nf) (blocks S')) /\ (forall a, Eb a -> a < alloc_ceiling /\ ~ in_img trasegs a) /\ (forall a, Eb a -> ~ STDOUT_MUT a) /\
(pf = PNull -> payload_len data = 0) /\ (pf <> PNull -> sptr_addr B ly' pf = q /\ nf = payload_len data /\ 0 < payload_len data) /\
SRr trasegs W' (cfg_at trasegs (pc_wrap_free (as_code B)) regsF memF mdF)
(fun W'' c'' => exists ly6 S6 regs6 mem6 md6 trc tr,
In trc (as_universe B) /\ apath (free pf trc S') tr (tt, S6) /\
c'' = cfg_at trasegs (raZ regsF) regs6 mem6 md6 /\
acall_post trasegs B ASTACK ly' S' W' regsF memF mdF Eb ly6 S6 W'' regs6 mem6 md6)).
{ destruct HBL' as [(Hz & Hq & HPm) | (Hp & HPm)].
- exists PNull, 0, (fun _ => False). split; [left; reflexivity|]. split; [intros a []|]. split; [intros a []|].
split; [intros _; exact Hz|]. split; [intros X; exfalso; exact (X eq_refl)|].
apply (FREEN _ ly' S' W' regsF memF mdF PREF).
+ rewrite RF10, Hq. reflexivity.
+ rewrite (ts_code B HB), HraF. apply (ts_universe_drv B HB). cbn. tauto.
+ rewrite (ts_code B HB). apply (ts_universe_drv B HB). cbn. tauto.
- assert (Hinq : In (q, payload_len data) (ablocks B ly' S')) by (apply (Permutation_in _ (Permutation_sym HPm)); apply in_or_app; right; right; left; reflexivity).
pose proof (al_blocks _ _ ARL ly' S' W' memF mdF _ _ HARF Hinq) as (_ & Hq4096 & Hqce & _).
assert (NIMGQ : forall a, q <= a < q + req_size (payload_len data) -> ~ in_img trasegs a).
{ intros a Ha. exact (proj2 (al_client_img _ _ ARL ly' S' W' memF mdF a HARF (or_introl (ex_intro _ _ (ex_intro _ _ (conj Hinq Ha)))))). }
unfold ablocks in Hinq. apply in_map_iff in Hinq as ([pf nf] & Hpf & Hinbf). cbn [fst snd] in Hpf. injection Hpf as Hq Hn.
assert (Hreqq : req_size (payload_len data) = payload_len data) by (unfold req_size; destruct (Z.eqb_spec (payload_len data) 0); lia).
rewrite Hreqq in Hqce, NIMGQ.
exists pf, nf, (fun a => sptr_addr B ly' pf <= a < sptr_addr B ly' pf + req_size nf).
split; [right; exact Hinbf|]. split; [intros a Ha; rewrite Hq, Hn, Hreqq in Ha; split; [lia | exact (NIMGQ a Ha)]|].
split; [intros a Ha X; rewrite Hq, Hn, Hreqq in Ha; apply (NIMGQ a Ha); apply in_img_rw; unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in X; lia|].
split; [intros ->; exfalso; cbn in Hq; lia|]. split; [intros _; rewrite Hq, Hn; repeat split; [reflexivity .. | exact Hp]|].
apply (FREE _ ly' S' W' regsF memF mdF pf nf PREF Hinbf).
+ rewrite RF10, Hq. reflexivity.
+ rewrite (ts_code B HB), HraF. apply (ts_universe_drv B HB). cbn. tauto.
+ rewrite (ts_code B HB). apply (ts_universe_drv B HB). cbn. tauto. }
destruct FSITE as (pf & nf & Eb & Hpfin & HEb & HEbso & HpfN & HpfB & FSITE).
eapply (SRr_srealizes trasegs W' (cfg_at trasegs (pc_wrap_free (as_code B)) regsF memF mdF)); [exact FSITE | exact HAI6 |].
cbv beta. intros W4 c4 Hwle4 HAI7 (ly6 & S6 & regs6 & mem6 & md6 & trc6 & tr6 & Htrc6 & Hpath6 & -> & HPOST6). cbn [cfg_model] in HAI7.
unfold cfg_at. rewrite HraF.
pose proof HPOST6 as (HAR6 & Hlyle6 & Hwle6 & HP6 & Hio6 & Hfr6 & Hsc6).
destruct (atok_apath _ _ _ tr6 _ (drv_free_big _ ML S' pf nf trc6 HWF' HQT' ltac:(rdrv_lia)
ltac:(destruct Hpfin as [X|X]; [left; exact X | right; exact X]) Htrc6) Hpath6) as (ns6 & HFP & HQT6 & HJB6).
cbn [free_post snd] in HFP. cbn [snd] in HQT6, HJB6. destruct HFP as (HWF6 & Hnev6 & _ & Hfr6' & (l1 & l2 & Hcase & Hbl6) & _). cbn [snd] in HWF6, Hnev6, Hbl6, Hfr6', HQT6.
destruct (same_io_fs_fds _ _ Hio6) as [Efs6 Efds6].
pose proof (al_layout _ _ ARL ly' S' W' memF mdF ly6 HARF Hlyle6) as (Habl6 & _ & _).
assert (EXT6 : forall b n, In (b, n) (blocks S') -> sptr_addr B ly6 b = sptr_addr B ly' b).
{ intros b n Hb. unfold ablocks in Habl6. pose proof (ext_in_map Habl6 (b, n) Hb) as X. cbn [fst snd] in X. injection X as X1. exact X1. }
assert (HBL6 : exists pb6, In (pb6, cap) (blocks S6) /\ sptr_addr B ly6 pb6 = buf).
{ unfold ablocks in Hinb. apply in_map_iff in Hinb as ([b0 n0] & Eb0 & HinS'). cbn [fst snd] in Eb0. injection Eb0 as Ea En. subst n0.
assert (GOAL : In (b0, cap) (blocks S6) \/ exists b1, In (b1, cap) (blocks S6) /\ sptr_addr B ly' b1 = buf).
{ destruct HBL' as [(Hz & Hq0 & HPm) | (Hp & HPm)].
- assert (Epf : pf = PNull).
{ destruct pf; [reflexivity | | |]; exfalso; (destruct (HpfB ltac:(discriminate)) as (_ & _ & X)); lia. }
subst pf. left. rewrite Hbl6. destruct Hcase as [[_ E12] | E12].
+ rewrite E12. exact HinS'.
+ rewrite E12 in HinS'. apply in_app_or in HinS' as [X|[X|X]]; apply in_or_app; [left; exact X | | right; exact X].
exfalso. injection X as Xb Xn. rewrite <- Xb in Ea. cbn in Ea. lia.
- assert (NE : pf <> PNull) by (intros ->; pose proof (HpfN eq_refl); lia).
destruct (HpfB NE) as (Hq & Hn & _).
destruct Hcase as [[Ez _] | E12]; [exfalso; exact (NE Ez)|].
right. unfold ablocks in HPm. rewrite E12, map_app in HPm. cbn [map fst snd] in HPm. rewrite Hq, Hn in HPm.
change (LK' ++ [(buf, cap); (q, payload_len data)]) with (LK' ++ ([(buf, cap)] ++ (q, payload_len data) :: [])) in HPm.
rewrite app_assoc in HPm.
pose proof (Permutation_app_inv _ _ (LK' ++ [(buf, cap)]) [] (q, payload_len data) HPm) as HP2. rewrite app_nil_r, <- map_app in HP2.
assert (Hin2 : In (buf, cap) (map (fun b : sptr * Z => (sptr_addr B ly' (fst b), snd b)) (l1 ++ l2))).
{ apply (Permutation_in _ (Permutation_sym HP2)). apply in_or_app. right. left. reflexivity. }
apply in_map_iff in Hin2 as ([b1 n1] & Eb1 & Hin1). cbn [fst snd] in Eb1. injection Eb1 as Ea1 En1. subst n1.
exists b1. split; [rewrite Hbl6; exact Hin1 | exact Ea1]. }
destruct GOAL as [X | (b1 & X & Ea1)].
- exists b0. split; [exact X|]. rewrite (EXT6 b0 cap HinS'). exact Ea.
- exists b1. split; [exact X|].
assert (Hin1' : In (b1, cap) (blocks S')).
{ rewrite Hbl6 in X. destruct Hcase as [[_ E12] | E12]; rewrite E12 || rewrite <- E12; [exact X|]. apply in_app_or in X as [Y|Y]; apply in_or_app; [left; exact Y | right; right; exact Y]. }
rewrite (EXT6 b1 cap Hin1'). exact Ea1. }
destruct HBL6 as (pb6 & Hbl6S & Hpb6).
rewrite HshapeF, restrict_mkst_fx in HSF. fold regsF memF in HSF. rewrite <- restrict_mkst_fx, <- HshapeF in HSF.
pose proof (drv_after_call B HB ARL K_FQ E4 S_FQ msF ly' S' W' mdF Eb ly6 S6 W4 regs6 mem6 md6 rsFQ RA_FQ usp (-208)
HSF RVF CKF WFF NCF MAF submem_FQ F1r HPOST6 HARF HEb KPF E4_0 E4_6 HspF ltac:(lia) Ulo HCT ltac:(intros a Ha; apply HwinF; lia)) as HS7.
rewrite S_FQr_eq in HS7. set (E8 := havoc E4 K_FQ (map (getr regs6) CLOB)) in HS7.
assert (E8old : forall i, (i < K_FQ)%nat -> ew E8 i = ew E4 i) by (intros i Hi; subst E8; apply ew_havoc_old; exact Hi).
assert (E8_0 : bv_unsigned (ew E8 0) = usp) by (rewrite E8old by (unfold K_FQ, A_BUF, A_LEN, K_PP; lia); exact E4_0).
assert (E8_6 : usp <= bv_unsigned (ew E8 6)) by (rewrite E8old by (unfold K_FQ, A_BUF, A_LEN, K_PP; lia); exact E4_6).
assert (HSO6 : so_state xst (Datatypes.S j) (w_H W4) mem6).
{ apply (so_state_keep xst XFR (Datatypes.S j) (w_H W') (w_H W4) memF mem6); [| exact HSOF]. intros a Ha. apply Hfr6.
- unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha. lia.
- exact (so_not_owned B HB ARL ly' S' W' memF mdF a HARF Ha).
- exact (so_not_owned B HB ARL ly6 S6 W4 mem6 md6 a HAR6 Ha).
- unfold ascratch. rewrite HspF, (ts_errno B HB). unfold TRA_ERRNO, ASTACK. unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha. unfold sp_window_lo in Ulo. lia.
- intros X. exact (HEbso a X Ha). }
apply (SRr_srealizes trasegs W4 _ _ _ (xm_run E8 W4 regs6 mem6 md6 HS7) HAI7).
intros W5 c5 _ HAI8 (-> & msX & matX & -> & HSX & HFX & HFrX). cbn [cfg_model] in HAI8.
set (mdX := with_vm_backing (m_vm_lazy md6) matX md6) in *.
pose proof (st_ok_mem_ok trasegs E8 S_XM _ HSX) as HMX. cbn [restrict ms_mem] in HMX. rewrite (proj1 (proj2 rsFQ_eq)) in HMX.
assert (HwinX : forall a, usp - 65536 <= a < usp -> apresent (w_H W4) (ms_mem msX) a).
{ intros a Ha. destruct (Z.lt_ge_cases a (usp - 208)); [| destruct (Z.lt_ge_cases a (usp - 128))].
- eapply (win_present sp Hsp E8 (w_H W4) (ms_mem msX) (WIN (-208) :: rsFQ)); [exact HMX | left; reflexivity | exact E8_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E8 (w_H W4) (ms_mem msX) (WIN (-208) :: rsFQ)); [exact HMX | right; left; reflexivity | exact E8_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E8 (w_H W4) (ms_mem msX) (WIN (-208) :: rsFQ)); [exact HMX | right; right; left; reflexivity | exact E8_0 | lia | lia | cbn; lia]. }
assert (HARX : AR trasegs B ly6 S6 W4 (ms_mem msX) mdX).
{         apply (AR_after_run B HB ARL ly6 S6 W4 E8 (WIN (-208) :: rsFQ) mem6 (ms_mem msX) md6 matX HAR6 WOKF); [rewrite E8_0; exact Ulo | rewrite E8_0; exact HCT | exact HFX |].
rewrite E8_0. intros a Ha. exact (apresent_some' _ _ _ (HwinX a Ha)). }
assert (HSOX : so_state xst (Datatypes.S j) (w_H W4) (ms_mem msX)).
{         exact (so_state_frame xst XFR (Datatypes.S j) (w_H W4) E8 (WIN (-208) :: rsFQ) _ _ HFrX SOKF ltac:(rewrite E8_0; exact Ulo) ltac:(rewrite E8_0; exact E8_6) HSO6). }
pose proof (xm_to_CM E8 W4 msX HSX) as (HSCM & V79 & ECold).
set (E9 := E_CM E8 (ms_regs msX)) in *.
replace (r + (Datatypes.S j - 1))%nat with (Datatypes.S j - 1)%nat by lia.
replace (ex 0 (in_fs inp)) with (ex (if count_mode data then 0 else 0) (in_fs inp)) by (destruct (count_mode data); reflexivity).
apply (tra_main_tail B HB ARL ML xst (FREE _) (EXITL _) XFR sp inp xw xd a0 p Hsp Hva Hve E9 W4 msX mdX ly6 S6 data pb6 cap 0 (Datatypes.S j)).
+ intros i Hi. rewrite ECold by (unfold K_CM, K_M1 in *; lia). rewrite E8old by (unfold K_FQ, K_M1 in *; lia). rewrite E4old by (unfold K_VP, K_M1 in *; lia).
rewrite E2old by (unfold K_LR, K_M1 in *; lia). apply HEE. exact Hi.
+ change (ed E9 2) with (ed E 2). exact HEd.
+ exact Hlen.
+ rewrite ECold by (unfold K_CM, A_BUF, A_LEN, K_PP; lia). rewrite E8old by (unfold K_FQ, A_BUF, A_LEN, K_PP; lia). rewrite E4old by (unfold K_VP, A_BUF, A_LEN, K_PP; lia). rewrite E2old by (unfold K_LR, A_BUF, A_LEN, K_PP; lia). rewrite Hpb6. exact E41.
+ exact V79.
+ left. reflexivity.
+ exact HSCM.
+ exact HAI8.
+ exact HARX.
+ exact (top_ok_le _ _ _ _ Hlyle6 HTOP').
+ exact Hbl6S.
+ exact (HQT6 HQT').
+ rdrv_lia.
+ exact HSOX.
+ subst mdX. rewrite wvb_fds', Efds6. subst mdF. rewrite wvb_fds'. exact HfdsB.
+ subst mdX. rewrite wvb_fs', Efs6. subst mdF. rewrite wvb_fs'. exact HfsB.
-
assert (HSB' : st_ok trasegs E4 (add_cond S_BR cond_BRt) (restrict (w_H W') msB)).
{ apply (st_ok_add_cond trasegs E4 S_BR _ BC_NE (SOff 166 (-1)) (SLit 0) HSB). cbn [ac_c ac_a ac_b sv_denot Sem.branch_taken].
rewrite E4_65. cbn [negb].
destruct (bv_eqb (Z_to_bv 64 (Z.of_nat (Datatypes.S r) + -1)) (Z_to_bv 64 0)) eqn:Eq; [|reflexivity].
exfalso. apply bv_eqb_eq in Eq. apply (f_equal bv_unsigned) in Eq. rewrite !u64_lit in Eq by lia. lia. }
apply (SRr_srealizes trasegs W' _ _ _ (l2_run E4 W' msB mdB HSB') HAI5).
intros W3 c3 _ HAI6 (-> & msL & matL & -> & HSL2 & HFL & HFrL). cbn [cfg_model] in HAI6.
set (mdL := with_vm_backing (m_vm_lazy mdB) matL mdB) in *.
pose proof (st_ok_mem_ok trasegs E4 S_L2 _ HSL2) as HML. cbn [restrict ms_mem] in HML.
assert (HwinL : forall a, usp - 65536 <= a < usp -> apresent (w_H W') (ms_mem msL) a).
{ intros a Ha. destruct (Z.lt_ge_cases a (usp - 208)); [| destruct (Z.lt_ge_cases a (usp - 128))].
- eapply (win_present sp Hsp E4 (w_H W') (ms_mem msL) (ss_mem S_L2)); [exact HML | left; reflexivity | exact E4_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E4 (w_H W') (ms_mem msL) (ss_mem S_L2)); [exact HML | right; left; reflexivity | exact E4_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E4 (w_H W') (ms_mem msL) (ss_mem S_L2)); [exact HML | right; right; left; reflexivity | exact E4_0 | lia | lia | cbn; lia]. }
assert (HARL : AR trasegs B ly' S' W' (ms_mem msL) mdL).
{ apply (AR_after_run B HB ARL ly' S' W' E4 (ss_mem S_VP) (ms_mem msB) (ms_mem msL) mdB matL HARB WOKV); [rewrite E4_0; exact Ulo | rewrite E4_0; exact HCT | exact HFL |].
rewrite E4_0. intros a Ha. exact (apresent_some' _ _ _ (HwinL a Ha)). }
assert (HSOL : so_state xst (Datatypes.S j) (w_H W') (ms_mem msL)).
{ exact (so_state_frame xst XFR (Datatypes.S j) (w_H W') E4 (ss_mem S_VP) _ _ HFrL SOKV ltac:(rewrite E4_0; exact Ulo) ltac:(rewrite E4_0; exact E4_6) HSOB). }
assert (HROL : arodata_ok B (aview trasegs (w_H W') (ms_mem msL))).
{ exact (arodata_frame (w_H W') E4 (ss_mem S_VP) _ _ HFrL WOKV ltac:(rewrite E4_0; exact Ulo) HROB). }
pose proof (l2_to_L E4 W' msL (Z.of_nat (Datatypes.S r)) HSL2 E4_65 ltac:(lia)) as (HSLn & V65n & ELold).
set (E6n := E_L2 E4 (ms_regs msL)) in *.
apply (IH fx' (Datatypes.S j) E6n W' msL mdL ly' S' data buf cap q LK' Hlk Hok).
+ intros i Hi. rewrite ELold by (unfold K_M1 in Hi; lia). rewrite E4old by (unfold K_VP, K_M1 in *; lia). rewrite E2old by (unfold K_LR, K_M1 in *; lia). apply HEE. exact Hi.
+ change (ed E6n 2) with (ed E 2). exact HEd.
+ rewrite ELold by (unfold A_BUF, A_LEN, K_PP; lia). rewrite E4old by (unfold K_VP, A_BUF, A_LEN, K_PP; lia). rewrite E2old by (unfold K_LR, A_BUF, A_LEN, K_PP; lia). exact E41.
+ rewrite ELold by (unfold A_BUF, A_LEN, K_PP; lia). rewrite E4old by (unfold K_VP, A_BUF, A_LEN, K_PP; lia). rewrite E2old by (unfold K_LR, A_BUF, A_LEN, K_PP; lia). exact E61.
+ rewrite ELold by (unfold A_BUF, A_LEN, K_PP; lia). rewrite E4old by (unfold K_VP, A_BUF, A_LEN, K_PP; lia). rewrite E2old by (unfold K_LR, A_BUF, A_LEN, K_PP; lia). exact E62.
+ rewrite ELold by (unfold A_BUF, A_LEN, K_PP; lia). rewrite E4old by (unfold K_VP, A_BUF, A_LEN, K_PP; lia). rewrite E2old by (unfold K_LR, A_BUF, A_LEN, K_PP; lia). exact E63.
+ rewrite V65n. lia.
+ exact HSLn.
+ lia.
+ lia.
+ exact HBL'.
+ exact HLK'0.
+ clear - HLK'. lia.
+ exact Hfrs.
+ exact HQT'.
+ exact HAI6.
+ exact HARL.
+ exact HTOP'.
+ exact Hnev1.
+ exact Hcap.
+ exact HLc.
+ exact Hlen.
+ exact HSOL.
+ exact HROL.
+ subst mdL. rewrite wvb_fs'. exact HfsB.
+ subst mdL. rewrite wvb_fds'. exact HfdsB.
+ exact Hfrm'.
Qed.
Theorem tra_loop_L_at : forall (fx : YK11.FPState), frm_zero (@fp_csr fx) -> forall E (W : world trasegs) ms md ly S data (pb pq : sptr) (cap q : Z) (j r : nat),
fs_lookup (in_fs inp) p = Some data -> 6 + config_len data <= dlen data ->
(forall k, (k < K_M1)%nat -> ew E k = ew EL k) -> ed E 2 = data ->
bv_unsigned (ew E A_BUF) = sptr_addr B ly pb -> bv_unsigned (ew E A_LEN) = dlen data ->
bv_unsigned (ew E 161) = sptr_addr B ly pb + 2 + config_len data ->
bv_unsigned (ew E 162) = payload_len data -> bv_unsigned (ew E 163) = (if payload_len data =? 0 then A_EMPTY_tfa else q) ->
bv_unsigned (ew E 164) = q -> bv_unsigned (ew E 166) = Z.of_nat r ->
st_ok trasegs E S_L (restrict (w_H W) ms) ->
(1 <= r)%nat -> (j + r = calls data)%nat ->
((payload_len data = 0 /\ q = 0 /\ blocks S = [(pb, cap)])
\/ (0 < payload_len data /\ blocks S = [(pb, cap); (pq, payload_len data)] /\ sptr_addr B ly pq = q)) ->
frames S = [] -> qtightB S ->
AI trasegs (w_H W) (w_A W) md -> AR trasegs B ly S W (ms_mem ms) md -> top_ok usp ly ->
rbud S (Z.of_nat r) 3 -> 65536 <= cap <= 2 ^ 26 -> dlen data < cap ->
((j = 0%nat /\ stdout_img (w_H W) (ms_mem ms)) \/ ((1 <= j)%nat /\ xst j (w_H W) (ms_mem ms))) ->
arodata_ok B (aview trasegs (w_H W) (ms_mem ms)) ->
m_fs md = in_fs inp -> m_fds md = APSG.fds_std ->
srealizes trasegs (mkCfg ms md) (wr ch_stdout (concat (repeat line0 (r + (j - 1))%nat)) (ex 0 (in_fs inp))).
Proof.
intros fx Hfrm E W ms md ly S data pb pq cap q j r Hlk Hok HEE HEd E41 E42 E60 E61 E62 E63 E65 HS Hr Hjr HBL Hfr HQT HAI HAR HTOP Hnev Hcap HLc HSO HRO Hfs Hfds.
pose proof (calls_bound data) as Hcb. pose proof (config_len_bound data) as Hcl.
apply (calls_loop r fx j E W ms md ly S data (sptr_addr B ly pb) cap q [] Hlk Hok HEE HEd E41 E61 E62 E63 E65 HS Hr ltac:(lia)).
- destruct HBL as [(Hz & Hq & Hbl) | (Hp & Hbl & Hpq)]; [left | right]; unfold ablocks; rewrite Hbl; cbn [map fst snd app].
+ split; [exact Hz|]. split; [exact Hq | apply Permutation_refl].
+ split; [exact Hp|]. rewrite Hpq. apply Permutation_refl.
- cbn. lia.
- cbn. lia.
- exact Hfr.
- exact HQT.
- exact HAI.
- exact HAR.
- exact HTOP.
- exact Hnev.
- exact Hcap.
- exact HLc.
- unfold dlen in Hok. lia.
- exact HSO.
- exact HRO.
- exact Hfs.
- exact Hfds.
- exact Hfrm.
Qed.
End c.
Theorem tra_loop_L {fx : YK11.FPState} {rc : YN05.RunCeil} (B : asyms) (HB : TraSyms B) (ARL : AR_laws trasegs B) (ML : model_laws (as_universe B))
(xst : nat -> (word -> bool) -> (word -> option byte) -> Prop)
(LIB : forall fx : YK11.FPState, @lib_site_rgb fx rc B)
(PF1 : forall fx : YK11.FPState, @printf_first_tfa fx rc B xst) (PFN : forall fx : YK11.FPState, @printf_next_tfa fx rc B xst)
(FREE : forall fx : YK11.FPState, @free_site_tfa fx rc B) (FREEN : forall fx : YK11.FPState, @free_null_site_tfa fx rc B)
(EXITL : forall fx : YK11.FPState, @exit_leaf_tfa fx rc B xst) (XFR : xst_frame_tfa xst)
(FRM0 : frm_zero (@fp_csr fx)) : @loop_L_tfa fx rc B xst.
Proof.
intros sp inp xw xd E W ms md ly S a0 p data pb pq cap q j r Hargv Hsp Hva Hve Hvfs Hlk HRU.
exact (tra_loop_L_at B HB ARL ML xst LIB PF1 PFN FREE FREEN EXITL XFR sp inp xw xd a0 p Hsp Hva Hve
ltac:(intros d Hd; rewrite Hlk in Hd; injection Hd as <-; exact HRU) fx FRM0 E W ms md ly S data pb pq cap q j r Hlk).
Qed.
