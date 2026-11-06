(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YL0z.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/Reusable/YL0z.v; 101 of its 248 lines of code are new or changed and 57 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0o YK0h YK0i YK14 YK1b YK1a YK15 YK0k YK0n YK0p YP0n YM06 YM02.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YO0i YO0f YO0x YO0d YO0e YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO06.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YH00 YH01 YH03 YH02 YN3e.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN03 YL07 YL01 YL08 YL0d YL0e YL0f YL02 YL0a YL00 YL04 YL0c YL09 YL05 YL0g YL0k YL0o YL0m YL0u YL0r YL0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI06 YI16 YI14 YI5b YI5c YL0i YL06 YL03 YL0l YL0t GIWalk.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YL11 YL10 YL16 YL17 YL18 YL19 YL12 YL13 YL14 YL15.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05 YM0b YO03 YO04 YL0z DriverSlots.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YO0d_cf YO04_cfw YK15_cfw YL0k_cfw YL0i_cfw YL0l_cfw.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YL0u_cfwi YL0r_cfw YL0t_cfw.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YL10_cfwi YL11_cfwi YL12_cfwi YL13_cfwi YL14_cfwi YL15_cfwi YL16_cfwi YL17_cfwi YL18_cfwi YL19_cfwi.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Contract AllocSI AllocGS AllocSlots SlotAgree SlotAgreeI.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Lemma exit_room : forall A b cap n, WF A -> res_ok A b -> RPinv (2 ^ 24) 12 cap b -> 0 <= cap <= MAX_INPUT -> 0 <= n < cap ->
room b n /\ roomcf SRC_LIM_MIN (malloc n A).
Proof using.
intros A b cap n HW HR (V1 & V2 & V3 & V4 & V5) Hcap Hn.
pose proof (mdelta_le cap ltac:(lia)) as Hmd. pose proof (shcap_845 (rb_hand b) ltac:(lia)) as SC.
pose proof (page_round_bounds (n + IB + UNIT) ltac:(unfold IB, UNIT; lia)) as Hpr.
assert (Hroom : room b n).
{ unfold room. unfold MG_LIVE, MG_SLOTS, MG_REQ, MAX_INPUT, MMAX, IB, UNIT, PGSZ in *.
assert (rb_brk b / 4096 <= 2 * 12) by (apply Z.div_le_upper_bound; lia).
repeat split; try lia. }
split; [exact Hroom|]. apply (roomcf_malloc_res A b n SRC_LIM_MIN HW HR Hroom).
unfold rb_live, SRC_LIM_MIN, MAX_INPUT, MMAX, IB, UNIT, PGSZ in *. lia.
Qed.
Lemma one_block_counts : forall A buf cap, user_blocks A = [(buf, cap)] -> nblocks A = 1 /\ ubytes A = cap.
Proof using. intros A buf cap Hub. unfold nblocks, ubytes. rewrite Hub. cbn. split; lia. Qed.
Lemma exit_slots : forall A b buf cap, DI A -> res_ok A b -> RPinv (2 ^ 24) 12 cap b -> user_blocks A = [(buf, cap)] ->
65536 <= cap <= MAX_INPUT -> II A.
Proof using.
intros A b buf cap HDI HR (V1 & V2 & V3 & V4 & V5) Hub Hcap.
pose proof (mdelta_le cap ltac:(lia)) as Hmd. destruct (one_block_counts A buf cap Hub) as [N1 N2].
unfold MAX_INPUT in Hcap.
refine (proj1 (_ : res_ok_slots _ SBD)). apply res_ok_slots_SBD; [| exact HDI | lia | lia].
eapply res_ok_DRB; [exact HR | | | |]; unfold MAX_INPUT, MMAX, IB, UNIT, PGSZ in *; lia.
Qed.
Lemma exit_none_slots : forall A b buf cap n, DI A -> res_ok A b -> RPinv (2 ^ 24) 12 cap b -> user_blocks A = [(buf, cap)] ->
65536 <= cap <= MAX_INPUT -> 0 <= n < cap ->
forall tr A2, cpath (malloc n A) tr (None, A2) -> II A2.
Proof using.
intros A b buf cap n HDI HR HRP Hub Hcap Hn tr A2 Hp.
destruct (exit_room A b cap n (proj1 HDI) HR HRP ltac:(lia) Hn) as [Hroom _].
pose proof (leaves_cpath _ _ _ _ (malloc_leaves_res A b n (proj1 HDI) HR Hroom) Hp) as [[HW2 Hub2] HR2].
cbn [fst snd] in Hub2, HR2.
pose proof (DI_malloc A n tr None A2 HDI ltac:(lia) (cpath_yields _ _ _ Hp)) as HDI2.
destruct HRP as (V1 & V2 & V3 & V4 & V5).
pose proof (mdelta_le cap ltac:(lia)) as Hmd. pose proof (mdelta_le n ltac:(lia)) as Hmdn.
assert (Hub2' : user_blocks A2 = [(buf, cap)]) by (rewrite Hub2; exact Hub).
destruct (one_block_counts A2 buf cap Hub2') as [N1 N2].
unfold MAX_INPUT in Hcap.
refine (proj1 (_ : res_ok_slots _ SBD)). apply res_ok_slots_SBD; [| exact HDI2 | lia | lia].
eapply res_ok_DRB; [exact HR2 | | | |]; unfold rb_malloc; cbn [rb_bytes rb_cnt rb_hand rb_brk];
unfold MAX_INPUT, MMAX, IB, UNIT, PGSZ in *; lia.
Qed.
Section c.
Variable API : AllocAPI src0_msyms.
Hypothesis AX : AllocExtra src0_msyms (aa_MR API).
Variable GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop.
Variable RI : list byte -> nat -> list (Z * Z) -> astate -> Prop.
Variable OUT : list byte -> list byte.
Hypothesis GIL : G_local_T src0segs src0_G GI.
Hypothesis GI0 : forall mem, G_img src0segs src0_G mem -> GI 0%nat [] mem.
Hypothesis LIBXc : lib_contract_x_Rc_all src0_msyms API RI src0_G src0_R GI OUT LIBPC RA_LIB EMPTY LIB_STACK.
Hypothesis FCF : forall fx' : FPState, @free_contract_cfi fx' rc src0_msyms API.
Hypothesis TBL : forall L A mem md, aa_MR API L A mem md -> forall a, static_owned src0_msyms a -> 0 <= a < 2 ^ 64 ->
Mem.ro_addr src0segs (Z_to_bv 64 a) = true -> mbyte src0segs mem a = seg_rom src0segs (Z_to_bv 64 a).
Hypothesis RIii : forall pl j T A, RI pl j T A -> II A.
Hypothesis MRC : forall fx' : FPState, @malloc_realizes_cf fx' rc src0_msyms (aa_MR API).
Hypothesis LIMLAW : forall L A mem md, aa_MR API L A mem md -> SRC_LIM_MIN <= vm_limit (m_vmmaps md).
Hypothesis FRM : frm_zero fp_csr.
Variables (sp tid : word) (a0 path : list byte) (inp : ProcInput) (data : list byte) (rnd : EntryDraw).
Hypothesis HSA0 : forall G, anchored_atoms G = anchored_atoms RD_facts -> stack_anchored (E_main sp [a0; path] (in_envp inp) tid rnd) G.
Hypothesis Hvfs : valid_fs (in_fs inp).
Hypothesis Hsp47 : bv_unsigned sp <= 2 ^ 47.
Lemma run_from_QX_cf : forall cap0 L' A' b0 E ms md (K : dleaf * astate -> TSet),
user_blocks A' = [(b0, cap0)] -> 65536 <= cap0 <= 67108864 ->
WF A' -> bounded A' -> st_init_done A' = true ->
DI A' -> (exists b, res_ok A' b /\ RPinv (2 ^ 24) 12 cap0 b) ->
6 + config_len data <= dlen data -> dlen data < cap0 ->
run_env E data (ptr_addr L' b0) -> env_top E ->
st_ok src0segs E (if config_len data =? 0 then sQ0 else sQ1) ms ->
aa_MR API L' A' (ms_mem ms) md -> md_invX (in_fs inp) md ->
blk_data src0_msyms (ms_mem ms) (ptr_addr L' b0) data ->
jinv K (driver_tail data (RdLoaded b0 cap0) A') -> gtree mgrant (driver_tail data (RdLoaded b0 cap0) A') ->
leaves (run_RI RI (payload data)) (driver_tail data (RdLoaded b0 cap0) A') ->
(forall r, t_eq (K r) (leaf_shapeX data (in_fs inp) r)) ->
crealizes src0_msyms (mkCfg ms md) (tset (driver_tail data (RdLoaded b0 cap0) A') K).
Proof using AX GIL GI0 LIBXc FCF TBL RIii MRC LIMLAW FRM.
intros cap0 L' A' b0 E ms md K Hub Hcap0 HW HB Hid HDI HRES Hok HLc HE HT HS HMR Hmd HD HJ HG HL HK.
pose proof (config_len_bound data) as Hclb.
destruct (Z.eq_dec (payload_len data) 0) as [Hpl0 | Hplnz].
-
pose proof (res_of_tail_none (run_RI RI (payload data)) data b0 cap0 A' HL Hok Hpl0) as HRb. cbn [run_RI fst snd] in HRb.
rewrite (driver_tail_run_eq data b0 cap0 A') by (unfold HDR_MIN; lia).
change (tset (ret (DL_run b0 cap0 None) A') K) with (K (DL_run b0 cap0 None, A')).
apply (crz_conseq _ _ (leaf_shapeX data (in_fs inp) (DL_run b0 cap0 None, A')) _); [| apply t_eq_sym; apply HK].
destruct (Z.eqb_spec (config_len data) 0) as [Hz | Hz].
+ assert (Hc : calls data = 1%nat) by (unfold calls, cfg_byte; rewrite (proj2 (Z.eqb_eq _ _) Hz); reflexivity).
exact (src0_runX_0E1_cf API AX GI RI OUT GI0 LIBXc FCF TBL RIii FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok Hz Hc Hpl0 E ms _ HE HT HS HMR Hmd HRb).
+ pose proof (calls_bound data) as Hcb.
destruct (calls data) as [|[|[|[|[|n]]]]] eqn:Hc; try lia.
* exact (src0_runX_1E1_cf API AX GI RI OUT GI0 LIBXc FCF TBL RIii FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl0 E ms _ HE HT HS HMR Hmd HRb).
* exact (src0_runX_1E2_cf API AX GI RI OUT GIL GI0 LIBXc FCF TBL RIii FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl0 E ms _ HE HT HS HMR Hmd HRb).
* exact (src0_runX_1E3_cf API AX GI RI OUT GIL GI0 LIBXc FCF TBL RIii FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl0 E ms _ HE HT HS HMR Hmd HRb).
* exact (src0_runX_1E4_cf API AX GI RI OUT GIL GI0 LIBXc FCF TBL RIii FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl0 E ms _ HE HT HS HMR Hmd HRb).
-
assert (Hpl : 0 < payload_len data) by (unfold payload_len, HDR_MIN in *; lia).
pose proof HRES as (bR & HR & HRP).
assert (Hplc : payload_len data < cap0) by (unfold payload_len, HDR_MIN in *; lia).
pose proof (proj2 (exit_room A' bR cap0 (payload_len data) HW HR HRP ltac:(unfold MAX_INPUT; lia) ltac:(lia))) as Hroom.
pose proof (exit_none_slots A' bR b0 cap0 (payload_len data) HDI HR HRP Hub ltac:(unfold MAX_INPUT; lia) ltac:(lia)) as Hnone.
assert (Heq := driver_tail_loaded_eq data b0 cap0 A'
ltac:(apply Z.ltb_ge; unfold HDR_MIN; lia) ltac:(apply Z.ltb_ge; unfold HDR_MIN; lia) ltac:(apply Z.eqb_neq; exact Hplnz)).
rewrite (tset_bind_eq _ _ _ _ _ Heq).
pose proof (jinv_head_eq _ _ _ _ _ Heq HJ) as HJ'. pose proof (gtree_head_eq _ _ _ _ _ Heq HG) as HG'.
pose proof (res_of_tail_some (run_RI RI (payload data)) data b0 cap0 A' HL Hok Hplnz) as HRb.
assert (HRb' : forall tr q A2, cpath (malloc (payload_len data) A') tr (Some q, A2) -> RI (payload data) 0%nat [] A2)
by (intros tr q A2 Hp; exact (HRb tr (Some q, A2) Hp)).
assert (HK' : forall r : option sptr * astate,
t_eq (tset (let '(a, s') := r in payload_k b0 cap0 a s') K) (leaf_shapeX data (in_fs inp) (payload_leaf b0 cap0 r))).
{ intros [[q|] s']; cbn [payload_k payload_leaf fst snd]; apply HK. }
destruct (Z.eqb_spec (config_len data) 0) as [Hz | Hz].
+ assert (Hc : calls data = 1%nat) by (unfold calls, cfg_byte; rewrite (proj2 (Z.eqb_eq _ _) Hz); reflexivity).
exact (src0_runX_0M1_cf API AX GI RI OUT GI0 LIBXc FCF TBL RIii MRC LIMLAW FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl E ms _ HE HT HS HMR Hmd HD HRb' Hnone _ HJ' HG' Hroom HK').
+ pose proof (calls_bound data) as Hcb.
destruct (calls data) as [|[|[|[|[|n]]]]] eqn:Hc; try lia.
* exact (src0_runX_1M1_cf API AX GI RI OUT GI0 LIBXc FCF TBL RIii MRC LIMLAW FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl E ms _ HE HT HS HMR Hmd HD HRb' Hnone _ HJ' HG' Hroom HK').
* exact (src0_runX_1M2_cf API AX GI RI OUT GIL GI0 LIBXc FCF TBL RIii MRC LIMLAW FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl E ms _ HE HT HS HMR Hmd HD HRb' Hnone _ HJ' HG' Hroom HK').
* exact (src0_runX_1M3_cf API AX GI RI OUT GIL GI0 LIBXc FCF TBL RIii MRC LIMLAW FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl E ms _ HE HT HS HMR Hmd HD HRb' Hnone _ HJ' HG' Hroom HK').
* exact (src0_runX_1M4_cf API AX GI RI OUT GIL GI0 LIBXc FCF TBL RIii MRC LIMLAW FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl E ms _ HE HT HS HMR Hmd HD HRb' Hnone _ HJ' HG' Hroom HK').
Qed.
Lemma post_from_h1X_cf : forall cap0 L' A' b0 E ms md (K : dleaf * astate -> TSet),
user_blocks A' = [(b0, cap0)] -> 65536 <= cap0 <= 67108864 ->
WF A' -> bounded A' -> st_init_done A' = true ->
DI A' -> (exists b, res_ok A' b /\ RPinv (2 ^ 24) 12 cap0 b) ->
6 + config_len data <= dlen data -> dlen data < cap0 ->
hdr_env E data (ptr_addr L' b0) -> hdr_anch E -> env_top E ->
st_ok src0segs E ss_h1 ms -> aa_MR API L' A' (ms_mem ms) md -> md_invX (in_fs inp) md ->
blk_data src0_msyms (ms_mem ms) (ptr_addr L' b0) data ->
jinv K (driver_tail data (RdLoaded b0 cap0) A') -> gtree mgrant (driver_tail data (RdLoaded b0 cap0) A') ->
leaves (run_RI RI (payload data)) (driver_tail data (RdLoaded b0 cap0) A') ->
(forall r, t_eq (K r) (leaf_shapeX data (in_fs inp) r)) ->
crealizes src0_msyms (mkCfg ms md) (tset (driver_tail data (RdLoaded b0 cap0) A') K).
Proof using AX GIL GI0 LIBXc FCF TBL RIii MRC LIMLAW FRM.
intros cap0 L' A' b0 E ms md K Hub Hcap0 HW HB Hid HDI HRES Hok HLc HE HAN HT HS HMR Hmd HD HJ HG HL HK.
assert (Hin : In (b0, cap0) (user_blocks A')) by (rewrite Hub; left; reflexivity).
pose proof (mr_blocks _ _ (aa_laws API) L' A' (ms_mem ms) md b0 cap0 0 HMR Hin ltac:(lia)) as (_ & Hq1 & Hq2 & _).
assert (Hac : alloc_ceiling < 2 ^ 47) by (pose proof YM05.alloc_ceiling_val; lia).
pose proof (config_len_bound data) as Hclb.
apply (src0_to_P_cf API AX data cap0 L' A' b0 E md Hub Hcap0 HE HAN ms _ Hok HLc HS HMR HD).
intros ms3 HS3 HMR3 HD3. clear HS HMR HD.
destruct HE as (HEd & HE13 & HE26).
assert (HRE : run_env (E_P E data (ptr_addr L' b0 + 2 + config_len data)) data (ptr_addr L' b0)).
{ unfold run_env. split; [| split; [| split; [| split]]].
- rewrite E_P_ed by lia. exact HEd.
- rewrite E_P_old by lia. exact HE13.
- rewrite E_P_old by lia. exact HE26.
- apply E_P_46. lia.
- apply (hdr_anch_ext E _ HAN). intros n Hn. apply E_P_old. lia. }
assert (HTE : env_top (E_P E data (ptr_addr L' b0 + 2 + config_len data))) by (unfold env_top; rewrite E_P_old by lia; exact HT).
apply (src0_P_to_QX_cf API AX data cap0 L' A' b0 md Hub Hok HLc _ ms3 _ HRE HS3 HMR3 HD3).
intros ms4 HS4 HMR4 HD4. clear HS3 HMR3 HD3.
exact (run_from_QX_cf cap0 L' A' b0 _ ms4 md K Hub Hcap0 HW HB Hid HDI HRES Hok HLc HRE HTE HS4 HMR4 Hmd HD4 HJ HG HL HK).
Qed.
Lemma post_from_h0X_cf : forall cap0 L' A' b0 E ms md (K : dleaf * astate -> TSet),
user_blocks A' = [(b0, cap0)] -> 65536 <= cap0 <= 67108864 ->
WF A' -> bounded A' -> st_init_done A' = true ->
DI A' -> (exists b, res_ok A' b /\ RPinv (2 ^ 24) 12 cap0 b) ->
dlen data < cap0 ->
hdr_env E data (ptr_addr L' b0) -> hdr_anch E -> env_top E ->
st_ok src0segs E ss_h0 ms -> aa_MR API L' A' (ms_mem ms) md -> md_invX (in_fs inp) md ->
blk_data src0_msyms (ms_mem ms) (ptr_addr L' b0) data ->
jinv K (driver_tail data (RdLoaded b0 cap0) A') -> gtree mgrant (driver_tail data (RdLoaded b0 cap0) A') ->
leaves (run_RI RI (payload data)) (driver_tail data (RdLoaded b0 cap0) A') ->
(forall r, t_eq (K r) (leaf_shapeX data (in_fs inp) r)) ->
crealizes src0_msyms (mkCfg ms md) (tset (driver_tail data (RdLoaded b0 cap0) A') K).
Proof using AX GIL GI0 LIBXc FCF TBL RIii MRC LIMLAW FRM.
intros cap0 L' A' b0 E ms md K Hub Hcap0 HW HB Hid HDI HRES HLc HE HAN HT HS HMR Hmd0 HD HJ HG HL HK.
pose proof (md_invX_inv _ _ Hmd0 : md_ok inp md) as Hmd.
pose proof (config_len_bound data) as Hclb.
pose proof HRES as (bR & HR & HRP).
pose proof (exit_slots A' bR b0 cap0 HDI HR HRP Hub ltac:(unfold MAX_INPUT; lia)) as Hslots.
assert (Hnn : 0 <= dlen data) by (unfold dlen; lia).
destruct (Z_lt_le_dec (dlen data) 6) as [Hshort | Hhdr].
-
rewrite (driver_tail_short_eq data b0 cap0 A') by (unfold HDR_MIN; exact Hshort).
change (tset (ret DL_short A') K) with (K (DL_short, A')).
apply (crz_conseq _ _ (leaf_shapeX data (in_fs inp) (DL_short, A')) _); [| apply t_eq_sym; apply HK].
cbn [leaf_shapeX leaf_shape fst].
exact (src0_short_tail_cf API AX FCF TBL inp data cap0 L' A' b0 Hub Hcap0 HW HB Hid E ms md HE HAN ltac:(lia) HS HMR Hslots Hmd).
-
apply (src0_to_h1_cf API AX data cap0 L' A' b0 Hub Hcap0 HLc E ms md _ HE HAN Hhdr HS HMR HD).
intros ms2 HS2 HMR2 HD2. clear HS HMR HD.
destruct (Z_lt_le_dec (dlen data) (6 + config_len data)) as [Hov | Hok].
+
rewrite (driver_tail_overrun_eq data b0 cap0 A') by (unfold HDR_MIN; lia).
change (tset (ret DL_overrun A') K) with (K (DL_overrun, A')).
apply (crz_conseq _ _ (leaf_shapeX data (in_fs inp) (DL_overrun, A')) _); [| apply t_eq_sym; apply HK].
cbn [leaf_shapeX leaf_shape fst].
exact (src0_overrun_tail_cf API AX FCF TBL inp data cap0 L' A' b0 Hub Hcap0 HW HB Hid E ms2 md HE HAN Hhdr Hov HS2 HMR2 Hslots Hmd).
+ exact (post_from_h1X_cf cap0 L' A' b0 E ms2 md K Hub Hcap0 HW HB Hid HDI HRES Hok HLc HE HAN HT HS2 HMR2 Hmd0 HD2 HJ HG HL HK).
Qed.
Theorem src0_postX_cf : forall K : dleaf * astate -> TSet,
(forall r, t_eq (K r) (leaf_shapeX data (in_fs inp) r)) ->
POST_cf API sp tid a0 path inp data rnd (run_RI RI (payload data)) K.
Proof using AX GIL GI0 LIBXc FCF TBL RIii MRC LIMLAW FRM HSA0 Hvfs Hsp47.
intros K HK. unfold POST_cf. cbv zeta beta.
intros cap' bufp' A' Lc' J' g' len0 w ms' md' HLc Hcap Hlen0 Hub HW HB Hid HDI HRES HS Hw HL0 HMR Hmd0 HD HJ HG HL.
pose proof (md_invX_of_post inp md' Hvfs Hmd0) as Hmd.
unfold MAX_INPUT in Hcap. subst len0.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hlz & _).
assert (Hin : In (bufp', cap') (user_blocks A')) by (rewrite Hub; left; reflexivity).
pose proof (mr_blocks _ _ (aa_laws API) Lc' A' (ms_mem ms') md' bufp' cap' 0 HMR Hin ltac:(lia)) as (_ & Hq1 & Hq2 & _).
assert (Hac : alloc_ceiling < 2 ^ 47) by (pose proof YM05.alloc_ceiling_val; lia).
lazymatch type of HS with st_ok _ ?E0 _ _ => set (E := E0) in HS end.
assert (HE : hdr_env E data (ptr_addr Lc' bufp')).
{ subst E. unfold hdr_env. split; [| split].
- rewrite ed_ewset. apply ed_lp2.
- rewrite ew_ewset_other by lia. unfold E_lp. rewrite ew_ewset_other, ew_ewset_other, ew_ewset_other, ew_ewset_same by lia.
apply u64_of_Z. lia.
- rewrite ew_ewset_other by lia. unfold E_lp. rewrite ew_ewset_other, ew_ewset_same by lia.
apply u64_of_Z. unfold dlen in HLc. lia. }
assert (HAN : hdr_anch E).
{ intros G HGa. subst E. apply (anch_lp sp tid a0 path inp data rnd HSA0 J' (ptr_addr Lc' bufp') g' (Z.of_nat (length data)) cap' _ G); [| exact HGa].
apply (ext29_ewset data); [lia | apply ext29_refl]. }
cdrv_run_with src0tbl_ok HS HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E ss_h0 msx) in HS end.
lazymatch type of HF with frame_of _ ?rs0 ?m0 ?m1 =>
pose proof (blk_data_after_frame src0_msyms (aa_MR API) (aa_laws API) AX Lc' A' m0 m1 _ E (ss_facts ss_h0) src0_keep rs0 bufp' cap' (ptr_addr Lc' bufp') data HMR
ltac:(destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & HG0); exact HG0) ltac:(drv_anch) ltac:(vm_compute; reflexivity) HF Hin ltac:(lia) ltac:(unfold dlen in HLc; lia)) as HD';
specialize (HD' HD); clear HD; rename HD' into HD end.
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep E HS HF HMR.
lazymatch type of HS with st_ok _ _ _ ?msx =>
assert (HT : env_top E) by (subst E; unfold env_top; rewrite ew_ewset_other by lia; rewrite ew_lp; cbn; exact Hsp47);
exact (post_from_h0X_cf cap' Lc' A' bufp' E msx md' K Hub ltac:(lia) HW HB Hid HDI HRES HLc HE HAN HT HS HMR Hmd HD HJ HG HL HK) end.
Qed.
End c.
End b.
