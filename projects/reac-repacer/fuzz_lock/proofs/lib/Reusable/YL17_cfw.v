(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from lib/Reusable/YL17.v. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/libreac/fuzz_scene/lib/Reusable/YL17_cfw.v, with its module paths changed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YK11 YK0o YK0h YK0i YK14 YK1b YK1a YK15 YK0k YK0n YK0p YP0n YM06 YM02.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YO0i YO0f YO0x YO0d YO0e YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO06.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YH00 YH01 YH03 YH02 YN3e YN35 YN3f YN3g YN34 YN3d.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YN03 YL07 YL01 YL08 YL0d YL0e YL02 YL0a YL00 YL04 YL0c YL09 YL05 YL0g YL0k YL0m YL0u YL0r YL0o YL0s.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YI06 YI16 YI14 YI5b YI5c YL0i YL06 YL03 YL0l YL0t GIWalk.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YI04 YM0b YO0d_cf YO04_cfw.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YL17 YK15_cfw YP03_cfw YN35_cfw YN3d_cfw YL0i_cfw YL06_cfw YL0d_cfw YL0k_cfw YL0o_cfw YL0d2_cfw YN34b_cfw.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib Require Import Contract SlotAgree.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Section d.
Variable API : AllocAPI src0_msyms.
Hypothesis AX : AllocExtra src0_msyms (aa_MR API).
Variable GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop.
Variable RI : list byte -> nat -> list (Z * Z) -> astate -> Prop.
Variable OUT : list byte -> list byte.
Hypothesis GIL : G_local_T src0segs src0_G GI.
Hypothesis GI0 : forall mem, G_img src0segs src0_G mem -> GI 0%nat [] mem.
Hypothesis LIBXc : lib_contract_x_Rc_all src0_msyms API RI src0_G src0_R GI OUT LIBPC RA_LIB EMPTY LIB_STACK.
Hypothesis FCF : forall fx' : FPState, @free_contract_cf fx' rc src0_msyms API.
Hypothesis TBL : forall L A mem md, aa_MR API L A mem md -> forall a, static_owned src0_msyms a -> 0 <= a < 2 ^ 64 ->
Mem.ro_addr src0segs (Z_to_bv 64 a) = true -> mbyte src0segs mem a = seg_rom src0segs (Z_to_bv 64 a).
Hypothesis RIres : forall pl j T A, RI pl j T A -> exists b, res_ok_slots A b.
Hypothesis MRC : forall fx' : FPState, @malloc_realizes_cf fx' rc src0_msyms (aa_MR API).
Hypothesis LIMLAW : forall L A mem md, aa_MR API L A mem md -> SRC_LIM_MIN <= vm_limit (m_vmmaps md).
Hypothesis FRM : frm_zero fp_csr.
Variables (data : list byte) (fs : Fs) (cap0 : Z) (L' : layout) (A' : astate) (b0 : sptr).
Hypothesis Hub : user_blocks A' = [(b0, cap0)].
Hypothesis Hcap0 : 65536 <= cap0 <= 67108864.
Hypothesis HW : WF A'.
Hypothesis HB : bounded A'.
Hypothesis Hid : st_init_done A' = true.
Hypothesis Hok : 6 + config_len data <= dlen data.
Hypothesis HLc : dlen data < cap0.
Hypothesis Hcl : config_len data <> 0.
Hypothesis Hcalls : calls data = 2%nat.
Hypothesis Hpl : 0 < payload_len data.
Let lib_stk_pos : 0 <= LIB_STACK := ltac:(unfold LIB_STACK; lia).
Ltac cto_free_buf HS HMR Hcm Hed :=
let HF := fresh "HF" in
first
[ sym_assume_with src0tbl_ok HS true;
[ lazymatch type of HS with st_ok _ ?E _ _ =>
change (sv_denot E (SLit 0)) with (Z_to_bv 64 0); etransitivity; [apply (bltz_b1s E data); [exact Hed | unfold dlen in *; lia] | exact Hcm] end
| ]
| sym_assume_with src0tbl_ok HS false;
[ lazymatch type of HS with st_ok _ ?E _ _ =>
change (sv_denot E (SLit 0)) with (Z_to_bv 64 0); etransitivity; [apply (bltz_b1s E data); [exact Hed | unfold dlen in *; lia] | exact Hcm] end
| ] ];
cdrv_run_to_with src0tbl_ok HS src0_A_free HF;
lazymatch type of HS with st_ok _ ?E _ _ =>
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep E HS HF HMR end.
Theorem src0_runX_1M2_cf : forall E ms md,
run_env E data (ptr_addr L' b0) -> env_top E ->
st_ok src0segs E sQ1 ms -> aa_MR API L' A' (ms_mem ms) md -> md_invX fs md ->
blk_data src0_msyms (ms_mem ms) (ptr_addr L' b0) data ->
(forall tr q A2, cpath (malloc (payload_len data) A') tr (Some q, A2) -> RI (payload data) 0%nat [] A2) ->
(forall tr A2, cpath (malloc (payload_len data) A') tr (None, A2) -> exists b, res_ok_slots A2 b) ->
forall K : option sptr * astate -> TSet,
jinv K (malloc (payload_len data) A') -> gtree mgrant (malloc (payload_len data) A') ->
roomcf SRC_LIM_MIN (malloc (payload_len data) A') ->
(forall r, t_eq (K r) (leaf_shapeX data fs (payload_leaf b0 cap0 r))) ->
crealizes src0_msyms (mkCfg ms md) (tset (malloc (payload_len data) A') K).
Proof using AX FCF FRM GI0 HB HLc HW Hcalls Hcap0 Hcl Hid Hok Hpl Hub LIBXc LIMLAW MRC RIres TBL GIL.
intros E ms md HE HT HS HMR Hmd HD HRb HRn K HJ HG HRM HK.
pose proof (payload_len_length data Hok) as HplLen.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hlz & _).
assert (Hin : In (b0, cap0) (user_blocks A')) by (rewrite Hub; left; reflexivity).
pose proof (mr_blocks _ _ (aa_laws API) L' A' (ms_mem ms) md b0 cap0 0 HMR Hin ltac:(lia)) as (_ & Hq1 & Hq2 & _).
assert (Hac : alloc_ceiling < 2 ^ 63) by (pose proof YM05.alloc_ceiling_val; lia).
unfold dlen in Hok, HLc. pose proof (config_len_bound data) as Hclb.
destruct (list_len2 data ltac:(lia)) as (d0 & d1 & rest & Ed).
assert (Hplv : payload_len data = Z.of_nat (length data) - 6 - config_len data) by reflexivity.
pose proof HE as HE0. destruct HE0 as (HEd & HE13 & HE26 & HE46 & HAN).
apply (src0_Q_calls data cap0 L' b0 Hcap0 Hok HLc E ms HE Hcl) in HS. rewrite Hcalls in HS. change (st_ok src0segs E r1M2_Q ms) in HS.
let v := eval cbv [sv_pl00 sv_pl add0 sv_cl sv_b1s] in sv_pl00 in
assert (Hpl00 : U E v = payload_len data) by (eapply U_pl00; eauto; lia).
apply (st_ok_add_cond src0segs E r1M2_Q ms BC_NE (ltac:(let v := eval cbv [sv_pl00 sv_pl add0 sv_cl sv_b1s] in sv_pl00 in exact v)) (SLit 0)) in HS.
2:{ rewrite branch_ne_U, Hpl00, U_SLit. change (zcanon 0) with 0. apply Bool.negb_true_iff. apply Z.eqb_neq. lia. }
cdrv_run_to_with src0tbl_ok HS src0_A_malloc HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E r1M2_ME msx) in HS end.
drv_bd AX src0_keep E HS HF HMR HD Hin.
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep E HS HF HMR.
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS) as Hr10. rewrite (proj1 (proj2 r1M2_ME_facts)) in Hr10.
rewrite (denot_lit_U E (add0 sv_pl00)), U_add0 in Hr10. cbv [sv_pl00 sv_pl add0 sv_cl sv_b1s] in Hr10. rewrite Hpl00 in Hr10.
eapply (malloc_site_cf src0_msyms API AX (MRC _) LIMLAW E r1M2_ME _ md L' A' (payload_len data) (-208) src0_keep [] 48 r1M2_LME r1M2_RSME RA_ME K
HS ltac:(drv_anch) r1M2_site_ME r1M2_statics_ME HMR HW HB);
[ intros Hf; rewrite Hid in Hf; discriminate
| exact Hr10
| lia
| intros kb sz [ ]
| exact HJ | exact HG | exact HRM | ].
clear Hr10.
intros res A2 L2 mS2 mD2 g2 tr HS2 ?HSA HMR2 HW2 HB2 Hmd2 Hpath Hstab Hhi Hbk Hres.
apply (md_invX_ex _ _ _ Hmd) in Hmd2.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR2) as (Hh2 & Hlz2 & _).
assert (Hid2 : st_init_done A2 = true) by (exact (malloc_keeps_init_done _ _ _ _ _ Hid (cpath_yields _ _ _ Hpath))).
destruct (Hstab _ _ Hin) as [Hin2 Hpb2].
lazymatch type of HS2 with st_ok _ _ _ ?msx => change (st_ok src0segs (post_env E 48 (ms_regs mS2) g2) r1M2_MEp msx) in HS2 end.
assert (HE2 : run_env (post_env E 48 (ms_regs mS2) g2) data (ptr_addr L' b0)) by (apply run_env_post; [lia | exact HE]).
assert (HT2 : env_top (post_env E 48 (ms_regs mS2) g2)) by (apply env_top_post; [lia | exact HT]). clear HT. rename HT2 into HT.
assert (HD2 : blk_data src0_msyms (ms_mem mS2) (ptr_addr L' b0) data).
{ eapply (blk_data_kept src0_msyms); [|exact HD]. intros i Hi. apply (Hbk b0 cap0 i Hin); unfold dlen in *; lia. }
clear HD. clear HS HMR Hhi Hbk. rename HS2 into HS. rename HMR2 into HMR.
destruct res as [q|].
+
pose proof (HRb _ _ _ Hpath) as HRbL.
destruct Hres as (Hq0 & Hqnz & b1 & b2 & HubA2 & HubA1).
assert (Hinq : In (q, payload_len data) (user_blocks A2)) by (rewrite HubA2; apply in_app_iff; right; left; reflexivity).
pose proof (mr_blocks _ _ (aa_laws API) L2 A2 (ms_mem mS2) mD2 q (payload_len data) 0 HMR Hinq ltac:(lia)) as (_ & Hq3 & Hq4 & _).
assert (Hqb : q <> b0).
{ intros ->. pose proof (YL0s.blocks_same_ptr _ _ (aa_laws API) _ _ _ _ _ _ _ _ HMR Hinq Hin2 ltac:(lia) ltac:(lia) eq_refl). lia. }
assert (Hqba : ptr_addr L2 q <> ptr_addr L' b0).
{ rewrite <- Hpb2. exact (blocks_distinct_addr _ _ (aa_laws API) _ _ _ _ _ _ _ _ HMR Hinq Hin2 ltac:(lia) ltac:(lia) Hqb). }
apply (crz_conseq _ _ (LIBK (payload data) (m_fs mD2) (fun l => wr ch_stdout line0 (lib_iter (payload data) 1 (run_tail 1) (ll_fs l)))) _).
2:{ eapply t_eq_trans; [| apply t_eq_sym; apply HK]. unfold payload_leaf; cbn [fst snd leaf_shapeX run_shape]. rewrite Hcalls. rewrite (md_invX_fs _ _ Hmd2). apply t_eq_refl. }
assert (H32 : bv_unsigned (ew (post_env E 48 (ms_regs mS2) g2) 52) = ptr_addr L2 q).
{ change 52%nat with (48 + 4)%nat. rewrite post_env_a0, Hq0, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
apply (st_ok_add_fact src0segs _ r1M2_MEp mS2 52 blkq_fact) in HS.
2:{ unfold afact_ok, blkq_fact. cbn [af_lo af_hi af_al2]. rewrite H32. change (2 ^ 4) with 16.
pose proof (mr_blocks_aligned _ _ (aa_laws API) L2 A2 (ms_mem mS2) mD2 q _ HMR Hinq). pose proof YM05.alloc_ceiling_val. lia. }
assert (HRE : renv (post_env E 48 (ms_regs mS2) g2) data (ptr_addr L' b0) (ptr_addr L2 q)) by (split; [exact HE2 | exact H32]).
clear HE2 H32.
cdrv_run_to_with src0tbl_ok HS src0_A_memcpy HF.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M2_MC msx) in HS;
drv_bd AX src0_keep Ec HS HF HMR HD2 Hin2;
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep Ec HS HF HMR end.
lazymatch type of HS with st_ok _ ?Ec _ ?msx =>
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS) as Hr10; pose proof (st_ok_reg src0segs _ _ _ 11%bv HS) as Hr11; pose proof (st_ok_reg src0segs _ _ _ 12%bv HS) as Hr12;
rewrite (proj1 r1M2_MC_facts) in Hr10; rewrite (proj1 (proj2 r1M2_MC_facts)) in Hr11; rewrite (proj2 (proj2 r1M2_MC_facts)) in Hr12;
eapply (src0_memcpy_site_cf API AX Ec r1M2_MC msx mD2 L2 A2 q (payload_len data) (payload_len data) b0 cap0 (ptr_addr L' b0 + 6 + config_len data) 52 65 RA_MC _
HS ltac:(drv_anch) r1M2_ck_MC HMR Hinq Hin2 Hqb);
[ rewrite Hr10; cbn [sv_denot]; rewrite Z.add_0_r, <- (proj2 HRE), Z_to_bv_bv_unsigned; reflexivity
| rewrite Hr11; cbn [sv_denot]; rewrite (denot_lit_U Ec (SOff 47 4)) || idtac;
apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64);
rewrite (proj1 (proj2 (proj2 (proj2 (proj1 HRE))))); rewrite !Z.mod_small by lia; lia
| rewrite Hpb2; lia
| rewrite Hpb2; lia
| rewrite Hr12, (denot_lit_U Ec (add0 sv_pl00)), U_add0; rewrite (U_pl00 Ec data d0 d1 rest); [reflexivity | exact (proj1 (proj1 HRE)) | exact Ed | exact (proj1 (proj2 (proj2 (proj1 HRE)))) | lia]
| lia
| lia
| clear Hr10 Hr11 Hr12 ]
end.
intros mS3 HS3 HMR3 Hout3 Hbd3.
assert (HDq : blk_data src0_msyms (ms_mem mS3) (ptr_addr L2 q) (payload data)).
{ apply Hbd3; [|exact (eq_sym HplLen)].
unfold payload.
replace (skipn (Z.to_nat (HDR_MIN + config_len data)) data) with (firstn (Z.to_nat (payload_len data)) (skipn (Z.to_nat (6 + config_len data)) data)).
2:{ unfold HDR_MIN. rewrite firstn_all2; [reflexivity|]. rewrite length_skipn. unfold payload_len, HDR_MIN, dlen in *. lia. }
replace (ptr_addr L' b0 + 6 + config_len data) with (ptr_addr L' b0 + Z.of_nat (Z.to_nat (6 + config_len data))) by lia.
apply (blk_data_sub src0_msyms); [exact HD2|]. unfold payload_len, dlen in *. lia. }
clear HS HMR Hbd3. rename HS3 into HS. rename HMR3 into HMR.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M2_MCp msx) in HS end.
renv_sync HS HRE. etop_sync HS HT.
cdrv_run_to_with src0tbl_ok HS LIBPC HF.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M2_L1 msx) in HS;
drv_bd AX src0_keep Ec HS HF HMR HDq Hinq;
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep Ec HS HF HMR end.
lazymatch type of HS with st_ok _ ?Ec _ ?msx =>
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS) as Hr10; pose proof (st_ok_reg src0segs _ _ _ 11%bv HS) as Hr11;
rewrite (proj1 r1M2_L1_facts) in Hr10; rewrite (proj1 (proj2 r1M2_L1_facts)) in Hr11;
try rewrite <- (md_invX_fs _ _ Hmd2);
assert (CK1 : env_check (ss_mem r1M2_L1) = true) by (vm_compute; reflexivity);
eapply (lib_site_x_R_cf src0_msyms API AX LIBPC RA_LIB EMPTY LIB_STACK src0_G src0_R GI RI OUT LIBXc lib_stk_pos FRM 0%nat [] Ec r1M2_L1 msx mD2 L2 A2
(ptr_addr L2 q) (payload_len data) (payload data) (-208) src0_keepG [] 76 r1M2_LL1 r1M2_RSL1 _
ltac:(lia) HS ltac:(drv_anch) r1M2_site_L1 ltac:(vm_compute; reflexivity) r1M2_statics_L1 HMR HW2 HB2 Hid2
(GI0 _ (st_ok_G_img src0segs _ _ _ src0_G HS ltac:(vm_compute; reflexivity))) (tb_live_nil L2 A2) (fun _ => notin_nil _)
(st_ok_G_img src0segs _ _ _ src0_R HS ltac:(vm_compute; reflexivity)) (proj1 (proj2 (md_invX_inv _ _ Hmd2))));
[ rewrite Hr10; cbn [sv_denot]; rewrite Z.add_0_r, <- (proj2 HRE), Z_to_bv_bv_unsigned; reflexivity
| rewrite Hr11; rewrite (denot_lit_U Ec (add0 sv_pl00)), U_add0, (U_pl00 Ec data d0 d1 rest); [reflexivity | exact (proj1 (proj1 HRE)) | exact Ed | exact (proj1 (proj2 (proj2 (proj1 HRE)))) | lia]
| right; split; [lia | exists q; split; [exact Hinq | reflexivity]]
| intros kb sz [ ]
| exact HplLen
| exact HDq
| exact HRbL
| split; [|split]; [ exact (proj1 (src0_env_rom _ (env_of_st_ok src0segs _ _ _ HS CK1)))
| exact (proj2 (src0_env_rom _ (env_of_st_ok src0segs _ _ _ HS CK1)))
| exact (md_invX_names _ _ Hmd2) ]
| exact (md_invX_free _ _ Hmd2)
| exact (md_invX_sorted _ _ Hmd2)
| unfold env_top in HT; lia
| clear Hr10 Hr11 CK1 ]
end.
intros l4 fx4 A3 L3 mS4 mD4 g4 T1 HS' ?HSA FRM' HMR' HW4 HB4 Hid4 Hmd4 Hstab4 Hhi4 Hbk4 Hret4 Hout4 Hsort4 HSN4 HRES4 Hplk4 HTL1 HTT1 HGI1. cbv beta. cbn [lib_iter run_tail].
destruct (RIres _ _ _ _ HRES4) as (b4 & Hb4).
pose proof (md_invX_lib _ _ _ _ _ Hmd2 Hmd4 HSN4 Hsort4) as HmdX4. clear Hmd4. rename HmdX4 into Hmd4.
assert (HDq4 : blk_data src0_msyms (ms_mem mS4) (ptr_addr L2 q) (payload data)).
{ eapply (blk_data_kept src0_msyms); [|exact HDq]. intros ii Hii. apply Hplk4. rewrite HplLen. exact Hii. }
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (Hh4 & Hlz4 & _).
destruct (Hstab4 _ _ Hin2 (notin_nil _)) as (bq4 & Hin4 & Hpb4).
pose proof (kept_notin _ _ _ _ _ _ _ Hin2 Hpb2 (notin_nil _) HTT1) as HbT1. try rewrite Hpb2 in Hpb4.
destruct (Hstab4 _ _ Hinq (notin_nil _)) as (pq4 & Hinq4 & Hpq4).
pose proof (kept_notin _ _ _ _ _ _ _ Hinq (eq_refl (ptr_addr L2 q)) (notin_nil _) HTT1) as HqT1.
clear HS HMR Hhi4 Hbk4 Hstab4. rename HS' into HS. rename HMR' into HMR. clear FRM; try clear fx. rename FRM' into FRM.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M2_P1 msx) in HS end.
renv_sync HS HRE. etop_sync HS HT.
pose proof (md_invX_ch1 _ _ Hmd4) as Hch4.
unfold wr at 1.
cdrv_printf0 HS Hch4 93%nat RET_PF HF.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M2_I1 msx) in HS;
drv_bd AX src0_keep Ec HS HF HMR HDq4 Hinq4;
drv_gi_T (GI_frame_T src0_msyms (aa_MR API) (aa_laws API) AX src0_G GI GIL src0_keep) Ec HS HF HGI1 HTL1 HMR;
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep Ec HS HF HMR end.
renv_sync HS HRE. etop_sync HS HT.
cdrv_run_to_with src0tbl_ok HS LIBPC HF.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M2_L2 msx) in HS;
drv_bd AX src0_keep Ec HS HF HMR HDq4 Hinq4;
drv_gi_T (GI_frame_T src0_msyms (aa_MR API) (aa_laws API) AX src0_G GI GIL src0_keep) Ec HS HF HGI1 HTL1 HMR;
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep Ec HS HF HMR end.
lazymatch type of HS with st_ok _ ?Ec _ ?msx =>
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS) as Hr10; pose proof (st_ok_reg src0segs _ _ _ 11%bv HS) as Hr11;
rewrite (proj1 r1M2_L2_facts) in Hr10; rewrite (proj1 (proj2 r1M2_L2_facts)) in Hr11;
try rewrite <- (md_invX_fs _ _ Hmd4);
assert (CK2 : env_check (ss_mem r1M2_L2) = true) by (vm_compute; reflexivity);
eapply (lib_site_x_R_cf src0_msyms API AX LIBPC RA_LIB EMPTY LIB_STACK src0_G src0_R GI RI OUT LIBXc lib_stk_pos FRM 1%nat T1 Ec r1M2_L2 msx mD4 L3 A3
(ptr_addr L2 q) (payload_len data) (payload data) (-208) src0_keepG [] 104 r1M2_LL2 r1M2_RSL2 _
ltac:(lia) HS ltac:(drv_anch) r1M2_site_L2 ltac:(vm_compute; reflexivity) r1M2_statics_L2 HMR HW4 HB4 Hid4 HGI1 HTL1 (fun _ => HqT1)
(st_ok_G_img src0segs _ _ _ src0_R HS ltac:(vm_compute; reflexivity)) (proj1 (proj2 (md_invX_inv _ _ Hmd4))));
[ rewrite Hr10; cbn [sv_denot]; rewrite Z.add_0_r, <- (proj2 HRE), Z_to_bv_bv_unsigned; reflexivity
| rewrite Hr11; rewrite (denot_lit_U Ec (add0 sv_pl00)), U_add0, (U_pl00 Ec data d0 d1 rest); [reflexivity | exact (proj1 (proj1 HRE)) | exact Ed | exact (proj1 (proj2 (proj2 (proj1 HRE)))) | lia]
| right; split; [lia | exists pq4; split; [exact Hinq4 | exact Hpq4]]
| intros kb sz [ ]
| exact HplLen
| exact HDq4
| exact HRES4
| split; [|split]; [ exact (proj1 (src0_env_rom _ (env_of_st_ok src0segs _ _ _ HS CK2)))
| exact (proj2 (src0_env_rom _ (env_of_st_ok src0segs _ _ _ HS CK2)))
| exact (md_invX_names _ _ Hmd4) ]
| exact (md_invX_free _ _ Hmd4)
| exact (md_invX_sorted _ _ Hmd4)
| unfold env_top in HT; lia
| clear Hr10 Hr11 CK2 ]
end.
intros l5 fx5 A4 L4 mS5 mD5 g5 T2 HS' ?HSA FRM' HMR' HW5 HB5 Hid5 Hmd5 Hstab5 Hhi5 Hbk5 Hret5 Hout5 Hsort5 HSN5 HRES5 Hplk5 HTL2 HTT2 HGI2. cbv beta. cbn [lib_iter run_tail].
destruct (RIres _ _ _ _ HRES5) as (b5 & Hb5).
pose proof (md_invX_lib _ _ _ _ _ Hmd4 Hmd5 HSN5 Hsort5) as HmdX5. clear Hmd5. rename HmdX5 into Hmd5.
assert (HDq5 : blk_data src0_msyms (ms_mem mS5) (ptr_addr L2 q) (payload data)).
{ eapply (blk_data_kept src0_msyms); [|exact HDq4]. intros ii Hii. apply Hplk5. rewrite HplLen. exact Hii. }
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (Hh5 & Hlz5 & _).
destruct (Hstab5 _ _ Hin4 ltac:(rewrite Hpb4; exact HbT1)) as (bq5 & Hin5 & Hpb5). try rewrite Hpb4 in Hpb5.
destruct (Hstab5 _ _ Hinq4 ltac:(rewrite Hpq4; exact HqT1)) as (pq5 & Hinq5 & Hpq5). rewrite Hpq4 in Hpq5.
clear HS HMR Hhi5 Hbk5 Hstab5. rename HS' into HS. rename HMR' into HMR. clear FRM; try clear fx4. rename FRM' into FRM.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M2_P2 msx) in HS end.
renv_sync HS HRE. etop_sync HS HT.
cdrv_run_to_with src0tbl_ok HS src0_A_free HF.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M2_F msx) in HS;
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep Ec HS HF HMR end.
lazymatch type of HS with st_ok _ ?Ec _ ?msx =>
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS) as Hr10; rewrite r1M2_F_facts in Hr10;
eapply (free_site_cf src0_msyms API AX TBL (FCF _) Ec r1M2_F msx mD5 L4 A4 pq5 (payload_len data) b5 (-208) src0_keep [] 132 r1M2_LF r1M2_RSF RA_FQ _
HS ltac:(drv_anch) r1M2_site_F ltac:(vm_compute; reflexivity) r1M2_statics_F HMR HW5 HB5 Hid5 Hinq5);
[ rewrite Hr10; cbn [sv_denot]; rewrite Z.add_0_r, Hpq5, <- (proj2 HRE), Z_to_bv_bv_unsigned; reflexivity
| exact Hb5
| intros kb sz [ ]
| clear Hr10 ]
end.
intros A6 L6 mS6 mD6 g6 HS' ?HSA HMR' HW6 HB6 Hmd6 Hstab6 Hhi6 Hbk6 Hb6.
apply (md_invX_ex _ _ _ Hmd5) in Hmd6.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (Hh6 & Hlz6 & _).
destruct (Hstab6 _ _ Hin5 ltac:(intros HH; apply Hqba; rewrite <- Hpq5, <- Hpb5, HH; reflexivity)) as [Hin6 Hpb6]. try rewrite Hpb5 in Hpb6.
assert (Hid6 : st_init_done A6 = true) by (exact (init_done_of_block A6 _ HW6 Hin6)).
clear HS HMR Hhi6 Hbk6 Hstab6. rename HS' into HS. rename HMR' into HMR.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M2_Fp msx) in HS end.
renv_sync HS HRE. etop_sync HS HT.
cdrv_run_with src0tbl_ok HS HF.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M2_N1 msx) in HS;
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep Ec HS HF HMR end.
unfold ex.
destruct (count_mode data) eqn:Hcm.
* cto_free_buf HS HMR Hcm (proj1 (proj1 HRE)).
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M2_N1t msx) in HS end.
lazymatch type of HS with st_ok _ ?Ec _ ?msx =>
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS) as Hr10;
eapply (free_site_cf src0_msyms API AX TBL (FCF _) Ec r1M2_N1t msx mD6 L6 A6 bq5 cap0 _ (-128) src0_keep [] 149 r1M2_LN1t r1M2_RSN1t RA_sf _
HS ltac:(drv_anch) r1M2_site_N1t ltac:(vm_compute; reflexivity) r1M2_statics_N1t HMR HW6 HB6 Hid6 Hin6);
[ rewrite Hr10; match goal with |- sv_denot _ ?x = _ => replace x with (SOff 14 0) by (symmetry; first [exact (proj1 r1M2_N_facts) | exact (proj1 (proj2 r1M2_N_facts)) | exact (proj1 (proj2 (proj2 r1M2_N_facts))) | exact (proj2 (proj2 (proj2 r1M2_N_facts)))]) end;
cbn [sv_denot]; rewrite Z.add_0_r, Hpb6, <- (proj1 (proj2 (proj1 HRE))), Z_to_bv_bv_unsigned; reflexivity
| exact Hb6
| intros kb sz [ ]
| clear Hr10 ]
end.
intros AN1t LN1t mSN1t mDN1t gN1t HS' ?HSA HMR' HWN1t HBN1t HmdN1t HstabN1t HhiN1t HbkN1t _.
apply (md_invX_ex _ _ _ Hmd6) in HmdN1t.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (HhN1t & HlzN1t & _).
pose proof (md_invX_ch1 _ _ HmdN1t) as HchN1t.
rewrite <- (md_invX_fs _ _ HmdN1t).
match goal with |- crealizes _ _ (t_exit (Z_to_bv 64 ?c) _) => let c' := eval cbv in c in change c with c' | _ => idtac end.
unfold wr; csrc0_diag_exit_tac HS' HchN1t 166%nat.
* cto_free_buf HS HMR Hcm (proj1 (proj1 HRE)).
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M2_N1f msx) in HS end.
lazymatch type of HS with st_ok _ ?Ec _ ?msx =>
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS) as Hr10;
eapply (free_site_cf src0_msyms API AX TBL (FCF _) Ec r1M2_N1f msx mD6 L6 A6 bq5 cap0 _ (-128) src0_keep [] 149 r1M2_LN1f r1M2_RSN1f RA_sf _
HS ltac:(drv_anch) r1M2_site_N1f ltac:(vm_compute; reflexivity) r1M2_statics_N1f HMR HW6 HB6 Hid6 Hin6);
[ rewrite Hr10; match goal with |- sv_denot _ ?x = _ => replace x with (SOff 14 0) by (symmetry; first [exact (proj1 r1M2_N_facts) | exact (proj1 (proj2 r1M2_N_facts)) | exact (proj1 (proj2 (proj2 r1M2_N_facts))) | exact (proj2 (proj2 (proj2 r1M2_N_facts)))]) end;
cbn [sv_denot]; rewrite Z.add_0_r, Hpb6, <- (proj1 (proj2 (proj1 HRE))), Z_to_bv_bv_unsigned; reflexivity
| exact Hb6
| intros kb sz [ ]
| clear Hr10 ]
end.
intros AN1f LN1f mSN1f mDN1f gN1f HS' ?HSA HMR' HWN1f HBN1f HmdN1f HstabN1f HhiN1f HbkN1f _.
apply (md_invX_ex _ _ _ Hmd6) in HmdN1f.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (HhN1f & HlzN1f & _).
pose proof (md_invX_ch1 _ _ HmdN1f) as HchN1f.
rewrite <- (md_invX_fs _ _ HmdN1f).
match goal with |- crealizes _ _ (t_exit (Z_to_bv 64 ?c) _) => let c' := eval cbv in c in change c with c' | _ => idtac end.
unfold wr; csrc0_diag_exit_tac HS' HchN1f 166%nat.
+
destruct Hres as [Hq0 HubA2].
destruct (HRn _ _ Hpath) as (b2 & Hb2).
apply (crz_conseq _ _ (ex (if count_mode data then 0 else 2) fs) _); [| apply t_eq_sym; apply HK].
apply (st_ok_regs src0segs _ _ mS2 (sr_set (ss_regs r1M2_MEp) 10%bv (SLit 0))) in HS.
2:{ intros r. destruct (decide (r = 10%bv)) as [->|Hne'].
- rewrite sr_get_set_same by reflexivity. rewrite (proj2 (proj2 r1M2_ME_facts)).
cbn [sv_denot]. rewrite Z.add_0_r. change 52%nat with (48 + 4)%nat. rewrite post_env_a0, Hq0. reflexivity.
- rewrite sr_get_set_other by exact Hne'. reflexivity. }
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M2_MEn msx) in HS end.
assert (HRE : run_env (post_env E 48 (ms_regs mS2) g2) data (ptr_addr L' b0)) by exact HE2.
cdrv_run_with src0tbl_ok HS HF.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M2_N0 msx) in HS;
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep Ec HS HF HMR end.
unfold ex.
destruct (count_mode data) eqn:Hcm.
* cto_free_buf HS HMR Hcm (proj1 HRE).
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M2_N0t msx) in HS end.
lazymatch type of HS with st_ok _ ?Ec _ ?msx =>
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS) as Hr10;
eapply (free_site_cf src0_msyms API AX TBL (FCF _) Ec r1M2_N0t msx mD2 L2 A2 b0 cap0 b2 (-128) src0_keep [] 65 r1M2_LN0t r1M2_RSN0t RA_sf _
HS ltac:(drv_anch) r1M2_site_N0t ltac:(vm_compute; reflexivity) r1M2_statics_N0t HMR HW2 HB2 Hid2 Hin2);
[ rewrite Hr10; match goal with |- sv_denot _ ?x = _ => replace x with (SOff 14 0) by (symmetry; first [exact (proj1 r1M2_N_facts) | exact (proj1 (proj2 r1M2_N_facts)) | exact (proj1 (proj2 (proj2 r1M2_N_facts))) | exact (proj2 (proj2 (proj2 r1M2_N_facts)))]) end;
cbn [sv_denot]; rewrite Z.add_0_r, Hpb2, <- (proj1 (proj2 HRE)), Z_to_bv_bv_unsigned; reflexivity
| exact Hb2
| intros kb sz [ ]
| clear Hr10 ]
end.
intros AN0t LN0t mSN0t mDN0t gN0t HS' ?HSA HMR' HWN0t HBN0t HmdN0t HstabN0t HhiN0t HbkN0t _.
apply (md_invX_ex _ _ _ Hmd2) in HmdN0t.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (HhN0t & HlzN0t & _).
pose proof (md_invX_ch1 _ _ HmdN0t) as HchN0t.
rewrite <- (md_invX_fs _ _ HmdN0t).
match goal with |- crealizes _ _ (t_exit (Z_to_bv 64 ?c) _) => let c' := eval cbv in c in change c with c' | _ => idtac end.
exact (src0_exit_cf _ _ mSN0t mDN0t 0 HS' ltac:(lia) r1M2_exit_N0t HhN0t HlzN0t).
* cto_free_buf HS HMR Hcm (proj1 HRE).
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M2_N0f msx) in HS end.
lazymatch type of HS with st_ok _ ?Ec _ ?msx =>
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS) as Hr10;
eapply (free_site_cf src0_msyms API AX TBL (FCF _) Ec r1M2_N0f msx mD2 L2 A2 b0 cap0 b2 (-128) src0_keep [] 65 r1M2_LN0f r1M2_RSN0f RA_sf _
HS ltac:(drv_anch) r1M2_site_N0f ltac:(vm_compute; reflexivity) r1M2_statics_N0f HMR HW2 HB2 Hid2 Hin2);
[ rewrite Hr10; match goal with |- sv_denot _ ?x = _ => replace x with (SOff 14 0) by (symmetry; first [exact (proj1 r1M2_N_facts) | exact (proj1 (proj2 r1M2_N_facts)) | exact (proj1 (proj2 (proj2 r1M2_N_facts))) | exact (proj2 (proj2 (proj2 r1M2_N_facts)))]) end;
cbn [sv_denot]; rewrite Z.add_0_r, Hpb2, <- (proj1 (proj2 HRE)), Z_to_bv_bv_unsigned; reflexivity
| exact Hb2
| intros kb sz [ ]
| clear Hr10 ]
end.
intros AN0f LN0f mSN0f mDN0f gN0f HS' ?HSA HMR' HWN0f HBN0f HmdN0f HstabN0f HhiN0f HbkN0f _.
apply (md_invX_ex _ _ _ Hmd2) in HmdN0f.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (HhN0f & HlzN0f & _).
pose proof (md_invX_ch1 _ _ HmdN0f) as HchN0f.
rewrite <- (md_invX_fs _ _ HmdN0f).
match goal with |- crealizes _ _ (t_exit (Z_to_bv 64 ?c) _) => let c' := eval cbv in c in change c with c' | _ => idtac end.
exact (src0_exit_cf _ _ mSN0f mDN0f 2 HS' ltac:(lia) r1M2_exit_N0f HhN0f HlzN0f).
Qed.
End d.
End a.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
