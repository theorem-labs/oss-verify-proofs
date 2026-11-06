(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YL19.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/U/Reusable/YL19.v; 21 of its 443 lines of code are new or changed and 128 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0h YK0i YK14 YK1b YK1a YK15 YK0k YK0n YK0p YP0n YM06 YM02.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0x YO0d YO0e YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YH00 YH01 YH03 YH02 YN3e YN35 YN3f YN3g YN34 YN3d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YN03 YL07 YL01 YL08 YL0d YL0e YL02 YL0a YL00 YL04 YL0c YL09 YL05 YL0g YL0k YL0m YL0u YL0r YL0o YL0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YI06 YI16 YI14 YI5b YI5c YL0i YL06 YL03 YL0l YL0t GIWalk.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL19 YO0d_mf YL0e_mf YL0d_mf YL06_mf.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable.R Require Import Cfg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Context {AM : AllocMode}.
Section d.
Variable API : AllocAPI src0_msyms.
Hypothesis AX : AllocExtra src0_msyms (aa_MR API).
Hypothesis HAM : amf = true.
Hypothesis Hmal : forall fx' : FPState, malloc_realizes (fx:=fx') (AM:=AM) src0_msyms (aa_MR API).
Hypothesis Hfre : forall fx' : FPState, free_realizes (fx:=fx') (AM:=AM) src0_msyms (aa_MR API).
Variable GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop.
Variable RI : list byte -> nat -> list (Z * Z) -> astate -> Prop.
Variable OUT : list byte -> list byte.
Hypothesis GIL : G_local_T src0segs src0_G GI.
Hypothesis GI0 : forall mem, G_img src0segs src0_G mem -> GI 0%nat [] mem.
Hypothesis LIBX : lib_contract_x_R_all src0_msyms API RI src0_G src0_R GI OUT LIBPC RA_LIB EMPTY LIB_STACK.
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
Hypothesis Hcalls : calls data = 4%nat.
Hypothesis Hpl : 0 < payload_len data.
Let lib_stk_pos : 0 <= LIB_STACK. Proof. unfold LIB_STACK. lia. Qed.
Ltac to_free_buf HS HMR Hcm Hed :=
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
drv_run_to_with src0tbl_ok HS src0_A_free HF;
lazymatch type of HS with st_ok _ ?E _ _ =>
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep E HS HF HMR end.
Theorem src0_runX_1M4_mf : forall E ms md,
run_env E data (ptr_addr L' b0) -> env_top E ->
st_ok src0segs E sQ1 ms -> aa_MR API L' A' (ms_mem ms) md -> md_invX fs md ->
blk_data src0_msyms (ms_mem ms) (ptr_addr L' b0) data ->
(forall tr q A2, cpath (malloc (payload_len data) A') tr (Some q, A2) -> RI (payload data) 0%nat [] A2) ->
forall K : option sptr * astate -> TSet,
(forall r, t_eq (K r) (leaf_shapeX data fs (payload_leaf b0 cap0 r))) ->
realizes src0segs (mkCfg ms md) (tset_mf (malloc (payload_len data) A') K).
Proof using AX HAM Hmal Hfre GIL GI0 LIBX FRM Hub Hcap0 HW HB Hid Hok HLc Hcl Hcalls Hpl.
intros E ms md HE HT HS HMR Hmd HD HRb K HK.
pose proof (payload_len_length data Hok) as HplLen.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hlz & _).
assert (Hin : In (b0, cap0) (user_blocks A')) by (rewrite Hub; left; reflexivity).
pose proof (mr_blocks _ _ (aa_laws API) L' A' (ms_mem ms) md b0 cap0 0 HMR Hin ltac:(lia)) as (_ & Hq1 & Hq2 & _).
assert (Hac : alloc_ceiling < 2 ^ 63) by (pose proof YM05.alloc_ceiling_val; lia).
unfold dlen in Hok, HLc. pose proof (config_len_bound data) as Hclb.
destruct (list_len2 data ltac:(lia)) as (d0 & d1 & rest & Ed).
assert (Hplv : payload_len data = Z.of_nat (length data) - 6 - config_len data) by reflexivity.
pose proof HE as HE0. destruct HE0 as (HEd & HE13 & HE26 & HE46 & HAN).
apply (src0_Q_calls data cap0 L' b0 Hcap0 Hok HLc E ms HE Hcl) in HS. rewrite Hcalls in HS. change (st_ok src0segs E r1M4_Q ms) in HS.
let v := eval cbv [sv_pl00 sv_pl add0 sv_cl sv_b1s] in sv_pl00 in
assert (Hpl00 : U E v = payload_len data) by (eapply U_pl00; eauto; lia).
apply (st_ok_add_cond src0segs E r1M4_Q ms BC_NE (ltac:(let v := eval cbv [sv_pl00 sv_pl add0 sv_cl sv_b1s] in sv_pl00 in exact v)) (SLit 0)) in HS.
2:{ rewrite branch_ne_U, Hpl00, U_SLit. change (zcanon 0) with 0. apply Bool.negb_true_iff. apply Z.eqb_neq. lia. }
drv_run_to_with src0tbl_ok HS src0_A_malloc HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E r1M4_ME msx) in HS end.
drv_bd AX src0_keep E HS HF HMR HD Hin.
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep E HS HF HMR.
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS) as Hr10. rewrite (proj1 (proj2 r1M4_ME_facts)) in Hr10.
rewrite (denot_lit_U E (add0 sv_pl00)), U_add0 in Hr10. cbv [sv_pl00 sv_pl add0 sv_cl sv_b1s] in Hr10. rewrite Hpl00 in Hr10.
eapply (malloc_site_mf src0_msyms API AX HAM Hmal E r1M4_ME _ md L' A' (payload_len data) (-208) src0_keep [] 48 r1M4_LME r1M4_RSME RA_ME K
HS ltac:(drv_anch) r1M4_site_ME r1M4_statics_ME HMR HW HB);
[ intros Hf; rewrite Hid in Hf; discriminate
| exact Hr10
| lia
| intros kb sz [ ]
| ].
clear Hr10.
intros res A2 L2 mS2 mD2 g2 tr HS2 ?HSA HMR2 HW2 HB2 Hmd2 Hpath Hstab Hhi Hbk Hres.
apply (md_invX_ex _ _ _ Hmd) in Hmd2.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR2) as (Hh2 & Hlz2 & _).
assert (Hid2 : st_init_done A2 = true) by (exact (malloc_keeps_init_done _ _ _ _ _ Hid (cpath_yields _ _ _ Hpath))).
destruct (Hstab _ _ Hin) as [Hin2 Hpb2].
lazymatch type of HS2 with st_ok _ _ _ ?msx => change (st_ok src0segs (post_env E 48 (ms_regs mS2) g2) r1M4_MEp msx) in HS2 end.
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
apply (rz_conseq _ _ (LIBK (payload data) (m_fs mD2) (fun l => wr ch_stdout line0 (lib_iter (payload data) 3 (run_tail 3) (ll_fs l)))) _).
2:{ eapply t_eq_trans; [| apply t_eq_sym; apply HK]. unfold payload_leaf; cbn [fst snd leaf_shapeX run_shape]. rewrite Hcalls. rewrite (md_invX_fs _ _ Hmd2). apply t_eq_refl. }
assert (H32 : bv_unsigned (ew (post_env E 48 (ms_regs mS2) g2) 52) = ptr_addr L2 q).
{ change 52%nat with (48 + 4)%nat. rewrite post_env_a0, Hq0, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
apply (st_ok_add_fact src0segs _ r1M4_MEp mS2 52 blkq_fact) in HS.
2:{ unfold afact_ok, blkq_fact. cbn [af_lo af_hi af_al2]. rewrite H32. change (2 ^ 4) with 16.
pose proof (mr_blocks_aligned _ _ (aa_laws API) L2 A2 (ms_mem mS2) mD2 q _ HMR Hinq). pose proof YM05.alloc_ceiling_val. lia. }
assert (HRE : renv (post_env E 48 (ms_regs mS2) g2) data (ptr_addr L' b0) (ptr_addr L2 q)) by (split; [exact HE2 | exact H32]).
clear HE2 H32.
drv_run_to_with src0tbl_ok HS src0_A_memcpy HF.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M4_MC msx) in HS;
drv_bd AX src0_keep Ec HS HF HMR HD2 Hin2;
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep Ec HS HF HMR end.
lazymatch type of HS with st_ok _ ?Ec _ ?msx =>
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS) as Hr10; pose proof (st_ok_reg src0segs _ _ _ 11%bv HS) as Hr11; pose proof (st_ok_reg src0segs _ _ _ 12%bv HS) as Hr12;
rewrite (proj1 r1M4_MC_facts) in Hr10; rewrite (proj1 (proj2 r1M4_MC_facts)) in Hr11; rewrite (proj2 (proj2 r1M4_MC_facts)) in Hr12;
eapply (src0_memcpy_site API AX Ec r1M4_MC msx mD2 L2 A2 q (payload_len data) (payload_len data) b0 cap0 (ptr_addr L' b0 + 6 + config_len data) 52 65 RA_MC _
HS ltac:(drv_anch) r1M4_ck_MC HMR Hinq Hin2 Hqb);
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
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M4_MCp msx) in HS end.
renv_sync HS HRE. etop_sync HS HT.
drv_run_to_with src0tbl_ok HS LIBPC HF.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M4_L1 msx) in HS;
drv_bd AX src0_keep Ec HS HF HMR HDq Hinq;
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep Ec HS HF HMR end.
lazymatch type of HS with st_ok _ ?Ec _ ?msx =>
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS) as Hr10; pose proof (st_ok_reg src0segs _ _ _ 11%bv HS) as Hr11;
rewrite (proj1 r1M4_L1_facts) in Hr10; rewrite (proj1 (proj2 r1M4_L1_facts)) in Hr11;
try rewrite <- (md_invX_fs _ _ Hmd2);
assert (CK1 : env_check (ss_mem r1M4_L1) = true) by (vm_compute; reflexivity);
eapply (lib_site_x_R_mf src0_msyms API AX LIBPC RA_LIB EMPTY LIB_STACK src0_G src0_R GI RI OUT LIBX lib_stk_pos FRM 0%nat [] Ec r1M4_L1 msx mD2 L2 A2
(ptr_addr L2 q) (payload_len data) (payload data) (-208) src0_keepG [] 76 r1M4_LL1 r1M4_RSL1 _
ltac:(lia) HS ltac:(drv_anch) r1M4_site_L1 ltac:(vm_compute; reflexivity) r1M4_statics_L1 HMR HW2 HB2 Hid2
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
pose proof (md_invX_lib _ _ _ _ _ Hmd2 Hmd4 HSN4 Hsort4) as HmdX4. clear Hmd4. rename HmdX4 into Hmd4.
assert (HDq4 : blk_data src0_msyms (ms_mem mS4) (ptr_addr L2 q) (payload data)).
{ eapply (blk_data_kept src0_msyms); [|exact HDq]. intros ii Hii. apply Hplk4. rewrite HplLen. exact Hii. }
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (Hh4 & Hlz4 & _).
destruct (Hstab4 _ _ Hin2 (notin_nil _)) as (bq4 & Hin4 & Hpb4).
pose proof (kept_notin _ _ _ _ _ _ _ Hin2 Hpb2 (notin_nil _) HTT1) as HbT1. try rewrite Hpb2 in Hpb4.
destruct (Hstab4 _ _ Hinq (notin_nil _)) as (pq4 & Hinq4 & Hpq4).
pose proof (kept_notin _ _ _ _ _ _ _ Hinq (eq_refl (ptr_addr L2 q)) (notin_nil _) HTT1) as HqT1.
clear HS HMR Hhi4 Hbk4 Hstab4. rename HS' into HS. rename HMR' into HMR. clear FRM; try clear fx. rename FRM' into FRM.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M4_P1 msx) in HS end.
renv_sync HS HRE. etop_sync HS HT.
pose proof (md_invX_ch1 _ _ Hmd4) as Hch4.
unfold wr at 1.
drv_printf0 HS Hch4 93%nat RET_PF HF.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M4_I1 msx) in HS;
drv_bd AX src0_keep Ec HS HF HMR HDq4 Hinq4;
drv_gi_T (GI_frame_T src0_msyms (aa_MR API) (aa_laws API) AX src0_G GI GIL src0_keep) Ec HS HF HGI1 HTL1 HMR;
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep Ec HS HF HMR end.
renv_sync HS HRE. etop_sync HS HT.
drv_run_to_with src0tbl_ok HS LIBPC HF.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M4_L2 msx) in HS;
drv_bd AX src0_keep Ec HS HF HMR HDq4 Hinq4;
drv_gi_T (GI_frame_T src0_msyms (aa_MR API) (aa_laws API) AX src0_G GI GIL src0_keep) Ec HS HF HGI1 HTL1 HMR;
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep Ec HS HF HMR end.
lazymatch type of HS with st_ok _ ?Ec _ ?msx =>
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS) as Hr10; pose proof (st_ok_reg src0segs _ _ _ 11%bv HS) as Hr11;
rewrite (proj1 r1M4_L2_facts) in Hr10; rewrite (proj1 (proj2 r1M4_L2_facts)) in Hr11;
try rewrite <- (md_invX_fs _ _ Hmd4);
assert (CK2 : env_check (ss_mem r1M4_L2) = true) by (vm_compute; reflexivity);
eapply (lib_site_x_R_mf src0_msyms API AX LIBPC RA_LIB EMPTY LIB_STACK src0_G src0_R GI RI OUT LIBX lib_stk_pos FRM 1%nat T1 Ec r1M4_L2 msx mD4 L3 A3
(ptr_addr L2 q) (payload_len data) (payload data) (-208) src0_keepG [] 104 r1M4_LL2 r1M4_RSL2 _
ltac:(lia) HS ltac:(drv_anch) r1M4_site_L2 ltac:(vm_compute; reflexivity) r1M4_statics_L2 HMR HW4 HB4 Hid4 HGI1 HTL1 (fun _ => HqT1)
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
pose proof (md_invX_lib _ _ _ _ _ Hmd4 Hmd5 HSN5 Hsort5) as HmdX5. clear Hmd5. rename HmdX5 into Hmd5.
assert (HDq5 : blk_data src0_msyms (ms_mem mS5) (ptr_addr L2 q) (payload data)).
{ eapply (blk_data_kept src0_msyms); [|exact HDq4]. intros ii Hii. apply Hplk5. rewrite HplLen. exact Hii. }
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (Hh5 & Hlz5 & _).
destruct (Hstab5 _ _ Hin4 ltac:(rewrite Hpb4; exact HbT1)) as (bq5 & Hin5 & Hpb5).
pose proof (kept_notin _ _ _ _ _ _ _ Hin4 Hpb4 HbT1 HTT2) as HbT2. try rewrite Hpb4 in Hpb5.
destruct (Hstab5 _ _ Hinq4 ltac:(rewrite Hpq4; exact HqT1)) as (pq5 & Hinq5 & Hpq5).
pose proof (kept_notin _ _ _ _ _ _ _ Hinq4 Hpq4 HqT1 HTT2) as HqT2. rewrite Hpq4 in Hpq5.
clear HS HMR Hhi5 Hbk5 Hstab5. rename HS' into HS. rename HMR' into HMR. clear FRM; try clear fx4. rename FRM' into FRM.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M4_P2 msx) in HS end.
renv_sync HS HRE. etop_sync HS HT.
drv_run_to_with src0tbl_ok HS LIBPC HF.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M4_L3 msx) in HS;
drv_bd AX src0_keep Ec HS HF HMR HDq5 Hinq5;
drv_gi_T (GI_frame_T src0_msyms (aa_MR API) (aa_laws API) AX src0_G GI GIL src0_keep) Ec HS HF HGI2 HTL2 HMR;
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep Ec HS HF HMR end.
lazymatch type of HS with st_ok _ ?Ec _ ?msx =>
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS) as Hr10; pose proof (st_ok_reg src0segs _ _ _ 11%bv HS) as Hr11;
rewrite (proj1 r1M4_L3_facts) in Hr10; rewrite (proj1 (proj2 r1M4_L3_facts)) in Hr11;
try rewrite <- (md_invX_fs _ _ Hmd5);
assert (CK3 : env_check (ss_mem r1M4_L3) = true) by (vm_compute; reflexivity);
eapply (lib_site_x_R_mf src0_msyms API AX LIBPC RA_LIB EMPTY LIB_STACK src0_G src0_R GI RI OUT LIBX lib_stk_pos FRM 2%nat T2 Ec r1M4_L3 msx mD5 L4 A4
(ptr_addr L2 q) (payload_len data) (payload data) (-208) src0_keepG [] 132 r1M4_LL3 r1M4_RSL3 _
ltac:(lia) HS ltac:(drv_anch) r1M4_site_L3 ltac:(vm_compute; reflexivity) r1M4_statics_L3 HMR HW5 HB5 Hid5 HGI2 HTL2 (fun _ => HqT2)
(st_ok_G_img src0segs _ _ _ src0_R HS ltac:(vm_compute; reflexivity)) (proj1 (proj2 (md_invX_inv _ _ Hmd5))));
[ rewrite Hr10; cbn [sv_denot]; rewrite Z.add_0_r, <- (proj2 HRE), Z_to_bv_bv_unsigned; reflexivity
| rewrite Hr11; rewrite (denot_lit_U Ec (add0 sv_pl00)), U_add0, (U_pl00 Ec data d0 d1 rest); [reflexivity | exact (proj1 (proj1 HRE)) | exact Ed | exact (proj1 (proj2 (proj2 (proj1 HRE)))) | lia]
| right; split; [lia | exists pq5; split; [exact Hinq5 | exact Hpq5]]
| intros kb sz [ ]
| exact HplLen
| exact HDq5
| exact HRES5
| split; [|split]; [ exact (proj1 (src0_env_rom _ (env_of_st_ok src0segs _ _ _ HS CK3)))
| exact (proj2 (src0_env_rom _ (env_of_st_ok src0segs _ _ _ HS CK3)))
| exact (md_invX_names _ _ Hmd5) ]
| exact (md_invX_free _ _ Hmd5)
| exact (md_invX_sorted _ _ Hmd5)
| unfold env_top in HT; lia
| clear Hr10 Hr11 CK3 ]
end.
intros l6 fx6 A5 L5 mS6 mD6 g6 T3 HS' ?HSA FRM' HMR' HW6 HB6 Hid6 Hmd6 Hstab6 Hhi6 Hbk6 Hret6 Hout6 Hsort6 HSN6 HRES6 Hplk6 HTL3 HTT3 HGI3. cbv beta. cbn [lib_iter run_tail].
pose proof (md_invX_lib _ _ _ _ _ Hmd5 Hmd6 HSN6 Hsort6) as HmdX6. clear Hmd6. rename HmdX6 into Hmd6.
assert (HDq6 : blk_data src0_msyms (ms_mem mS6) (ptr_addr L2 q) (payload data)).
{ eapply (blk_data_kept src0_msyms); [|exact HDq5]. intros ii Hii. apply Hplk6. rewrite HplLen. exact Hii. }
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (Hh6 & Hlz6 & _).
destruct (Hstab6 _ _ Hin5 ltac:(rewrite Hpb5; exact HbT2)) as (bq6 & Hin6 & Hpb6).
pose proof (kept_notin _ _ _ _ _ _ _ Hin5 Hpb5 HbT2 HTT3) as HbT3. try rewrite Hpb5 in Hpb6.
destruct (Hstab6 _ _ Hinq5 ltac:(rewrite Hpq5; exact HqT2)) as (pq6 & Hinq6 & Hpq6).
pose proof (kept_notin _ _ _ _ _ _ _ Hinq5 Hpq5 HqT2 HTT3) as HqT3. rewrite Hpq5 in Hpq6.
clear HS HMR Hhi6 Hbk6 Hstab6. rename HS' into HS. rename HMR' into HMR. clear FRM; try clear fx5. rename FRM' into FRM.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M4_P3 msx) in HS end.
renv_sync HS HRE. etop_sync HS HT.
drv_run_to_with src0tbl_ok HS LIBPC HF.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M4_L4 msx) in HS;
drv_bd AX src0_keep Ec HS HF HMR HDq6 Hinq6;
drv_gi_T (GI_frame_T src0_msyms (aa_MR API) (aa_laws API) AX src0_G GI GIL src0_keep) Ec HS HF HGI3 HTL3 HMR;
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep Ec HS HF HMR end.
lazymatch type of HS with st_ok _ ?Ec _ ?msx =>
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS) as Hr10; pose proof (st_ok_reg src0segs _ _ _ 11%bv HS) as Hr11;
rewrite (proj1 r1M4_L4_facts) in Hr10; rewrite (proj1 (proj2 r1M4_L4_facts)) in Hr11;
try rewrite <- (md_invX_fs _ _ Hmd6);
assert (CK4 : env_check (ss_mem r1M4_L4) = true) by (vm_compute; reflexivity);
eapply (lib_site_x_R_mf src0_msyms API AX LIBPC RA_LIB EMPTY LIB_STACK src0_G src0_R GI RI OUT LIBX lib_stk_pos FRM 3%nat T3 Ec r1M4_L4 msx mD6 L5 A5
(ptr_addr L2 q) (payload_len data) (payload data) (-208) src0_keepG [] 160 r1M4_LL4 r1M4_RSL4 _
ltac:(lia) HS ltac:(drv_anch) r1M4_site_L4 ltac:(vm_compute; reflexivity) r1M4_statics_L4 HMR HW6 HB6 Hid6 HGI3 HTL3 (fun _ => HqT3)
(st_ok_G_img src0segs _ _ _ src0_R HS ltac:(vm_compute; reflexivity)) (proj1 (proj2 (md_invX_inv _ _ Hmd6))));
[ rewrite Hr10; cbn [sv_denot]; rewrite Z.add_0_r, <- (proj2 HRE), Z_to_bv_bv_unsigned; reflexivity
| rewrite Hr11; rewrite (denot_lit_U Ec (add0 sv_pl00)), U_add0, (U_pl00 Ec data d0 d1 rest); [reflexivity | exact (proj1 (proj1 HRE)) | exact Ed | exact (proj1 (proj2 (proj2 (proj1 HRE)))) | lia]
| right; split; [lia | exists pq6; split; [exact Hinq6 | exact Hpq6]]
| intros kb sz [ ]
| exact HplLen
| exact HDq6
| exact HRES6
| split; [|split]; [ exact (proj1 (src0_env_rom _ (env_of_st_ok src0segs _ _ _ HS CK4)))
| exact (proj2 (src0_env_rom _ (env_of_st_ok src0segs _ _ _ HS CK4)))
| exact (md_invX_names _ _ Hmd6) ]
| exact (md_invX_free _ _ Hmd6)
| exact (md_invX_sorted _ _ Hmd6)
| unfold env_top in HT; lia
| clear Hr10 Hr11 CK4 ]
end.
intros l7 fx7 A6 L6 mS7 mD7 g7 T4 HS' ?HSA FRM' HMR' HW7 HB7 Hid7 Hmd7 Hstab7 Hhi7 Hbk7 Hret7 Hout7 Hsort7 HSN7 HRES7 Hplk7 HTL4 HTT4 HGI4. cbv beta. cbn [lib_iter run_tail].
pose proof (md_invX_lib _ _ _ _ _ Hmd6 Hmd7 HSN7 Hsort7) as HmdX7. clear Hmd7. rename HmdX7 into Hmd7.
assert (HDq7 : blk_data src0_msyms (ms_mem mS7) (ptr_addr L2 q) (payload data)).
{ eapply (blk_data_kept src0_msyms); [|exact HDq6]. intros ii Hii. apply Hplk7. rewrite HplLen. exact Hii. }
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (Hh7 & Hlz7 & _).
destruct (Hstab7 _ _ Hin6 ltac:(rewrite Hpb6; exact HbT3)) as (bq7 & Hin7 & Hpb7). try rewrite Hpb6 in Hpb7.
destruct (Hstab7 _ _ Hinq6 ltac:(rewrite Hpq6; exact HqT3)) as (pq7 & Hinq7 & Hpq7). rewrite Hpq6 in Hpq7.
clear HS HMR Hhi7 Hbk7 Hstab7. rename HS' into HS. rename HMR' into HMR. clear FRM; try clear fx6. rename FRM' into FRM.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M4_P4 msx) in HS end.
renv_sync HS HRE. etop_sync HS HT.
drv_run_to_with src0tbl_ok HS src0_A_free HF.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M4_F msx) in HS;
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep Ec HS HF HMR end.
lazymatch type of HS with st_ok _ ?Ec _ ?msx =>
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS) as Hr10; rewrite r1M4_F_facts in Hr10;
eapply (free_site_mf src0_msyms API AX Hfre Ec r1M4_F msx mD7 L6 A6 pq7 (payload_len data) (-208) src0_keep [] 188 r1M4_LF r1M4_RSF RA_FQ _
HS ltac:(drv_anch) r1M4_site_F r1M4_statics_F HMR HW7 HB7 Hid7 Hinq7);
[ rewrite Hr10; cbn [sv_denot]; rewrite Z.add_0_r, Hpq7, <- (proj2 HRE), Z_to_bv_bv_unsigned; reflexivity
| intros kb sz [ ]
| clear Hr10 ]
end.
intros A8 L8 mS8 mD8 g8 tr8 HS' ?HSA HMR' HW8 HB8 Hmd8 Hpath8 Hub8 Hstab8 Hhi8 Hbk8.
apply (md_invX_ex _ _ _ Hmd7) in Hmd8.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (Hh8 & Hlz8 & _).
assert (Hid8 : st_init_done A8 = true) by (exact (free_keeps_init_done _ _ _ _ _ Hid7 (cpath_yields _ _ _ Hpath8))).
destruct (Hstab8 _ _ Hin7 ltac:(intros HH; apply Hqba; rewrite <- Hpq7, <- Hpb7, HH; reflexivity)) as [Hin8 Hpb8]. try rewrite Hpb7 in Hpb8.
clear HS HMR Hhi8 Hbk8 Hstab8. rename HS' into HS. rename HMR' into HMR.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M4_Fp msx) in HS end.
renv_sync HS HRE. etop_sync HS HT.
drv_run_with src0tbl_ok HS HF.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M4_N1 msx) in HS;
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep Ec HS HF HMR end.
unfold ex.
destruct (count_mode data) eqn:Hcm.
* to_free_buf HS HMR Hcm (proj1 (proj1 HRE)).
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M4_N1t msx) in HS end.
lazymatch type of HS with st_ok _ ?Ec _ ?msx =>
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS) as Hr10;
eapply (free_site_mf src0_msyms API AX Hfre Ec r1M4_N1t msx mD8 L8 A8 bq7 cap0 (-128) src0_keep [] 205 r1M4_LN1t r1M4_RSN1t RA_sf _
HS ltac:(drv_anch) r1M4_site_N1t r1M4_statics_N1t HMR HW8 HB8 Hid8 Hin8);
[ rewrite Hr10; match goal with |- sv_denot _ ?x = _ => replace x with (SOff 14 0) by (symmetry; first [exact (proj1 r1M4_N_facts) | exact (proj1 (proj2 r1M4_N_facts)) | exact (proj1 (proj2 (proj2 r1M4_N_facts))) | exact (proj2 (proj2 (proj2 r1M4_N_facts)))]) end;
cbn [sv_denot]; rewrite Z.add_0_r, Hpb8, <- (proj1 (proj2 (proj1 HRE))), Z_to_bv_bv_unsigned; reflexivity
| intros kb sz [ ]
| clear Hr10 ]
end.
intros AN1t LN1t mSN1t mDN1t gN1t trN1t HS' ?HSA HMR' HWN1t HBN1t HmdN1t HpathN1t HubN1t HstabN1t HhiN1t HbkN1t.
apply (md_invX_ex _ _ _ Hmd8) in HmdN1t.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (HhN1t & HlzN1t & _).
pose proof (md_invX_ch1 _ _ HmdN1t) as HchN1t.
rewrite <- (md_invX_fs _ _ HmdN1t).
match goal with |- realizes _ _ (t_exit (Z_to_bv 64 ?c) _) => let c' := eval cbv in c in change c with c' | _ => idtac end.
unfold wr; src0_diag_exit_tac HS' HchN1t 222%nat.
* to_free_buf HS HMR Hcm (proj1 (proj1 HRE)).
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M4_N1f msx) in HS end.
lazymatch type of HS with st_ok _ ?Ec _ ?msx =>
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS) as Hr10;
eapply (free_site_mf src0_msyms API AX Hfre Ec r1M4_N1f msx mD8 L8 A8 bq7 cap0 (-128) src0_keep [] 205 r1M4_LN1f r1M4_RSN1f RA_sf _
HS ltac:(drv_anch) r1M4_site_N1f r1M4_statics_N1f HMR HW8 HB8 Hid8 Hin8);
[ rewrite Hr10; match goal with |- sv_denot _ ?x = _ => replace x with (SOff 14 0) by (symmetry; first [exact (proj1 r1M4_N_facts) | exact (proj1 (proj2 r1M4_N_facts)) | exact (proj1 (proj2 (proj2 r1M4_N_facts))) | exact (proj2 (proj2 (proj2 r1M4_N_facts)))]) end;
cbn [sv_denot]; rewrite Z.add_0_r, Hpb8, <- (proj1 (proj2 (proj1 HRE))), Z_to_bv_bv_unsigned; reflexivity
| intros kb sz [ ]
| clear Hr10 ]
end.
intros AN1f LN1f mSN1f mDN1f gN1f trN1f HS' ?HSA HMR' HWN1f HBN1f HmdN1f HpathN1f HubN1f HstabN1f HhiN1f HbkN1f.
apply (md_invX_ex _ _ _ Hmd8) in HmdN1f.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (HhN1f & HlzN1f & _).
pose proof (md_invX_ch1 _ _ HmdN1f) as HchN1f.
rewrite <- (md_invX_fs _ _ HmdN1f).
match goal with |- realizes _ _ (t_exit (Z_to_bv 64 ?c) _) => let c' := eval cbv in c in change c with c' | _ => idtac end.
unfold wr; src0_diag_exit_tac HS' HchN1f 222%nat.
+
destruct Hres as [Hq0 HubA2].
apply (rz_conseq _ _ (ex (if count_mode data then 0 else 2) fs) _); [| apply t_eq_sym; apply HK].
apply (st_ok_regs src0segs _ _ mS2 (sr_set (ss_regs r1M4_MEp) 10%bv (SLit 0))) in HS.
2:{ intros r. destruct (decide (r = 10%bv)) as [->|Hne'].
- rewrite sr_get_set_same by reflexivity. rewrite (proj2 (proj2 r1M4_ME_facts)).
cbn [sv_denot]. rewrite Z.add_0_r. change 52%nat with (48 + 4)%nat. rewrite post_env_a0, Hq0. reflexivity.
- rewrite sr_get_set_other by exact Hne'. reflexivity. }
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M4_MEn msx) in HS end.
assert (HRE : run_env (post_env E 48 (ms_regs mS2) g2) data (ptr_addr L' b0)) by exact HE2.
drv_run_with src0tbl_ok HS HF.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M4_N0 msx) in HS;
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep Ec HS HF HMR end.
unfold ex.
destruct (count_mode data) eqn:Hcm.
* to_free_buf HS HMR Hcm (proj1 HRE).
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M4_N0t msx) in HS end.
lazymatch type of HS with st_ok _ ?Ec _ ?msx =>
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS) as Hr10;
eapply (free_site_mf src0_msyms API AX Hfre Ec r1M4_N0t msx mD2 L2 A2 b0 cap0 (-128) src0_keep [] 65 r1M4_LN0t r1M4_RSN0t RA_sf _
HS ltac:(drv_anch) r1M4_site_N0t r1M4_statics_N0t HMR HW2 HB2 Hid2 Hin2);
[ rewrite Hr10; match goal with |- sv_denot _ ?x = _ => replace x with (SOff 14 0) by (symmetry; first [exact (proj1 r1M4_N_facts) | exact (proj1 (proj2 r1M4_N_facts)) | exact (proj1 (proj2 (proj2 r1M4_N_facts))) | exact (proj2 (proj2 (proj2 r1M4_N_facts)))]) end;
cbn [sv_denot]; rewrite Z.add_0_r, Hpb2, <- (proj1 (proj2 HRE)), Z_to_bv_bv_unsigned; reflexivity
| intros kb sz [ ]
| clear Hr10 ]
end.
intros AN0t LN0t mSN0t mDN0t gN0t trN0t HS' ?HSA HMR' HWN0t HBN0t HmdN0t HpathN0t HubN0t HstabN0t HhiN0t HbkN0t.
apply (md_invX_ex _ _ _ Hmd2) in HmdN0t.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (HhN0t & HlzN0t & _).
pose proof (md_invX_ch1 _ _ HmdN0t) as HchN0t.
rewrite <- (md_invX_fs _ _ HmdN0t).
match goal with |- realizes _ _ (t_exit (Z_to_bv 64 ?c) _) => let c' := eval cbv in c in change c with c' | _ => idtac end.
exact (src0_exit _ _ mSN0t mDN0t 0 HS' ltac:(lia) r1M4_exit_N0t HhN0t HlzN0t).
* to_free_buf HS HMR Hcm (proj1 HRE).
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1M4_N0f msx) in HS end.
lazymatch type of HS with st_ok _ ?Ec _ ?msx =>
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS) as Hr10;
eapply (free_site_mf src0_msyms API AX Hfre Ec r1M4_N0f msx mD2 L2 A2 b0 cap0 (-128) src0_keep [] 65 r1M4_LN0f r1M4_RSN0f RA_sf _
HS ltac:(drv_anch) r1M4_site_N0f r1M4_statics_N0f HMR HW2 HB2 Hid2 Hin2);
[ rewrite Hr10; match goal with |- sv_denot _ ?x = _ => replace x with (SOff 14 0) by (symmetry; first [exact (proj1 r1M4_N_facts) | exact (proj1 (proj2 r1M4_N_facts)) | exact (proj1 (proj2 (proj2 r1M4_N_facts))) | exact (proj2 (proj2 (proj2 r1M4_N_facts)))]) end;
cbn [sv_denot]; rewrite Z.add_0_r, Hpb2, <- (proj1 (proj2 HRE)), Z_to_bv_bv_unsigned; reflexivity
| intros kb sz [ ]
| clear Hr10 ]
end.
intros AN0f LN0f mSN0f mDN0f gN0f trN0f HS' ?HSA HMR' HWN0f HBN0f HmdN0f HpathN0f HubN0f HstabN0f HhiN0f HbkN0f.
apply (md_invX_ex _ _ _ Hmd2) in HmdN0f.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (HhN0f & HlzN0f & _).
pose proof (md_invX_ch1 _ _ HmdN0f) as HchN0f.
rewrite <- (md_invX_fs _ _ HmdN0f).
match goal with |- realizes _ _ (t_exit (Z_to_bv 64 ?c) _) => let c' := eval cbv in c in change c with c' | _ => idtac end.
exact (src0_exit _ _ mSN0f mDN0f 2 HS' ltac:(lia) r1M4_exit_N0f HhN0f HlzN0f).
Qed.
End d.
End a.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
