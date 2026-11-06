(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from lib/Reusable/YL12.v. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/libreac/fuzz_scene/lib/Reusable/YL12_cfw.v, with its module paths changed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK11 YK0o YK0h YK0i YK14 YK1b YK1a YK15 YK0k YK0n YK0p YP0n YM06 YM02.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YO0i YO0f YO0x YO0d YO0e YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO06.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YH00 YH01 YH03 YH02 YN3e YN35 YN3f YN3g YN34 YN3d.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YN03 YL07 YL01 YL08 YL0d YL0e YL02 YL0a YL00 YL04 YL0c YL09 YL05 YL0g YL0k YL0m YL0u YL0r YL0o YL0s.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YI06 YI16 YI14 YI5b YI5c YL0i YL06 YL03 YL0l YL0t GIWalk.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YL12 YK15_cfw YP03_cfw YN35_cfw YN3d_cfw YL0i_cfw YL06_cfw YL0d_cfw YL0k_cfw.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib Require Import Contract SlotAgree.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Mem.
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
Hypothesis GI0 : forall mem, G_img src0segs src0_G mem -> GI 0%nat [] mem.
Hypothesis LIBXc : lib_contract_x_Rc_all src0_msyms API RI src0_G src0_R GI OUT LIBPC RA_LIB EMPTY LIB_STACK.
Hypothesis FCF : forall fx' : FPState, @free_contract_cf fx' rc src0_msyms API.
Hypothesis TBL : forall L A mem md, aa_MR API L A mem md -> forall a, static_owned src0_msyms a -> 0 <= a < 2 ^ 64 ->
Mem.ro_addr src0segs (Z_to_bv 64 a) = true -> mbyte src0segs mem a = seg_rom src0segs (Z_to_bv 64 a).
Hypothesis RIres : forall pl j T A, RI pl j T A -> exists b, res_ok_slots A b.
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
Hypothesis Hcalls : calls data = 1%nat.
Hypothesis Hpl : payload_len data = 0.
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
Theorem src0_runX_1E1_cf : forall E ms md,
run_env E data (ptr_addr L' b0) -> env_top E ->
st_ok src0segs E sQ1 ms -> aa_MR API L' A' (ms_mem ms) md -> md_invX fs md ->
RI (payload data) 0%nat [] A' ->
crealizes src0_msyms (mkCfg ms md) (leaf_shapeX data fs (DL_run b0 cap0 None, A')).
Proof using AX FCF FRM GI0 HB HLc HW Hcalls Hcap0 Hcl Hid Hok Hpl Hub LIBXc RIres TBL.
intros E ms md HE HT HS HMR Hmd HRb.
pose proof (payload_len_length data Hok) as HplLen. pose proof (payload_nil data Hok Hpl) as HplNil.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hlz & _).
assert (Hin : In (b0, cap0) (user_blocks A')) by (rewrite Hub; left; reflexivity).
pose proof (mr_blocks _ _ (aa_laws API) L' A' (ms_mem ms) md b0 cap0 0 HMR Hin ltac:(lia)) as (_ & Hq1 & Hq2 & _).
assert (Hac : alloc_ceiling < 2 ^ 63) by (pose proof YM05.alloc_ceiling_val; lia).
unfold dlen in Hok, HLc. pose proof (config_len_bound data) as Hclb.
destruct (list_len2 data ltac:(lia)) as (d0 & d1 & rest & Ed).
assert (Hplv : payload_len data = Z.of_nat (length data) - 6 - config_len data) by reflexivity.
pose proof HE as HE0. destruct HE0 as (HEd & HE13 & HE26 & HE46 & HAN).
apply (src0_Q_calls data cap0 L' b0 Hcap0 Hok HLc E ms HE Hcl) in HS. rewrite Hcalls in HS. change (st_ok src0segs E r1E1_Q ms) in HS.
let v := eval cbv [sv_pl00 sv_pl add0 sv_cl sv_b1s] in sv_pl00 in
assert (Hpl00 : U E v = payload_len data) by (eapply U_pl00; eauto; lia).
apply (st_ok_add_cond src0segs E r1E1_Q ms BC_EQ (ltac:(let v := eval cbv [sv_pl00 sv_pl add0 sv_cl sv_b1s] in sv_pl00 in exact v)) (SLit 0)) in HS.
2:{ rewrite branch_eq_U, Hpl00, U_SLit, Hpl. reflexivity. }
change (st_ok src0segs E r1E1_QE ms) in HS.
rewrite <- (md_invX_fs _ _ Hmd).
apply (crz_conseq _ _ (LIBK (payload data) (m_fs md) (fun l => wr ch_stdout line0 (lib_iter (payload data) 0 (run_tail 0) (ll_fs l)))) _).
2:{ cbn [fst snd leaf_shapeX run_shape]. rewrite Hcalls. apply t_eq_refl. }
assert (HRE : run_env E data (ptr_addr L' b0)) by exact HE.
pose proof Hin as Hin2. assert (Hpb2 : ptr_addr L' b0 = ptr_addr L' b0) by reflexivity.
pose proof HRb as HRbL.
cdrv_run_to_with src0tbl_ok HS LIBPC HF.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1E1_L1 msx) in HS;
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep Ec HS HF HMR end.
lazymatch type of HS with st_ok _ ?Ec _ ?msx =>
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS) as Hr10; pose proof (st_ok_reg src0segs _ _ _ 11%bv HS) as Hr11;
rewrite (proj1 r1E1_L1_facts) in Hr10; rewrite (proj1 (proj2 r1E1_L1_facts)) in Hr11;
try rewrite <- (md_invX_fs _ _ Hmd);
assert (CK1 : env_check (ss_mem r1E1_L1) = true) by (vm_compute; reflexivity);
eapply (lib_site_x_R_cf src0_msyms API AX LIBPC RA_LIB EMPTY LIB_STACK src0_G src0_R GI RI OUT LIBXc lib_stk_pos FRM 0%nat [] Ec r1E1_L1 msx md L' A'
EMPTY (payload_len data) (payload data) (-208) src0_keepG [] 48 r1E1_LL1 r1E1_RSL1 _
ltac:(lia) HS ltac:(drv_anch) r1E1_site_L1 ltac:(vm_compute; reflexivity) r1E1_statics_L1 HMR HW HB Hid
(GI0 _ (st_ok_G_img src0segs _ _ _ src0_G HS ltac:(vm_compute; reflexivity))) (tb_live_nil L' A') (fun _ => notin_nil _)
(st_ok_G_img src0segs _ _ _ src0_R HS ltac:(vm_compute; reflexivity)) (proj1 (proj2 (md_invX_inv _ _ Hmd))));
[ rewrite Hr10; reflexivity
| rewrite Hr11; rewrite (denot_lit_U Ec (add0 sv_pl00)), U_add0, (U_pl00 Ec data d0 d1 rest); [rewrite Hpl; reflexivity | exact (proj1 HRE) | exact Ed | exact (proj1 (proj2 (proj2 HRE))) | lia]
| left; split; [exact Hpl | reflexivity]
| intros kb sz [ ]
| exact HplLen
| rewrite HplNil; apply (blk_data_nil src0_msyms)
| exact HRbL
| split; [|split]; [ exact (proj1 (src0_env_rom _ (env_of_st_ok src0segs _ _ _ HS CK1)))
| exact (proj2 (src0_env_rom _ (env_of_st_ok src0segs _ _ _ HS CK1)))
| exact (md_invX_names _ _ Hmd) ]
| exact (md_invX_free _ _ Hmd)
| exact (md_invX_sorted _ _ Hmd)
| unfold env_top in HT; lia
| clear Hr10 Hr11 CK1 ]
end.
intros l4 fx4 A3 L3 mS4 mD4 g4 T1 HS' ?HSA FRM' HMR' HW4 HB4 Hid4 Hmd4 Hstab4 Hhi4 Hbk4 Hret4 Hout4 Hsort4 HSN4 HRES4 Hplk4 HTL1 HTT1 HGI1. cbv beta. cbn [lib_iter run_tail].
destruct (RIres _ _ _ _ HRES4) as (b4 & Hb4).
pose proof (md_invX_lib _ _ _ _ _ Hmd Hmd4 HSN4 Hsort4) as HmdX4. clear Hmd4. rename HmdX4 into Hmd4.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (Hh4 & Hlz4 & _).
destruct (Hstab4 _ _ Hin2 (notin_nil _)) as (bq4 & Hin4 & Hpb4). try rewrite Hpb2 in Hpb4.
clear HS HMR Hhi4 Hbk4 Hstab4. rename HS' into HS. rename HMR' into HMR. clear FRM; try clear fx. rename FRM' into FRM.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1E1_P1 msx) in HS end.
renv_sync HS HRE. etop_sync HS HT.
pose proof (md_invX_ch1 _ _ Hmd4) as Hch4.
unfold wr at 1.
cdrv_printf0 HS Hch4 65%nat RET_PF HF.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1E1_I1 msx) in HS;
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep Ec HS HF HMR end.
renv_sync HS HRE. etop_sync HS HT.
cdrv_run_with src0tbl_ok HS HF.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1E1_N1 msx) in HS;
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep Ec HS HF HMR end.
unfold ex.
destruct (count_mode data) eqn:Hcm.
* cto_free_buf HS HMR Hcm (proj1 HRE).
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1E1_N1t msx) in HS end.
lazymatch type of HS with st_ok _ ?Ec _ ?msx =>
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS) as Hr10;
eapply (free_site_cf src0_msyms API AX TBL (FCF _) Ec r1E1_N1t msx mD4 L3 A3 bq4 cap0 b4 (-128) src0_keep [] 76 r1E1_LN1t r1E1_RSN1t RA_sf _
HS ltac:(drv_anch) r1E1_site_N1t ltac:(vm_compute; reflexivity) r1E1_statics_N1t HMR HW4 HB4 Hid4 Hin4);
[ rewrite Hr10; match goal with |- sv_denot _ ?x = _ => replace x with (SOff 14 0) by (symmetry; first [exact (proj1 r1E1_N_facts) | exact (proj1 (proj2 r1E1_N_facts)) | exact (proj1 (proj2 (proj2 r1E1_N_facts))) | exact (proj2 (proj2 (proj2 r1E1_N_facts)))]) end;
cbn [sv_denot]; rewrite Z.add_0_r, Hpb4, <- (proj1 (proj2 HRE)), Z_to_bv_bv_unsigned; reflexivity
| exact Hb4
| intros kb sz [ ]
| clear Hr10 ]
end.
intros AN1t LN1t mSN1t mDN1t gN1t HS' ?HSA HMR' HWN1t HBN1t HmdN1t HstabN1t HhiN1t HbkN1t _.
apply (md_invX_ex _ _ _ Hmd4) in HmdN1t.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (HhN1t & HlzN1t & _).
pose proof (md_invX_ch1 _ _ HmdN1t) as HchN1t.
rewrite <- (md_invX_fs _ _ HmdN1t).
match goal with |- crealizes _ _ (t_exit (Z_to_bv 64 ?c) _) => let c' := eval cbv in c in change c with c' | _ => idtac end.
exact (src0_exit_cf _ _ mSN1t mDN1t 0 HS' ltac:(lia) r1E1_exit_N1t HhN1t HlzN1t).
* cto_free_buf HS HMR Hcm (proj1 HRE).
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r1E1_N1f msx) in HS end.
lazymatch type of HS with st_ok _ ?Ec _ ?msx =>
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS) as Hr10;
eapply (free_site_cf src0_msyms API AX TBL (FCF _) Ec r1E1_N1f msx mD4 L3 A3 bq4 cap0 b4 (-128) src0_keep [] 76 r1E1_LN1f r1E1_RSN1f RA_sf _
HS ltac:(drv_anch) r1E1_site_N1f ltac:(vm_compute; reflexivity) r1E1_statics_N1f HMR HW4 HB4 Hid4 Hin4);
[ rewrite Hr10; match goal with |- sv_denot _ ?x = _ => replace x with (SOff 14 0) by (symmetry; first [exact (proj1 r1E1_N_facts) | exact (proj1 (proj2 r1E1_N_facts)) | exact (proj1 (proj2 (proj2 r1E1_N_facts))) | exact (proj2 (proj2 (proj2 r1E1_N_facts)))]) end;
cbn [sv_denot]; rewrite Z.add_0_r, Hpb4, <- (proj1 (proj2 HRE)), Z_to_bv_bv_unsigned; reflexivity
| exact Hb4
| intros kb sz [ ]
| clear Hr10 ]
end.
intros AN1f LN1f mSN1f mDN1f gN1f HS' ?HSA HMR' HWN1f HBN1f HmdN1f HstabN1f HhiN1f HbkN1f _.
apply (md_invX_ex _ _ _ Hmd4) in HmdN1f.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (HhN1f & HlzN1f & _).
pose proof (md_invX_ch1 _ _ HmdN1f) as HchN1f.
rewrite <- (md_invX_fs _ _ HmdN1f).
match goal with |- crealizes _ _ (t_exit (Z_to_bv 64 ?c) _) => let c' := eval cbv in c in change c with c' | _ => idtac end.
exact (src0_exit_cf _ _ mSN1f mDN1f 0 HS' ltac:(lia) r1E1_exit_N1f HhN1f HlzN1f).
Qed.
End d.
End a.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
