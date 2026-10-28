(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0p YK0i YK0j YK14 YK1b YK1a YK15 YK0l YK0o YK0q YQ0k YN06 YN02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ0a YQ04 YQ0d YQ05 YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e YP07.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH05 UH07 UH06 UO3p UO3k UO3q UO3r UO3j UO3o.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO04 YL05 YL01 UL06 YL0b YL0c YL02 YL08 YL00 YL03 YL0a YL07 YL04 YL0e UL0g UL0i UL0p UL0n UL0k UL0o.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition r1E1_Q : sstate := Eval vm_compute in (sQ1k 1).
Definition r1E1_QE : sstate := Eval vm_compute in (add_cond r1E1_Q cond_PL0).
Definition r1E1_L1 : sstate := Eval vm_compute in (runto_ LIBPC r1E1_QE).
Definition r1E1_LL1 : list (nat * YQ0b.region) := Eval vm_compute in (drop_base 47 (drop_base 14 (precall ubs2_keep (-208) LIB_STACK_RGB (ss_mem r1E1_L1)))).
Lemma r1E1_site_L1 : lib_site_check ubs2_msyms LIBPC RA_LIB LIB_STACK_RGB r1E1_L1 (-208) ubs2_keep [] 48 r1E1_LL1 = true.
Proof. vm_compute. reflexivity. Qed.
Definition r1E1_RSL1 : smem := Eval vm_compute in (match drv_add_statics ubs2_msyms (map snd r1E1_LL1) 64 with Some x => x | None => [] end).
Lemma r1E1_statics_L1 : drv_add_statics ubs2_msyms (map snd r1E1_LL1) (48 + 16) = Some r1E1_RSL1.
Proof. vm_compute. reflexivity. Qed.
Definition r1E1_P1 : sstate := Eval vm_compute in (mkSS RA_LIB (ss_regs (lib_post_state RA_LIB r1E1_L1 48 r1E1_RSL1)) r1E1_RSL1 None (ss_facts r1E1_L1)).
Lemma r1E1_L1_facts : sr_get (ss_regs r1E1_L1) 10%bv = SLit EMPTY /\ sr_get (ss_regs r1E1_L1) 11%bv = add0 sv_pl00 /\ sr_get (ss_regs r1E1_L1) 8%bv = sv_pl00.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition r1E1_I1 : sstate := Eval vm_compute in (match pf0_check 65 r1E1_P1 RET_PF with Some (s, _) => s | None => r1E1_P1 end).

Definition r1E1_N1 : sstate := Eval vm_compute in (run_ r1E1_I1).
Definition r1E1_N1t : sstate := Eval vm_compute in (runto_ ubs2_A_free (add_cond r1E1_N1 cond_CMt)).
Definition r1E1_LN1t : list (nat * YQ0b.region) := Eval vm_compute in (precall ubs2_keep (-128) ALLOC_STACK (ss_mem r1E1_N1t)).
Lemma r1E1_site_N1t : site_check ubs2_msyms r1E1_N1t ubs2_A_free RA_sf (-128) ubs2_keep [] 76 r1E1_LN1t = true.
Proof. vm_compute. reflexivity. Qed.
Definition r1E1_RSN1t : smem := Eval vm_compute in (match drv_add_statics ubs2_msyms (map snd r1E1_LN1t) 92 with Some x => x | None => [] end).
Lemma r1E1_statics_N1t : drv_add_statics ubs2_msyms (map snd r1E1_LN1t) (76 + 16) = Some r1E1_RSN1t.
Proof. vm_compute. reflexivity. Qed.
Lemma r1E1_exit_N1t : exit_run_check ubs2segs ubs2tbl (post_state r1E1_N1t RA_sf 76 r1E1_RSN1t) 0 = true.
Proof. vm_compute. reflexivity. Qed.
Definition r1E1_N1f : sstate := Eval vm_compute in (runto_ ubs2_A_free (add_cond r1E1_N1 cond_CMf)).
Definition r1E1_LN1f : list (nat * YQ0b.region) := Eval vm_compute in (precall ubs2_keep (-128) ALLOC_STACK (ss_mem r1E1_N1f)).
Lemma r1E1_site_N1f : site_check ubs2_msyms r1E1_N1f ubs2_A_free RA_sf (-128) ubs2_keep [] 76 r1E1_LN1f = true.
Proof. vm_compute. reflexivity. Qed.
Definition r1E1_RSN1f : smem := Eval vm_compute in (match drv_add_statics ubs2_msyms (map snd r1E1_LN1f) 92 with Some x => x | None => [] end).
Lemma r1E1_statics_N1f : drv_add_statics ubs2_msyms (map snd r1E1_LN1f) (76 + 16) = Some r1E1_RSN1f.
Proof. vm_compute. reflexivity. Qed.
Lemma r1E1_exit_N1f : exit_run_check ubs2segs ubs2tbl (post_state r1E1_N1f RA_sf 76 r1E1_RSN1f) 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma r1E1_N_facts : sr_get (ss_regs r1E1_N1t) 10%bv = SOff 14 0 /\ sr_get (ss_regs r1E1_N1f) 10%bv = SOff 14 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
Section b.
Variable API : AllocAPI ubs2_msyms.
Hypothesis AX : AllocExtra ubs2_msyms (aa_MR API).
Hypothesis LIB : lib_contract_all ubs2_msyms API LIBPC RA_LIB EMPTY LIB_STACK_RGB.
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
Let lib_stk_pos : 0 <= LIB_STACK_RGB. Proof. unfold LIB_STACK_RGB. lia. Qed.
Ltac to_free_buf HS HMR Hcm Hed :=
let HF := fresh "HF" in
first
[ sym_assume_with ubs2tbl_ok HS true;
[ lazymatch type of HS with st_ok _ ?E _ _ =>
change (sv_denot E (SLit 0)) with (Z_to_bv 64 0); etransitivity; [apply (bltz_b1s E data); [exact Hed | unfold dlen in *; lia] | exact Hcm] end
| ]
| sym_assume_with ubs2tbl_ok HS false;
[ lazymatch type of HS with st_ok _ ?E _ _ =>
change (sv_denot E (SLit 0)) with (Z_to_bv 64 0); etransitivity; [apply (bltz_b1s E data); [exact Hed | unfold dlen in *; lia] | exact Hcm] end
| ] ];
drv_run_to_with ubs2tbl_ok HS ubs2_A_free HF;
lazymatch type of HS with st_ok _ ?E _ _ =>
drv_mr (MR_after_frame ubs2_msyms (aa_MR API) (aa_laws API) AX) ubs2_keep E HS HF HMR end.
Theorem ubs2_run_1E1 : forall E ms md,
run_env E data (ptr_addr L' b0) ->
st_ok ubs2segs E sQ1 ms -> aa_MR API L' A' (ms_mem ms) md -> md_inv fs md ->
realizes ubs2segs (mkCfg ms md) (leaf_shape data fs (DL_run b0 cap0 None, A')).
Proof.
intros E ms md HE HS HMR Hmd.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hlz & _).
assert (Hin : In (b0, cap0) (user_blocks A')) by (rewrite Hub; left; reflexivity).
pose proof (mr_blocks _ _ (aa_laws API) L' A' (ms_mem ms) md b0 cap0 0 HMR Hin ltac:(lia)) as (_ & Hq1 & Hq2 & _).
assert (Hac : alloc_ceiling < 2 ^ 63) by (pose proof YN05.alloc_ceiling_val; lia).
unfold dlen in Hok, HLc. pose proof (config_len_bound data) as Hclb.
destruct (list_len2 data ltac:(lia)) as (d0 & d1 & rest & Ed).
assert (Hplv : payload_len data = Z.of_nat (length data) - 6 - config_len data) by reflexivity.
pose proof HE as HE0. destruct HE0 as (HEd & HE13 & HE26 & HE46 & HAN).
apply (ubs2_Q_calls data cap0 L' b0 Hcap0 Hok HLc E ms HE Hcl) in HS. rewrite Hcalls in HS. change (st_ok ubs2segs E r1E1_Q ms) in HS.
let v := eval cbv [sv_pl00 sv_pl add0 sv_cl sv_b1s] in sv_pl00 in
assert (Hpl00 : U E v = payload_len data) by (eapply U_pl00; eauto; lia).
apply (st_ok_add_cond ubs2segs E r1E1_Q ms BC_EQ (ltac:(let v := eval cbv [sv_pl00 sv_pl add0 sv_cl sv_b1s] in sv_pl00 in exact v)) (SLit 0)) in HS.
2:{ rewrite branch_eq_U, Hpl00, U_SLit, Hpl. reflexivity. }
change (st_ok ubs2segs E r1E1_QE ms) in HS.
apply (rz_conseq _ _ (wr ch_stdout line0 (ex 0 fs)) _).
2:{ cbn [fst snd leaf_shape]. rewrite Hcalls.
change (repeat line0 1) with [line0]. cbn [concat]. rewrite app_nil_r. apply t_eq_refl. }
assert (HRE : run_env E data (ptr_addr L' b0)) by exact HE.
pose proof Hin as Hin2. assert (Hpb2 : ptr_addr L' b0 = ptr_addr L' b0) by reflexivity.
drv_run_to_with ubs2tbl_ok HS LIBPC HF.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok ubs2segs Ec r1E1_L1 msx) in HS;
drv_mr (MR_after_frame ubs2_msyms (aa_MR API) (aa_laws API) AX) ubs2_keep Ec HS HF HMR end.
lazymatch type of HS with st_ok _ ?Ec _ ?msx =>
pose proof (st_ok_reg ubs2segs _ _ _ 10%bv HS) as Hr10; pose proof (st_ok_reg ubs2segs _ _ _ 11%bv HS) as Hr11;
rewrite (proj1 r1E1_L1_facts) in Hr10; rewrite (proj1 (proj2 r1E1_L1_facts)) in Hr11;
eapply (lib_site ubs2_msyms API AX LIBPC RA_LIB EMPTY LIB_STACK_RGB LIB lib_stk_pos FRM Ec r1E1_L1 msx md L' A'
EMPTY (payload_len data) (-208) ubs2_keep [] 48 r1E1_LL1 r1E1_RSL1 _
HS ltac:(drv_anch) r1E1_site_L1 r1E1_statics_L1 HMR HW HB Hid);
[ rewrite Hr10; reflexivity
| rewrite Hr11; rewrite (denot_lit_U Ec (add0 sv_pl00)), U_add0, (U_pl00 Ec data d0 d1 rest); [rewrite Hpl; reflexivity | exact (proj1 HRE) | exact Ed | exact (proj1 (proj2 (proj2 HRE))) | lia]
| left; split; [exact Hpl | reflexivity]
| intros kb sz [ ]
| clear Hr10 Hr11 ]
end.
intros fx4 A3 L3 mS4 mD4 g4 HS' ?HSA FRM' HMR' HW4 HB4 Hid4 Hmd4 Hstab4 Hhi4 Hbk4.
apply (md_inv_ex _ _ _ Hmd) in Hmd4.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (Hh4 & Hlz4 & _).
destruct (Hstab4 _ _ Hin2) as (bq4 & Hin4 & Hpb4). try rewrite Hpb2 in Hpb4.
clear HS HMR Hhi4 Hbk4 Hstab4. rename HS' into HS. rename HMR' into HMR. clear FRM; try clear fx. rename FRM' into FRM.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok ubs2segs Ec r1E1_P1 msx) in HS end.
renv_sync HS HRE.
pose proof (md_inv_ch1 _ _ Hmd4) as Hch4.
unfold wr at 1.
drv_printf0 HS Hch4 65%nat RET_PF HF.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok ubs2segs Ec r1E1_I1 msx) in HS;
drv_mr (MR_after_frame ubs2_msyms (aa_MR API) (aa_laws API) AX) ubs2_keep Ec HS HF HMR end.
renv_sync HS HRE.
drv_run_with ubs2tbl_ok HS HF.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok ubs2segs Ec r1E1_N1 msx) in HS;
drv_mr (MR_after_frame ubs2_msyms (aa_MR API) (aa_laws API) AX) ubs2_keep Ec HS HF HMR end.
unfold ex.
destruct (count_mode data) eqn:Hcm.
* to_free_buf HS HMR Hcm (proj1 HRE).
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok ubs2segs Ec r1E1_N1t msx) in HS end.
lazymatch type of HS with st_ok _ ?Ec _ ?msx =>
pose proof (st_ok_reg ubs2segs _ _ _ 10%bv HS) as Hr10;
eapply (free_site ubs2_msyms API AX Ec r1E1_N1t msx mD4 L3 A3 bq4 cap0 (-128) ubs2_keep [] 76 r1E1_LN1t r1E1_RSN1t RA_sf _
HS ltac:(drv_anch) r1E1_site_N1t r1E1_statics_N1t HMR HW4 HB4 Hid4 Hin4);
[ rewrite Hr10; match goal with |- sv_denot _ ?x = _ => replace x with (SOff 14 0) by (symmetry; first [exact (proj1 r1E1_N_facts) | exact (proj1 (proj2 r1E1_N_facts)) | exact (proj1 (proj2 (proj2 r1E1_N_facts))) | exact (proj2 (proj2 (proj2 r1E1_N_facts)))]) end;
cbn [sv_denot]; rewrite Z.add_0_r, Hpb4, <- (proj1 (proj2 HRE)), Z_to_bv_bv_unsigned; reflexivity
| intros kb sz [ ]
| clear Hr10 ]
end.
intros AN1t LN1t mSN1t mDN1t gN1t trN1t HS' ?HSA HMR' HWN1t HBN1t HmdN1t HpathN1t HubN1t HstabN1t HhiN1t HbkN1t.
apply (md_inv_ex _ _ _ Hmd4) in HmdN1t.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (HhN1t & HlzN1t & _).
pose proof (md_inv_ch1 _ _ HmdN1t) as HchN1t.
rewrite <- (md_inv_fs _ _ HmdN1t).
match goal with |- realizes _ _ (t_exit (Z_to_bv 64 ?c) _) => let c' := eval cbv in c in change c with c' | _ => idtac end.
exact (ubs2_exit _ _ mSN1t mDN1t 0 HS' ltac:(lia) r1E1_exit_N1t HhN1t HlzN1t).
* to_free_buf HS HMR Hcm (proj1 HRE).
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok ubs2segs Ec r1E1_N1f msx) in HS end.
lazymatch type of HS with st_ok _ ?Ec _ ?msx =>
pose proof (st_ok_reg ubs2segs _ _ _ 10%bv HS) as Hr10;
eapply (free_site ubs2_msyms API AX Ec r1E1_N1f msx mD4 L3 A3 bq4 cap0 (-128) ubs2_keep [] 76 r1E1_LN1f r1E1_RSN1f RA_sf _
HS ltac:(drv_anch) r1E1_site_N1f r1E1_statics_N1f HMR HW4 HB4 Hid4 Hin4);
[ rewrite Hr10; match goal with |- sv_denot _ ?x = _ => replace x with (SOff 14 0) by (symmetry; first [exact (proj1 r1E1_N_facts) | exact (proj1 (proj2 r1E1_N_facts)) | exact (proj1 (proj2 (proj2 r1E1_N_facts))) | exact (proj2 (proj2 (proj2 r1E1_N_facts)))]) end;
cbn [sv_denot]; rewrite Z.add_0_r, Hpb4, <- (proj1 (proj2 HRE)), Z_to_bv_bv_unsigned; reflexivity
| intros kb sz [ ]
| clear Hr10 ]
end.
intros AN1f LN1f mSN1f mDN1f gN1f trN1f HS' ?HSA HMR' HWN1f HBN1f HmdN1f HpathN1f HubN1f HstabN1f HhiN1f HbkN1f.
apply (md_inv_ex _ _ _ Hmd4) in HmdN1f.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (HhN1f & HlzN1f & _).
pose proof (md_inv_ch1 _ _ HmdN1f) as HchN1f.
rewrite <- (md_inv_fs _ _ HmdN1f).
match goal with |- realizes _ _ (t_exit (Z_to_bv 64 ?c) _) => let c' := eval cbv in c in change c with c' | _ => idtac end.
exact (ubs2_exit _ _ mSN1f mDN1f 0 HS' ltac:(lia) r1E1_exit_N1f HhN1f HlzN1f).
Qed.
End b.
End a.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
