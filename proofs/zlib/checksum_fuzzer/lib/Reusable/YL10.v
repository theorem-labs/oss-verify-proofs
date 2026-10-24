(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11 YK0o YK0h YK0i YK14 YK1b YK1a YK15 YK0k YK0n YK0p YP0n YM06 YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i YO0f YO0x YO0d YO0e YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH00 YH01 YH03 YH02 YN3e YN35 YN3f YN3g YN34 YN3d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN03 YL07 YL01 YL08 YL0d YL0e YL02 YL0a YL00 YL04 YL0c YL09 YL05 YL0g YL0k YL0m YL0u YL0r YL0o YL0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YI06 YI16 YI14 YI5b YI5c YL0i YL06 YL03 YL0l YL0t.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Definition r0E1_Q : sstate := sQ0.
Definition r0E1_QE : sstate := Eval vm_compute in (add_cond r0E1_Q cond_PL0).
Definition r0E1_L1 : sstate := Eval vm_compute in (runto_ LIBPC r0E1_QE).
Definition r0E1_LL1 : list (nat * YP09.region) := Eval vm_compute in (drop_base 47 (drop_base 14 (precall src0_keep (-208) LIB_STACK (ss_mem r0E1_L1)))).
Lemma r0E1_site_L1 : lib_site_check src0_msyms LIBPC RA_LIB LIB_STACK r0E1_L1 (-208) src0_keep [] 48 r0E1_LL1 = true.
Proof. vm_compute. reflexivity. Qed.
Definition r0E1_RSL1 : smem := Eval vm_compute in (match drv_add_statics src0_msyms (map snd r0E1_LL1) 64 with Some x => x | None => [] end).
Lemma r0E1_statics_L1 : drv_add_statics src0_msyms (map snd r0E1_LL1) (48 + 16) = Some r0E1_RSL1.
Proof. vm_compute. reflexivity. Qed.
Definition r0E1_P1 : sstate := Eval vm_compute in (mkSS RA_LIB (ss_regs (lib_post_state RA_LIB r0E1_L1 48 r0E1_RSL1)) r0E1_RSL1 None (ss_facts r0E1_L1)).
Lemma r0E1_L1_facts : sr_get (ss_regs r0E1_L1) 10%bv = SLit EMPTY /\ sr_get (ss_regs r0E1_L1) 11%bv = add0 sv_pl00 /\ sr_get (ss_regs r0E1_L1) 8%bv = sv_pl00.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition r0E1_I1 : sstate := Eval vm_compute in (match pf0_check 65 r0E1_P1 RET_PF with Some (s, _) => s | None => r0E1_P1 end).
Lemma r0E1_ck_I1 : pf0_check 65 r0E1_P1 RET_PF = Some (r0E1_I1, [48; 10]).
Proof. vm_compute. reflexivity. Qed.
Definition r0E1_N1 : sstate := Eval vm_compute in (run_ r0E1_I1).
Definition r0E1_N1t : sstate := Eval vm_compute in (runto_ src0_A_free (add_cond r0E1_N1 cond_CMt)).
Definition r0E1_LN1t : list (nat * YP09.region) := Eval vm_compute in (precall src0_keep (-128) ALLOC_STACK (ss_mem r0E1_N1t)).
Lemma r0E1_site_N1t : site_check src0_msyms r0E1_N1t src0_A_free RA_sf (-128) src0_keep [] 76 r0E1_LN1t = true.
Proof. vm_compute. reflexivity. Qed.
Definition r0E1_RSN1t : smem := Eval vm_compute in (match drv_add_statics src0_msyms (map snd r0E1_LN1t) 92 with Some x => x | None => [] end).
Lemma r0E1_statics_N1t : drv_add_statics src0_msyms (map snd r0E1_LN1t) (76 + 16) = Some r0E1_RSN1t.
Proof. vm_compute. reflexivity. Qed.
Lemma r0E1_exit_N1t : exit_run_check src0segs src0tbl (post_state r0E1_N1t RA_sf 76 r0E1_RSN1t) 0 = true.
Proof. vm_compute. reflexivity. Qed.
Definition r0E1_N1f : sstate := Eval vm_compute in (runto_ src0_A_free (add_cond r0E1_N1 cond_CMf)).
Definition r0E1_LN1f : list (nat * YP09.region) := Eval vm_compute in (precall src0_keep (-128) ALLOC_STACK (ss_mem r0E1_N1f)).
Lemma r0E1_site_N1f : site_check src0_msyms r0E1_N1f src0_A_free RA_sf (-128) src0_keep [] 76 r0E1_LN1f = true.
Proof. vm_compute. reflexivity. Qed.
Definition r0E1_RSN1f : smem := Eval vm_compute in (match drv_add_statics src0_msyms (map snd r0E1_LN1f) 92 with Some x => x | None => [] end).
Lemma r0E1_statics_N1f : drv_add_statics src0_msyms (map snd r0E1_LN1f) (76 + 16) = Some r0E1_RSN1f.
Proof. vm_compute. reflexivity. Qed.
Lemma r0E1_exit_N1f : exit_run_check src0segs src0tbl (post_state r0E1_N1f RA_sf 76 r0E1_RSN1f) 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma r0E1_N_facts : sr_get (ss_regs r0E1_N1t) 10%bv = SOff 14 0 /\ sr_get (ss_regs r0E1_N1f) 10%bv = SOff 14 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
Section d.
Variable API : AllocAPI src0_msyms.
Hypothesis AX : AllocExtra src0_msyms (aa_MR API).
Hypothesis LIBX : lib_contract_x_all src0_msyms API LIBPC RA_LIB EMPTY LIB_STACK.
Hypothesis FRM : frm_zero fp_csr.
Variables (data : list byte) (fs : Fs) (cap0 : Z) (L' : layout) (A' : astate) (b0 : sptr).
Hypothesis Hub : user_blocks A' = [(b0, cap0)].
Hypothesis Hcap0 : 65536 <= cap0 <= 67108864.
Hypothesis HW : WF A'.
Hypothesis HB : bounded A'.
Hypothesis Hid : st_init_done A' = true.
Hypothesis Hok : 6 + config_len data <= dlen data.
Hypothesis HLc : dlen data < cap0.
Hypothesis Hcl : config_len data = 0.
Hypothesis Hcalls : calls data = 1%nat.
Hypothesis Hpl : payload_len data = 0.
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
Theorem src0_runX_0E1 : forall E ms md (b : rbound),
run_env E data (ptr_addr L' b0) -> env_top E ->
st_ok src0segs E sQ0 ms -> aa_MR API L' A' (ms_mem ms) md -> md_invX fs md ->
res_ok A' b -> room_calls (payload_len data) (calls data) b ->
realizes src0segs (mkCfg ms md) (leaf_shapeX data fs (DL_run b0 cap0 None, A')).
Proof.
intros E ms md b HE HT HS HMR Hmd HRb HRC.
pose proof HRC as HRC0. rewrite Hcalls in HRC. cbn [room_calls] in HRC.
pose proof (payload_len_length data Hok) as HplLen. pose proof (payload_nil data Hok Hpl) as HplNil.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hlz & _).
assert (Hin : In (b0, cap0) (user_blocks A')) by (rewrite Hub; left; reflexivity).
pose proof (mr_blocks _ _ (aa_laws API) L' A' (ms_mem ms) md b0 cap0 0 HMR Hin ltac:(lia)) as (_ & Hq1 & Hq2 & _).
assert (Hac : alloc_ceiling < 2 ^ 63) by (pose proof YM05.alloc_ceiling_val; lia).
unfold dlen in Hok, HLc. pose proof (config_len_bound data) as Hclb.
destruct (list_len2 data ltac:(lia)) as (d0 & d1 & rest & Ed).
assert (Hplv : payload_len data = Z.of_nat (length data) - 6 - config_len data) by reflexivity.
pose proof HE as HE0. destruct HE0 as (HEd & HE13 & HE26 & HE46 & HAN).
change (st_ok src0segs E r0E1_Q ms) in HS.
let v := eval cbv [sv_pl00 sv_pl add0 sv_cl sv_b1s] in sv_pl00 in
assert (Hpl00 : U E v = payload_len data) by (eapply U_pl00; eauto; lia).
apply (st_ok_add_cond src0segs E r0E1_Q ms BC_EQ (ltac:(let v := eval cbv [sv_pl00 sv_pl add0 sv_cl sv_b1s] in sv_pl00 in exact v)) (SLit 0)) in HS.
2:{ rewrite branch_eq_U, Hpl00, U_SLit, Hpl. reflexivity. }
change (st_ok src0segs E r0E1_QE ms) in HS.
rewrite <- (md_invX_fs _ _ Hmd).
apply (rz_conseq _ _ (LIBK (payload data) (m_fs md) (fun l => wr ch_stdout line0 (lib_iter (payload data) 0 (run_tail 0) (ll_fs l)))) _).
2:{ cbn [fst snd leaf_shapeX run_shape]. rewrite Hcalls. apply t_eq_refl. }
assert (HRE : run_env E data (ptr_addr L' b0)) by exact HE.
pose proof Hin as Hin2. assert (Hpb2 : ptr_addr L' b0 = ptr_addr L' b0) by reflexivity.
pose proof HRb as HRbL. pose proof HRC as HRC1.
drv_run_to_with src0tbl_ok HS LIBPC HF.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r0E1_L1 msx) in HS;
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep Ec HS HF HMR end.
lazymatch type of HS with st_ok _ ?Ec _ ?msx =>
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS) as Hr10; pose proof (st_ok_reg src0segs _ _ _ 11%bv HS) as Hr11;
rewrite (proj1 r0E1_L1_facts) in Hr10; rewrite (proj1 (proj2 r0E1_L1_facts)) in Hr11;
try rewrite <- (md_invX_fs _ _ Hmd);
assert (CK1 : env_check (ss_mem r0E1_L1) = true) by (vm_compute; reflexivity);
eapply (lib_site_x src0_msyms API AX LIBPC RA_LIB EMPTY LIB_STACK LIBX lib_stk_pos FRM Ec r0E1_L1 msx md L' A'
EMPTY (payload_len data) (payload data) _ (-208) src0_keep [] 48 r0E1_LL1 r0E1_RSL1 _
HS ltac:(drv_anch) r0E1_site_L1 r0E1_statics_L1 HMR HW HB Hid);
[ rewrite Hr10; reflexivity
| rewrite Hr11; rewrite (denot_lit_U Ec (add0 sv_pl00)), U_add0, (U_pl00 Ec data d0 d1 rest); [rewrite Hpl; reflexivity | exact (proj1 HRE) | exact Ed | exact (proj1 (proj2 (proj2 HRE))) | lia]
| left; split; [exact Hpl | reflexivity]
| intros kb sz [ ]
| exact HplLen
| rewrite HplNil; apply (blk_data_nil src0_msyms)
| exact HRbL
| exact (proj1 HRC1)
| split; [|split]; [ exact (proj1 (src0_env_rom _ (env_of_st_ok src0segs _ _ _ HS CK1)))
| exact (proj2 (src0_env_rom _ (env_of_st_ok src0segs _ _ _ HS CK1)))
| exact (md_invX_names _ _ Hmd) ]
| exact (md_invX_free _ _ Hmd)
| exact (md_invX_sorted _ _ Hmd)
| unfold env_top in HT; lia
| clear Hr10 Hr11 CK1 ]
end.
intros l4 fx4 A3 L3 mS4 mD4 g4 HS' ?HSA FRM' HMR' HW4 HB4 Hid4 Hmd4 Hstab4 Hhi4 Hbk4 Hret4 Hout4 Hsort4 HSN4 HRES4 Hplk4. cbv beta. cbn [lib_iter run_tail].
pose proof (md_invX_lib _ _ _ _ _ Hmd Hmd4 HSN4 Hsort4) as HmdX4. clear Hmd4. rename HmdX4 into Hmd4.
pose proof (proj2 HRC1) as HRC2.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (Hh4 & Hlz4 & _).
destruct (Hstab4 _ _ Hin2) as (bq4 & Hin4 & Hpb4). try rewrite Hpb2 in Hpb4.
clear HS HMR Hhi4 Hbk4 Hstab4. rename HS' into HS. rename HMR' into HMR. clear FRM; try clear fx. rename FRM' into FRM.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r0E1_P1 msx) in HS end.
renv_sync HS HRE. etop_sync HS HT.
pose proof (md_invX_ch1 _ _ Hmd4) as Hch4.
unfold wr at 1.
drv_printf0 HS Hch4 65%nat RET_PF HF.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r0E1_I1 msx) in HS;
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep Ec HS HF HMR end.
renv_sync HS HRE. etop_sync HS HT.
drv_run_with src0tbl_ok HS HF.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r0E1_N1 msx) in HS;
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep Ec HS HF HMR end.
unfold ex.
destruct (count_mode data) eqn:Hcm.
* to_free_buf HS HMR Hcm (proj1 HRE).
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r0E1_N1t msx) in HS end.
lazymatch type of HS with st_ok _ ?Ec _ ?msx =>
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS) as Hr10;
eapply (free_site src0_msyms API AX Ec r0E1_N1t msx mD4 L3 A3 bq4 cap0 (-128) src0_keep [] 76 r0E1_LN1t r0E1_RSN1t RA_sf _
HS ltac:(drv_anch) r0E1_site_N1t r0E1_statics_N1t HMR HW4 HB4 Hid4 Hin4);
[ rewrite Hr10; match goal with |- sv_denot _ ?x = _ => replace x with (SOff 14 0) by (symmetry; first [exact (proj1 r0E1_N_facts) | exact (proj1 (proj2 r0E1_N_facts)) | exact (proj1 (proj2 (proj2 r0E1_N_facts))) | exact (proj2 (proj2 (proj2 r0E1_N_facts)))]) end;
cbn [sv_denot]; rewrite Z.add_0_r, Hpb4, <- (proj1 (proj2 HRE)), Z_to_bv_bv_unsigned; reflexivity
| intros kb sz [ ]
| clear Hr10 ]
end.
intros AN1t LN1t mSN1t mDN1t gN1t trN1t HS' ?HSA HMR' HWN1t HBN1t HmdN1t HpathN1t HubN1t HstabN1t HhiN1t HbkN1t.
apply (md_invX_ex _ _ _ Hmd4) in HmdN1t.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (HhN1t & HlzN1t & _).
pose proof (md_invX_ch1 _ _ HmdN1t) as HchN1t.
rewrite <- (md_invX_fs _ _ HmdN1t).
match goal with |- realizes _ _ (t_exit (Z_to_bv 64 ?c) _) => let c' := eval cbv in c in change c with c' | _ => idtac end.
exact (src0_exit _ _ mSN1t mDN1t 0 HS' ltac:(lia) r0E1_exit_N1t HhN1t HlzN1t).
* to_free_buf HS HMR Hcm (proj1 HRE).
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok src0segs Ec r0E1_N1f msx) in HS end.
lazymatch type of HS with st_ok _ ?Ec _ ?msx =>
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS) as Hr10;
eapply (free_site src0_msyms API AX Ec r0E1_N1f msx mD4 L3 A3 bq4 cap0 (-128) src0_keep [] 76 r0E1_LN1f r0E1_RSN1f RA_sf _
HS ltac:(drv_anch) r0E1_site_N1f r0E1_statics_N1f HMR HW4 HB4 Hid4 Hin4);
[ rewrite Hr10; match goal with |- sv_denot _ ?x = _ => replace x with (SOff 14 0) by (symmetry; first [exact (proj1 r0E1_N_facts) | exact (proj1 (proj2 r0E1_N_facts)) | exact (proj1 (proj2 (proj2 r0E1_N_facts))) | exact (proj2 (proj2 (proj2 r0E1_N_facts)))]) end;
cbn [sv_denot]; rewrite Z.add_0_r, Hpb4, <- (proj1 (proj2 HRE)), Z_to_bv_bv_unsigned; reflexivity
| intros kb sz [ ]
| clear Hr10 ]
end.
intros AN1f LN1f mSN1f mDN1f gN1f trN1f HS' ?HSA HMR' HWN1f HBN1f HmdN1f HpathN1f HubN1f HstabN1f HhiN1f HbkN1f.
apply (md_invX_ex _ _ _ Hmd4) in HmdN1f.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (HhN1f & HlzN1f & _).
pose proof (md_invX_ch1 _ _ HmdN1f) as HchN1f.
rewrite <- (md_invX_fs _ _ HmdN1f).
match goal with |- realizes _ _ (t_exit (Z_to_bv 64 ?c) _) => let c' := eval cbv in c in change c with c' | _ => idtac end.
exact (src0_exit _ _ mSN1f mDN1f 0 HS' ltac:(lia) r0E1_exit_N1f HhN1f HlzN1f).
Qed.
End d.
End a.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
