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
Definition r1M1_Q : sstate := Eval vm_compute in (sQ1k 1).
Definition r1M1_ME : sstate := Eval vm_compute in (runto_ ubs2_A_malloc (add_cond r1M1_Q cond_PL1)).
Definition r1M1_LME : list (nat * YQ0b.region) := Eval vm_compute in (drop_base 47 (drop_base 14 (precall ubs2_keep (-208) ALLOC_STACK (ss_mem r1M1_ME)))).
Lemma r1M1_site_ME : site_check ubs2_msyms r1M1_ME ubs2_A_malloc RA_ME (-208) ubs2_keep [] 48 r1M1_LME = true.
Proof. vm_compute. reflexivity. Qed.
Definition r1M1_RSME : smem := Eval vm_compute in (match drv_add_statics ubs2_msyms (map snd r1M1_LME) 64 with Some x => x | None => [] end).
Lemma r1M1_statics_ME : drv_add_statics ubs2_msyms (map snd r1M1_LME) (48 + 16) = Some r1M1_RSME.
Proof. vm_compute. reflexivity. Qed.
Definition r1M1_MEp : sstate := Eval vm_compute in (post_state r1M1_ME RA_ME 48 r1M1_RSME).
Lemma r1M1_ME_facts : ss_pc r1M1_ME = ubs2_A_malloc /\ sr_get (ss_regs r1M1_ME) 10%bv = add0 sv_pl00 /\ sr_get (ss_regs r1M1_MEp) 10%bv = SOff 52 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition r1M1_MEn : sstate := Eval vm_compute in (setreg_ 10%bv (SLit 0) r1M1_MEp).
Definition r1M1_N0 : sstate := Eval vm_compute in (run_ r1M1_MEn).
Definition r1M1_N0t : sstate := Eval vm_compute in (runto_ ubs2_A_free (add_cond r1M1_N0 cond_CMt)).
Definition r1M1_LN0t : list (nat * YQ0b.region) := Eval vm_compute in (precall ubs2_keep (-128) ALLOC_STACK (ss_mem r1M1_N0t)).
Lemma r1M1_site_N0t : site_check ubs2_msyms r1M1_N0t ubs2_A_free RA_sf (-128) ubs2_keep [] 65 r1M1_LN0t = true.
Proof. vm_compute. reflexivity. Qed.
Definition r1M1_RSN0t : smem := Eval vm_compute in (match drv_add_statics ubs2_msyms (map snd r1M1_LN0t) 81 with Some x => x | None => [] end).
Lemma r1M1_statics_N0t : drv_add_statics ubs2_msyms (map snd r1M1_LN0t) (65 + 16) = Some r1M1_RSN0t.
Proof. vm_compute. reflexivity. Qed.
Lemma r1M1_exit_N0t : exit_run_check ubs2segs ubs2tbl (post_state r1M1_N0t RA_sf 65 r1M1_RSN0t) 0 = true.
Proof. vm_compute. reflexivity. Qed.
Definition r1M1_N0f : sstate := Eval vm_compute in (runto_ ubs2_A_free (add_cond r1M1_N0 cond_CMf)).
Definition r1M1_LN0f : list (nat * YQ0b.region) := Eval vm_compute in (precall ubs2_keep (-128) ALLOC_STACK (ss_mem r1M1_N0f)).
Lemma r1M1_site_N0f : site_check ubs2_msyms r1M1_N0f ubs2_A_free RA_sf (-128) ubs2_keep [] 65 r1M1_LN0f = true.
Proof. vm_compute. reflexivity. Qed.
Definition r1M1_RSN0f : smem := Eval vm_compute in (match drv_add_statics ubs2_msyms (map snd r1M1_LN0f) 81 with Some x => x | None => [] end).
Lemma r1M1_statics_N0f : drv_add_statics ubs2_msyms (map snd r1M1_LN0f) (65 + 16) = Some r1M1_RSN0f.
Proof. vm_compute. reflexivity. Qed.
Lemma r1M1_exit_N0f : exit_run_check ubs2segs ubs2tbl (post_state r1M1_N0f RA_sf 65 r1M1_RSN0f) 2 = true.
Proof. vm_compute. reflexivity. Qed.
Definition r1M1_MC : sstate := Eval vm_compute in (runto_ ubs2_A_memcpy (add_atom r1M1_MEp 52 blkq_fact)).
Lemma r1M1_ck_MC : memcpy_check r1M1_MC RA_MC 52 65 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma r1M1_MC_facts : sr_get (ss_regs r1M1_MC) 10%bv = SOff 52 0 /\ sr_get (ss_regs r1M1_MC) 11%bv = SOff 47 4 /\ sr_get (ss_regs r1M1_MC) 12%bv = add0 sv_pl00.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition r1M1_MCp : sstate := Eval vm_compute in (memcpy_post r1M1_MC RA_MC 65).
Definition r1M1_L1 : sstate := Eval vm_compute in (runto_ LIBPC r1M1_MCp).
Definition r1M1_LL1 : list (nat * YQ0b.region) := Eval vm_compute in (drop_base 47 (drop_base 14 (precall ubs2_keep (-208) LIB_STACK_RGB (ss_mem r1M1_L1)))).
Lemma r1M1_site_L1 : lib_site_check ubs2_msyms LIBPC RA_LIB LIB_STACK_RGB r1M1_L1 (-208) ubs2_keep [] 76 r1M1_LL1 = true.
Proof. vm_compute. reflexivity. Qed.
Definition r1M1_RSL1 : smem := Eval vm_compute in (match drv_add_statics ubs2_msyms (map snd r1M1_LL1) 92 with Some x => x | None => [] end).
Lemma r1M1_statics_L1 : drv_add_statics ubs2_msyms (map snd r1M1_LL1) (76 + 16) = Some r1M1_RSL1.
Proof. vm_compute. reflexivity. Qed.
Definition r1M1_P1 : sstate := Eval vm_compute in (mkSS RA_LIB (ss_regs (lib_post_state RA_LIB r1M1_L1 76 r1M1_RSL1)) r1M1_RSL1 None (ss_facts r1M1_L1)).
Lemma r1M1_L1_facts : sr_get (ss_regs r1M1_L1) 10%bv = SOff 52 0 /\ sr_get (ss_regs r1M1_L1) 11%bv = add0 sv_pl00 /\ sr_get (ss_regs r1M1_L1) 8%bv = sv_pl00.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition r1M1_I1 : sstate := Eval vm_compute in (match pf0_check 93 r1M1_P1 RET_PF with Some (s, _) => s | None => r1M1_P1 end).

Definition r1M1_F : sstate := Eval vm_compute in (runto_ ubs2_A_free r1M1_I1).
Definition r1M1_LF : list (nat * YQ0b.region) := Eval vm_compute in (precall ubs2_keep (-208) ALLOC_STACK (ss_mem r1M1_F)).
Lemma r1M1_site_F : site_check ubs2_msyms r1M1_F ubs2_A_free RA_FQ (-208) ubs2_keep [] 104 r1M1_LF = true.
Proof. vm_compute. reflexivity. Qed.
Definition r1M1_RSF : smem := Eval vm_compute in (match drv_add_statics ubs2_msyms (map snd r1M1_LF) 120 with Some x => x | None => [] end).
Lemma r1M1_statics_F : drv_add_statics ubs2_msyms (map snd r1M1_LF) (104 + 16) = Some r1M1_RSF.
Proof. vm_compute. reflexivity. Qed.
Lemma r1M1_F_facts : sr_get (ss_regs r1M1_F) 10%bv = SOff 52 0.
Proof. vm_compute. reflexivity. Qed.
Definition r1M1_Fp : sstate := Eval vm_compute in (post_state r1M1_F RA_FQ 104 r1M1_RSF).
Definition r1M1_N1 : sstate := Eval vm_compute in (run_ r1M1_Fp).
Definition r1M1_N1t : sstate := Eval vm_compute in (runto_ ubs2_A_free (add_cond r1M1_N1 cond_CMt)).
Definition r1M1_LN1t : list (nat * YQ0b.region) := Eval vm_compute in (precall ubs2_keep (-128) ALLOC_STACK (ss_mem r1M1_N1t)).
Lemma r1M1_site_N1t : site_check ubs2_msyms r1M1_N1t ubs2_A_free RA_sf (-128) ubs2_keep [] 121 r1M1_LN1t = true.
Proof. vm_compute. reflexivity. Qed.
Definition r1M1_RSN1t : smem := Eval vm_compute in (match drv_add_statics ubs2_msyms (map snd r1M1_LN1t) 137 with Some x => x | None => [] end).
Lemma r1M1_statics_N1t : drv_add_statics ubs2_msyms (map snd r1M1_LN1t) (121 + 16) = Some r1M1_RSN1t.
Proof. vm_compute. reflexivity. Qed.
Lemma r1M1_exit_N1t : exit_run_check ubs2segs ubs2tbl (post_state r1M1_N1t RA_sf 121 r1M1_RSN1t) 0 = true.
Proof. vm_compute. reflexivity. Qed.
Definition r1M1_N1f : sstate := Eval vm_compute in (runto_ ubs2_A_free (add_cond r1M1_N1 cond_CMf)).
Definition r1M1_LN1f : list (nat * YQ0b.region) := Eval vm_compute in (precall ubs2_keep (-128) ALLOC_STACK (ss_mem r1M1_N1f)).
Lemma r1M1_site_N1f : site_check ubs2_msyms r1M1_N1f ubs2_A_free RA_sf (-128) ubs2_keep [] 121 r1M1_LN1f = true.
Proof. vm_compute. reflexivity. Qed.
Definition r1M1_RSN1f : smem := Eval vm_compute in (match drv_add_statics ubs2_msyms (map snd r1M1_LN1f) 137 with Some x => x | None => [] end).
Lemma r1M1_statics_N1f : drv_add_statics ubs2_msyms (map snd r1M1_LN1f) (121 + 16) = Some r1M1_RSN1f.
Proof. vm_compute. reflexivity. Qed.
Lemma r1M1_exit_N1f : exit_run_check ubs2segs ubs2tbl (post_state r1M1_N1f RA_sf 121 r1M1_RSN1f) 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma r1M1_N_facts : sr_get (ss_regs r1M1_N1t) 10%bv = SOff 14 0 /\ sr_get (ss_regs r1M1_N1f) 10%bv = SOff 14 0 /\ sr_get (ss_regs r1M1_N0t) 10%bv = SOff 14 0 /\ sr_get (ss_regs r1M1_N0f) 10%bv = SOff 14 0.
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
Hypothesis Hpl : 0 < payload_len data.
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
Theorem ubs2_run_1M1 : forall E ms md,
run_env E data (ptr_addr L' b0) ->
st_ok ubs2segs E sQ1 ms -> aa_MR API L' A' (ms_mem ms) md -> md_inv fs md ->
forall K : option sptr * astate -> TSet,
jinv K (malloc (payload_len data) A') -> gtree mgrant (malloc (payload_len data) A') ->
(forall r, t_eq (K r) (leaf_shape data fs (payload_leaf b0 cap0 r))) ->
realizes ubs2segs (mkCfg ms md) (tset (malloc (payload_len data) A') K).
Proof.
intros E ms md HE HS HMR Hmd K HJ HG HK.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hlz & _).
assert (Hin : In (b0, cap0) (user_blocks A')) by (rewrite Hub; left; reflexivity).
pose proof (mr_blocks _ _ (aa_laws API) L' A' (ms_mem ms) md b0 cap0 0 HMR Hin ltac:(lia)) as (_ & Hq1 & Hq2 & _).
assert (Hac : alloc_ceiling < 2 ^ 63) by (pose proof YN05.alloc_ceiling_val; lia).
unfold dlen in Hok, HLc. pose proof (config_len_bound data) as Hclb.
destruct (list_len2 data ltac:(lia)) as (d0 & d1 & rest & Ed).
assert (Hplv : payload_len data = Z.of_nat (length data) - 6 - config_len data) by reflexivity.
pose proof HE as HE0. destruct HE0 as (HEd & HE13 & HE26 & HE46 & HAN).
apply (ubs2_Q_calls data cap0 L' b0 Hcap0 Hok HLc E ms HE Hcl) in HS. rewrite Hcalls in HS. change (st_ok ubs2segs E r1M1_Q ms) in HS.
let v := eval cbv [sv_pl00 sv_pl add0 sv_cl sv_b1s] in sv_pl00 in
assert (Hpl00 : U E v = payload_len data) by (eapply U_pl00; eauto; lia).
apply (st_ok_add_cond ubs2segs E r1M1_Q ms BC_NE (ltac:(let v := eval cbv [sv_pl00 sv_pl add0 sv_cl sv_b1s] in sv_pl00 in exact v)) (SLit 0)) in HS.
2:{ rewrite branch_ne_U, Hpl00, U_SLit. change (zcanon 0) with 0. apply Bool.negb_true_iff. apply Z.eqb_neq. lia. }
drv_run_to_with ubs2tbl_ok HS ubs2_A_malloc HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok ubs2segs E r1M1_ME msx) in HS end.
drv_mr (MR_after_frame ubs2_msyms (aa_MR API) (aa_laws API) AX) ubs2_keep E HS HF HMR.
pose proof (st_ok_reg ubs2segs _ _ _ 10%bv HS) as Hr10. rewrite (proj1 (proj2 r1M1_ME_facts)) in Hr10.
rewrite (denot_lit_U E (add0 sv_pl00)), U_add0 in Hr10. cbv [sv_pl00 sv_pl add0 sv_cl sv_b1s] in Hr10. rewrite Hpl00 in Hr10.
eapply (malloc_site ubs2_msyms API AX E r1M1_ME _ md L' A' (payload_len data) (-208) ubs2_keep [] 48 r1M1_LME r1M1_RSME RA_ME K
HS ltac:(drv_anch) r1M1_site_ME r1M1_statics_ME HMR HW HB);
[ intros Hf; rewrite Hid in Hf; discriminate
| exact Hr10
| lia
| intros kb sz [ ]
| exact HJ | exact HG | ].
clear Hr10.
intros res A2 L2 mS2 mD2 g2 tr HS2 ?HSA HMR2 HW2 HB2 Hmd2 Hpath Hstab Hhi Hbk Hres.
apply (md_inv_ex _ _ _ Hmd) in Hmd2.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR2) as (Hh2 & Hlz2 & _).
assert (Hid2 : st_init_done A2 = true) by (exact (malloc_keeps_init_done _ _ _ _ _ Hid (cpath_yields _ _ _ Hpath))).
destruct (Hstab _ _ Hin) as [Hin2 Hpb2].
lazymatch type of HS2 with st_ok _ _ _ ?msx => change (st_ok ubs2segs (post_env E 48 (ms_regs mS2) g2) r1M1_MEp msx) in HS2 end.
assert (HE2 : run_env (post_env E 48 (ms_regs mS2) g2) data (ptr_addr L' b0)) by (apply run_env_post; [lia | exact HE]).
clear HS HMR Hhi Hbk. rename HS2 into HS. rename HMR2 into HMR.
destruct res as [q|].
+
destruct Hres as (Hq0 & Hqnz & b1 & b2 & HubA2 & HubA1).
assert (Hinq : In (q, payload_len data) (user_blocks A2)) by (rewrite HubA2; apply in_app_iff; right; left; reflexivity).
pose proof (mr_blocks _ _ (aa_laws API) L2 A2 (ms_mem mS2) mD2 q (payload_len data) 0 HMR Hinq ltac:(lia)) as (_ & Hq3 & Hq4 & _).
assert (Hqb : q <> b0).
{ intros ->. pose proof (UL0o.blocks_same_ptr _ _ (aa_laws API) _ _ _ _ _ _ _ _ HMR Hinq Hin2 ltac:(lia) ltac:(lia) eq_refl). lia. }
assert (Hqba : ptr_addr L2 q <> ptr_addr L' b0).
{ rewrite <- Hpb2. exact (blocks_distinct_addr _ _ (aa_laws API) _ _ _ _ _ _ _ _ HMR Hinq Hin2 ltac:(lia) ltac:(lia) Hqb). }
apply (rz_conseq _ _ (wr ch_stdout line0 (ex 0 fs)) _).
2:{ eapply t_eq_trans; [| apply t_eq_sym; apply HK]. unfold payload_leaf; cbn [fst snd leaf_shape]. rewrite Hcalls.
change (repeat line0 1) with [line0]. cbn [concat]. rewrite app_nil_r. apply t_eq_refl. }
assert (H32 : bv_unsigned (ew (post_env E 48 (ms_regs mS2) g2) 52) = ptr_addr L2 q).
{ change 52%nat with (48 + 4)%nat. rewrite post_env_a0, Hq0, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
apply (st_ok_add_fact ubs2segs _ r1M1_MEp mS2 52 blkq_fact) in HS.
2:{ unfold afact_ok, blkq_fact. cbn [af_lo af_hi af_al2]. rewrite H32. change (2 ^ 4) with 16.
pose proof (mr_blocks_aligned _ _ (aa_laws API) L2 A2 (ms_mem mS2) mD2 q _ HMR Hinq). pose proof YN05.alloc_ceiling_val. lia. }
assert (HRE : renv (post_env E 48 (ms_regs mS2) g2) data (ptr_addr L' b0) (ptr_addr L2 q)) by (split; [exact HE2 | exact H32]).
clear HE2 H32.
drv_run_to_with ubs2tbl_ok HS ubs2_A_memcpy HF.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok ubs2segs Ec r1M1_MC msx) in HS;
drv_mr (MR_after_frame ubs2_msyms (aa_MR API) (aa_laws API) AX) ubs2_keep Ec HS HF HMR end.
lazymatch type of HS with st_ok _ ?Ec _ ?msx =>
pose proof (st_ok_reg ubs2segs _ _ _ 10%bv HS) as Hr10; pose proof (st_ok_reg ubs2segs _ _ _ 11%bv HS) as Hr11; pose proof (st_ok_reg ubs2segs _ _ _ 12%bv HS) as Hr12;
rewrite (proj1 r1M1_MC_facts) in Hr10; rewrite (proj1 (proj2 r1M1_MC_facts)) in Hr11; rewrite (proj2 (proj2 r1M1_MC_facts)) in Hr12;
eapply (ubs2_memcpy_site API AX Ec r1M1_MC msx mD2 L2 A2 q (payload_len data) (payload_len data) b0 cap0 (ptr_addr L' b0 + 6 + config_len data) 52 65 RA_MC _
HS ltac:(drv_anch) r1M1_ck_MC HMR Hinq Hin2 Hqb);
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
intros mS3 HS3 HMR3 Hout3 Hbd3. clear HS HMR Hbd3. rename HS3 into HS. rename HMR3 into HMR.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok ubs2segs Ec r1M1_MCp msx) in HS end.
renv_sync HS HRE.
drv_run_to_with ubs2tbl_ok HS LIBPC HF.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok ubs2segs Ec r1M1_L1 msx) in HS;
drv_mr (MR_after_frame ubs2_msyms (aa_MR API) (aa_laws API) AX) ubs2_keep Ec HS HF HMR end.
lazymatch type of HS with st_ok _ ?Ec _ ?msx =>
pose proof (st_ok_reg ubs2segs _ _ _ 10%bv HS) as Hr10; pose proof (st_ok_reg ubs2segs _ _ _ 11%bv HS) as Hr11;
rewrite (proj1 r1M1_L1_facts) in Hr10; rewrite (proj1 (proj2 r1M1_L1_facts)) in Hr11;
eapply (lib_site ubs2_msyms API AX LIBPC RA_LIB EMPTY LIB_STACK_RGB LIB lib_stk_pos FRM Ec r1M1_L1 msx mD2 L2 A2
(ptr_addr L2 q) (payload_len data) (-208) ubs2_keep [] 76 r1M1_LL1 r1M1_RSL1 _
HS ltac:(drv_anch) r1M1_site_L1 r1M1_statics_L1 HMR HW2 HB2 Hid2);
[ rewrite Hr10; cbn [sv_denot]; rewrite Z.add_0_r, <- (proj2 HRE), Z_to_bv_bv_unsigned; reflexivity
| rewrite Hr11; rewrite (denot_lit_U Ec (add0 sv_pl00)), U_add0, (U_pl00 Ec data d0 d1 rest); [reflexivity | exact (proj1 (proj1 HRE)) | exact Ed | exact (proj1 (proj2 (proj2 (proj1 HRE)))) | lia]
| right; split; [lia | exists q; split; [exact Hinq | reflexivity]]
| intros kb sz [ ]
| clear Hr10 Hr11 ]
end.
intros fx4 A3 L3 mS4 mD4 g4 HS' ?HSA FRM' HMR' HW4 HB4 Hid4 Hmd4 Hstab4 Hhi4 Hbk4.
apply (md_inv_ex _ _ _ Hmd2) in Hmd4.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (Hh4 & Hlz4 & _).
destruct (Hstab4 _ _ Hin2) as (bq4 & Hin4 & Hpb4). try rewrite Hpb2 in Hpb4.
destruct (Hstab4 _ _ Hinq) as (pq4 & Hinq4 & Hpq4).
clear HS HMR Hhi4 Hbk4 Hstab4. rename HS' into HS. rename HMR' into HMR. clear FRM; try clear fx. rename FRM' into FRM.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok ubs2segs Ec r1M1_P1 msx) in HS end.
renv_sync HS HRE.
pose proof (md_inv_ch1 _ _ Hmd4) as Hch4.
unfold wr at 1.
drv_printf0 HS Hch4 93%nat RET_PF HF.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok ubs2segs Ec r1M1_I1 msx) in HS;
drv_mr (MR_after_frame ubs2_msyms (aa_MR API) (aa_laws API) AX) ubs2_keep Ec HS HF HMR end.
renv_sync HS HRE.
drv_run_to_with ubs2tbl_ok HS ubs2_A_free HF.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok ubs2segs Ec r1M1_F msx) in HS;
drv_mr (MR_after_frame ubs2_msyms (aa_MR API) (aa_laws API) AX) ubs2_keep Ec HS HF HMR end.
lazymatch type of HS with st_ok _ ?Ec _ ?msx =>
pose proof (st_ok_reg ubs2segs _ _ _ 10%bv HS) as Hr10; rewrite r1M1_F_facts in Hr10;
eapply (free_site ubs2_msyms API AX Ec r1M1_F msx mD4 L3 A3 pq4 (payload_len data) (-208) ubs2_keep [] 104 r1M1_LF r1M1_RSF RA_FQ _
HS ltac:(drv_anch) r1M1_site_F r1M1_statics_F HMR HW4 HB4 Hid4 Hinq4);
[ rewrite Hr10; cbn [sv_denot]; rewrite Z.add_0_r, Hpq4, <- (proj2 HRE), Z_to_bv_bv_unsigned; reflexivity
| intros kb sz [ ]
| clear Hr10 ]
end.
intros A5 L5 mS5 mD5 g5 tr5 HS' ?HSA HMR' HW5 HB5 Hmd5 Hpath5 Hub5 Hstab5 Hhi5 Hbk5.
apply (md_inv_ex _ _ _ Hmd4) in Hmd5.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (Hh5 & Hlz5 & _).
assert (Hid5 : st_init_done A5 = true) by (exact (free_keeps_init_done _ _ _ _ _ Hid4 (cpath_yields _ _ _ Hpath5))).
destruct (Hstab5 _ _ Hin4 ltac:(intros HH; apply Hqba; rewrite <- Hpq4, <- Hpb4, HH; reflexivity)) as [Hin5 Hpb5]. try rewrite Hpb4 in Hpb5.
clear HS HMR Hhi5 Hbk5 Hstab5. rename HS' into HS. rename HMR' into HMR.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok ubs2segs Ec r1M1_Fp msx) in HS end.
renv_sync HS HRE.
drv_run_with ubs2tbl_ok HS HF.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok ubs2segs Ec r1M1_N1 msx) in HS;
drv_mr (MR_after_frame ubs2_msyms (aa_MR API) (aa_laws API) AX) ubs2_keep Ec HS HF HMR end.
unfold ex.
destruct (count_mode data) eqn:Hcm.
* to_free_buf HS HMR Hcm (proj1 (proj1 HRE)).
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok ubs2segs Ec r1M1_N1t msx) in HS end.
lazymatch type of HS with st_ok _ ?Ec _ ?msx =>
pose proof (st_ok_reg ubs2segs _ _ _ 10%bv HS) as Hr10;
eapply (free_site ubs2_msyms API AX Ec r1M1_N1t msx mD5 L5 A5 bq4 cap0 (-128) ubs2_keep [] 121 r1M1_LN1t r1M1_RSN1t RA_sf _
HS ltac:(drv_anch) r1M1_site_N1t r1M1_statics_N1t HMR HW5 HB5 Hid5 Hin5);
[ rewrite Hr10; match goal with |- sv_denot _ ?x = _ => replace x with (SOff 14 0) by (symmetry; first [exact (proj1 r1M1_N_facts) | exact (proj1 (proj2 r1M1_N_facts)) | exact (proj1 (proj2 (proj2 r1M1_N_facts))) | exact (proj2 (proj2 (proj2 r1M1_N_facts)))]) end;
cbn [sv_denot]; rewrite Z.add_0_r, Hpb5, <- (proj1 (proj2 (proj1 HRE))), Z_to_bv_bv_unsigned; reflexivity
| intros kb sz [ ]
| clear Hr10 ]
end.
intros AN1t LN1t mSN1t mDN1t gN1t trN1t HS' ?HSA HMR' HWN1t HBN1t HmdN1t HpathN1t HubN1t HstabN1t HhiN1t HbkN1t.
apply (md_inv_ex _ _ _ Hmd5) in HmdN1t.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (HhN1t & HlzN1t & _).
pose proof (md_inv_ch1 _ _ HmdN1t) as HchN1t.
rewrite <- (md_inv_fs _ _ HmdN1t).
match goal with |- realizes _ _ (t_exit (Z_to_bv 64 ?c) _) => let c' := eval cbv in c in change c with c' | _ => idtac end.
exact (ubs2_exit _ _ mSN1t mDN1t 0 HS' ltac:(lia) r1M1_exit_N1t HhN1t HlzN1t).
* to_free_buf HS HMR Hcm (proj1 (proj1 HRE)).
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok ubs2segs Ec r1M1_N1f msx) in HS end.
lazymatch type of HS with st_ok _ ?Ec _ ?msx =>
pose proof (st_ok_reg ubs2segs _ _ _ 10%bv HS) as Hr10;
eapply (free_site ubs2_msyms API AX Ec r1M1_N1f msx mD5 L5 A5 bq4 cap0 (-128) ubs2_keep [] 121 r1M1_LN1f r1M1_RSN1f RA_sf _
HS ltac:(drv_anch) r1M1_site_N1f r1M1_statics_N1f HMR HW5 HB5 Hid5 Hin5);
[ rewrite Hr10; match goal with |- sv_denot _ ?x = _ => replace x with (SOff 14 0) by (symmetry; first [exact (proj1 r1M1_N_facts) | exact (proj1 (proj2 r1M1_N_facts)) | exact (proj1 (proj2 (proj2 r1M1_N_facts))) | exact (proj2 (proj2 (proj2 r1M1_N_facts)))]) end;
cbn [sv_denot]; rewrite Z.add_0_r, Hpb5, <- (proj1 (proj2 (proj1 HRE))), Z_to_bv_bv_unsigned; reflexivity
| intros kb sz [ ]
| clear Hr10 ]
end.
intros AN1f LN1f mSN1f mDN1f gN1f trN1f HS' ?HSA HMR' HWN1f HBN1f HmdN1f HpathN1f HubN1f HstabN1f HhiN1f HbkN1f.
apply (md_inv_ex _ _ _ Hmd5) in HmdN1f.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (HhN1f & HlzN1f & _).
pose proof (md_inv_ch1 _ _ HmdN1f) as HchN1f.
rewrite <- (md_inv_fs _ _ HmdN1f).
match goal with |- realizes _ _ (t_exit (Z_to_bv 64 ?c) _) => let c' := eval cbv in c in change c with c' | _ => idtac end.
exact (ubs2_exit _ _ mSN1f mDN1f 0 HS' ltac:(lia) r1M1_exit_N1f HhN1f HlzN1f).
+
destruct Hres as [Hq0 HubA2].
apply (rz_conseq _ _ (ex (if count_mode data then 0 else 2) fs) _); [| apply t_eq_sym; apply HK].
apply (st_ok_regs ubs2segs _ _ mS2 (sr_set (ss_regs r1M1_MEp) 10%bv (SLit 0))) in HS.
2:{ intros r. destruct (decide (r = 10%bv)) as [->|Hne'].
- rewrite sr_get_set_same by reflexivity. rewrite (proj2 (proj2 r1M1_ME_facts)).
cbn [sv_denot]. rewrite Z.add_0_r. change 52%nat with (48 + 4)%nat. rewrite post_env_a0, Hq0. reflexivity.
- rewrite sr_get_set_other by exact Hne'. reflexivity. }
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok ubs2segs Ec r1M1_MEn msx) in HS end.
assert (HRE : run_env (post_env E 48 (ms_regs mS2) g2) data (ptr_addr L' b0)) by exact HE2.
drv_run_with ubs2tbl_ok HS HF.
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok ubs2segs Ec r1M1_N0 msx) in HS;
drv_mr (MR_after_frame ubs2_msyms (aa_MR API) (aa_laws API) AX) ubs2_keep Ec HS HF HMR end.
unfold ex.
destruct (count_mode data) eqn:Hcm.
* to_free_buf HS HMR Hcm (proj1 HRE).
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok ubs2segs Ec r1M1_N0t msx) in HS end.
lazymatch type of HS with st_ok _ ?Ec _ ?msx =>
pose proof (st_ok_reg ubs2segs _ _ _ 10%bv HS) as Hr10;
eapply (free_site ubs2_msyms API AX Ec r1M1_N0t msx mD2 L2 A2 b0 cap0 (-128) ubs2_keep [] 65 r1M1_LN0t r1M1_RSN0t RA_sf _
HS ltac:(drv_anch) r1M1_site_N0t r1M1_statics_N0t HMR HW2 HB2 Hid2 Hin2);
[ rewrite Hr10; match goal with |- sv_denot _ ?x = _ => replace x with (SOff 14 0) by (symmetry; first [exact (proj1 r1M1_N_facts) | exact (proj1 (proj2 r1M1_N_facts)) | exact (proj1 (proj2 (proj2 r1M1_N_facts))) | exact (proj2 (proj2 (proj2 r1M1_N_facts)))]) end;
cbn [sv_denot]; rewrite Z.add_0_r, Hpb2, <- (proj1 (proj2 HRE)), Z_to_bv_bv_unsigned; reflexivity
| intros kb sz [ ]
| clear Hr10 ]
end.
intros AN0t LN0t mSN0t mDN0t gN0t trN0t HS' ?HSA HMR' HWN0t HBN0t HmdN0t HpathN0t HubN0t HstabN0t HhiN0t HbkN0t.
apply (md_inv_ex _ _ _ Hmd2) in HmdN0t.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (HhN0t & HlzN0t & _).
pose proof (md_inv_ch1 _ _ HmdN0t) as HchN0t.
rewrite <- (md_inv_fs _ _ HmdN0t).
match goal with |- realizes _ _ (t_exit (Z_to_bv 64 ?c) _) => let c' := eval cbv in c in change c with c' | _ => idtac end.
exact (ubs2_exit _ _ mSN0t mDN0t 0 HS' ltac:(lia) r1M1_exit_N0t HhN0t HlzN0t).
* to_free_buf HS HMR Hcm (proj1 HRE).
lazymatch type of HS with st_ok _ ?Ec _ ?msx => change (st_ok ubs2segs Ec r1M1_N0f msx) in HS end.
lazymatch type of HS with st_ok _ ?Ec _ ?msx =>
pose proof (st_ok_reg ubs2segs _ _ _ 10%bv HS) as Hr10;
eapply (free_site ubs2_msyms API AX Ec r1M1_N0f msx mD2 L2 A2 b0 cap0 (-128) ubs2_keep [] 65 r1M1_LN0f r1M1_RSN0f RA_sf _
HS ltac:(drv_anch) r1M1_site_N0f r1M1_statics_N0f HMR HW2 HB2 Hid2 Hin2);
[ rewrite Hr10; match goal with |- sv_denot _ ?x = _ => replace x with (SOff 14 0) by (symmetry; first [exact (proj1 r1M1_N_facts) | exact (proj1 (proj2 r1M1_N_facts)) | exact (proj1 (proj2 (proj2 r1M1_N_facts))) | exact (proj2 (proj2 (proj2 r1M1_N_facts)))]) end;
cbn [sv_denot]; rewrite Z.add_0_r, Hpb2, <- (proj1 (proj2 HRE)), Z_to_bv_bv_unsigned; reflexivity
| intros kb sz [ ]
| clear Hr10 ]
end.
intros AN0f LN0f mSN0f mDN0f gN0f trN0f HS' ?HSA HMR' HWN0f HBN0f HmdN0f HpathN0f HubN0f HstabN0f HhiN0f HbkN0f.
apply (md_inv_ex _ _ _ Hmd2) in HmdN0f.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR') as (HhN0f & HlzN0f & _).
pose proof (md_inv_ch1 _ _ HmdN0f) as HchN0f.
rewrite <- (md_inv_fs _ _ HmdN0f).
match goal with |- realizes _ _ (t_exit (Z_to_bv 64 ?c) _) => let c' := eval cbv in c in change c with c' | _ => idtac end.
exact (ubs2_exit _ _ mSN0f mDN0f 2 HS' ltac:(lia) r1M1_exit_N0f HhN0f HlzN0f).
Qed.
End b.
End a.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
