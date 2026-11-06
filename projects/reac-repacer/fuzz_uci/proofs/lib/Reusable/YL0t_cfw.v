(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from lib/Reusable/YL0t.v. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/libreac/fuzz_scene/lib/Reusable/YL0t_cfw.v, with its module paths changed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0k YK0n YK0p YP0n YM06 YM02.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YO0i YO0f YO0x YO0d YO0e YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO06.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YH00 YH01 YH03 YH02 YN3e YN35 YN3f YN3g YN34 YN3d.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YN03 YL07 YL01 YL08 YL0d YL0e YL02 YL0a YL00 YL04 YL0c YL09 YL05 YL0g YL0k YL0m YL0u YL0r YL0o YL0s.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YI06 YI16 YI14 YI5b YI5c YL0i YL06 YL03 YL0l.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YL0t YK15_cfw YP03_cfw YL0k_cfw.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib Require Import SlotAgree AgreeLift.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Section d.
Variable API : AllocAPI src0_msyms.
Hypothesis AX : AllocExtra src0_msyms (aa_MR API).
Variables (data : list byte) (cap0 : Z) (L' : layout) (A' : astate) (b0 : sptr) (MDc : Model).
Hypothesis Hub : user_blocks A' = [(b0, cap0)].
Hypothesis Hcap0 : 65536 <= cap0 <= 67108864.
Hypothesis Hok : 6 + config_len data <= dlen data.
Hypothesis HLc : dlen data < cap0.
Theorem src0_P_to_QX_cf : forall E ms T,
run_env E data (ptr_addr L' b0) ->
st_ok src0segs E (if config_len data =? 0 then ssP0 else ssP1) ms ->
aa_MR API L' A' (ms_mem ms) MDc ->
blk_data src0_msyms (ms_mem ms) (ptr_addr L' b0) data ->
(forall ms', st_ok src0segs E (if config_len data =? 0 then sQ0 else sQ1) ms' ->
aa_MR API L' A' (ms_mem ms') MDc ->
blk_data src0_msyms (ms_mem ms') (ptr_addr L' b0) data ->
crealizes src0_msyms (mkCfg ms' MDc) T) ->
crealizes src0_msyms (mkCfg ms MDc) T.
Proof using AX HLc Hok Hub.
intros E ms T HE HS HMR HD K.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hlz & _).
assert (Hin : In (b0, cap0) (user_blocks A')) by (rewrite Hub; left; reflexivity).
pose proof HE as HE0. destruct HE as (HEd & HE13 & HE26 & HE46 & HAN). unfold dlen in *.
destruct (list_len2 data ltac:(pose proof (config_len_bound data); lia)) as (d0 & d1 & rest & Ed).
let v := eval cbv [sv_cl00 add0 sv_cl sv_b1s] in sv_cl00 in
assert (Hcl00 : U E v = config_len data) by (eapply U_cl00; eauto).
destruct (Z.eqb_spec (config_len data) 0) as [Hz | Hnz].
- cdrv_run_with src0tbl_ok HS HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E sB0 msx) in HS end.
drv_bd AX src0_keep E HS HF HMR HD Hin.
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep E HS HF HMR.
sym_assume_with src0tbl_ok HS true.
{ rewrite branch_eq_U, Hcl00, U_SLit, Hz. reflexivity. }
cdrv_run_with src0tbl_ok HS HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E sQ0 msx) in HS end.
drv_bd AX src0_keep E HS HF HMR HD Hin.
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep E HS HF HMR.
exact (K _ HS HMR HD).
- cdrv_run_with src0tbl_ok HS HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E sB1 msx) in HS end.
drv_bd AX src0_keep E HS HF HMR HD Hin.
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep E HS HF HMR.
sym_assume_with src0tbl_ok HS false.
{ rewrite branch_eq_U, Hcl00, U_SLit. change (zcanon 0) with 0. apply Z.eqb_neq. exact Hnz. }
cdrv_run_with src0tbl_ok HS HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E sQ1 msx) in HS end.
drv_bd AX src0_keep E HS HF HMR HD Hin.
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep E HS HF HMR.
exact (K _ HS HMR HD).
Qed.
End d.
End b.
