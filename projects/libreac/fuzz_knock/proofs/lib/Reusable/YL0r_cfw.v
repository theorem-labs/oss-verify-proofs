(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from lib/Reusable/YL0r.v. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/libreac/fuzz_scene/lib/Reusable/YL0r_cfw.v, with its module paths changed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YK0p YP0n YM06 YM02.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YO0i YO0f YO0x YO0d YO0e YO05.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YH00 YH01 YH03 YH02 YN3e.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YN03 YL07 YL01 YL08 YL0d YL0e YL02 YL0a YL0b YL00 YL04 YL0c YL09 YL0k YL0m YL0u.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YL0r YK15_cfw YP03_cfw YL0k_cfw.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require Import SlotAgree AgreeLift.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section P.
Variable API : AllocAPI src0_msyms.
Hypothesis AX : AllocExtra src0_msyms (aa_MR API).
Variables (data : list byte) (cap0 : Z) (L' : layout) (A' : astate) (b0 : sptr) (E2 : env) (md : Model).
Hypothesis Hub : user_blocks A' = [(b0, cap0)].
Hypothesis Hcap0 : 65536 <= cap0 <= 67108864.
Hypothesis HE : hdr_env E2 data (ptr_addr L' b0).
Hypothesis HAN : hdr_anch E2.
Let pP : Z := ptr_addr L' b0 + 2 + config_len data.
Let E3 : env := E_P E2 data pP.
Let E2_ed2 : ed E2 2 = data := ltac:(eapply YL0r.E2_ed2; exact HE).
Let E3_ed2 : ed E3 2 = data := ltac:(eapply YL0r.E3_ed2; exact HE).
Theorem src0_to_P_cf : forall ms2 T,
6 + config_len data <= dlen data -> dlen data < cap0 ->
st_ok src0segs E2 ss_h1 ms2 ->
aa_MR API L' A' (ms_mem ms2) md ->
blk_data src0_msyms (ms_mem ms2) (ptr_addr L' b0) data ->
(forall ms3, st_ok src0segs E3 (if config_len data =? 0 then ssP0 else ssP1) ms3 ->
aa_MR API L' A' (ms_mem ms3) md ->
blk_data src0_msyms (ms_mem ms3) (ptr_addr L' b0) data ->
crealizes src0_msyms (mkCfg ms3 md) T) ->
crealizes src0_msyms (mkCfg ms2 md) T.
Proof using AX HAN HE Hcap0 Hub.
intros ms2 T Hok HLc HS0 HMR HD K.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hlz & _).
assert (Hin : In (b0, cap0) (user_blocks A')) by (rewrite Hub; left; reflexivity).
pose proof (mr_blocks _ _ (aa_laws API) L' A' (ms_mem ms2) md b0 cap0 0 HMR Hin ltac:(lia)) as (_ & Hq1 & Hq2 & _).
unfold dlen in Hok, HLc. pose proof (config_len_bound data) as Hcl.
assert (Hac : alloc_ceiling < 2 ^ 47) by (pose proof YM05.alloc_ceiling_val; lia).
destruct (list_len2 data ltac:(lia)) as (d0 & d1 & rest & Ed).
pose proof (proj1 (proj2 HE)) as E13. pose proof (proj2 (proj2 HE)) as E26.
assert (HS : st_ok src0segs E2 (add_cond ss_h1 cond_OK) ms2).
{ apply (st_ok_add_cond_neg src0segs E2 ss_h1 ms2 BC_LTU (SOff 27 0) sv_cl6 HS0).
rewrite branch_ltu_U, (U_cl6 E2 d0 d1 rest) by (rewrite E2_ed2; exact Ed).
rewrite U_SOff, E26, Z.add_0_r, zcanon_id by (unfold M64 in *; lia).
apply Z.ltb_ge. rewrite <- Ed. lia. }
clear HS0.
cdrv_run_with src0tbl_ok HS HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E2 sP msx) in HS end.
lazymatch type of HF with frame_of _ ?rs0 ?m0 ?m1 =>
pose proof (blk_data_after_frame src0_msyms (aa_MR API) (aa_laws API) AX L' A' m0 m1 _ E2 (ss_facts sP) src0_keep rs0 b0 cap0 (ptr_addr L' b0) data HMR
ltac:(destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & HG0); exact HG0) ltac:(drv_anch) ltac:(vm_compute; reflexivity) HF Hin ltac:(lia) ltac:(lia)) as HD';
specialize (HD' HD); clear HD; rename HD' into HD end.
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep E2 HS HF HMR.
lazymatch type of HS with st_ok _ _ _ ?msx => apply (K msx); [| exact HMR | exact HD] end.
destruct sP_facts as (Hpc & Ha0P & Hhd & Hpd & Hsep & Hrv).
assert (HpP : 0 <= pP < 2 ^ 64) by (unfold pP; lia).
apply (st_ok_agree_pd src0segs _ _ E2 E3 sP _ HS (E_P_agree E2 data pP)) in Hpd. clear HS. rename Hpd into HS.
destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
assert (HS' : st_ok src0segs E3 (ssP (if config_len data =? 0 then 2 else 3)) ltac:(lazymatch type of H7 with regs_ok _ _ (ms_regs ?m) => exact m end)).
2:{ destruct (config_len data =? 0); [change ssP0 with (ssP 2) | change ssP1 with (ssP 3)]; exact HS'. }
unfold st_ok, ssP. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [rewrite H4, Hrv; reflexivity|].
split; [exact H5|]. split; [exact H6|]. split; [| split].
-
intros r. destruct (decide (r = 10%bv)) as [->|Hne].
+ rewrite sr_get_set_same by reflexivity. rewrite (H7 10%bv), Ha0P.
rewrite (denot_lit_U E3 (SOff 47 0)), (denot_lit_U E3 (SAlu ALU_ADD (SOff 14 2) sv_cl)). f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, (U_cl E3 d0 d1 rest) by (rewrite E3_ed2; exact Ed).
unfold E3. rewrite E_P_46 by exact HpP. rewrite E_P_old by lia. rewrite E13.
rewrite <- Ed. unfold pP. rewrite (zcanon_id (ptr_addr L' b0 + 2)) by (unfold M64 in *; lia).
rewrite !zcanon_id by (unfold M64 in *; lia). lia.
+ rewrite sr_get_set_other by exact Hne. apply H7.
-
change (ss_mem sP) with (block_region 14 6 [mkChunk 0 (CData 2 0 6)] :: tl (ss_mem sP)) in H8.
set (tail := tl (ss_mem sP)) in *.
assert (E13' : bv_unsigned (ew E3 14) = ptr_addr L' b0) by (unfold E3; rewrite E_P_old by lia; exact E13).
assert (HM1 : mem_ok src0segs E3 (ms_mem ms) (R13h (if config_len data =? 0 then 2 else 3) :: tail)).
{ eapply (mem_ok_head_replace src0_msyms); [exact H8 | reflexivity | cbn; lia | | | cbn; lia | |].
- unfold R13h, block_region. cbn [r_hi]. destruct (config_len data =? 0); lia.
- unfold R13h, block_region. cbn [r_lo r_hi]. destruct (config_len data =? 0); lia.
- unfold R13h, block_region. cbn. destruct (config_len data =? 0); reflexivity.
- unfold R13h, block_region. cbn [r_chunks r_base base_val]. rewrite E13'. constructor; [| constructor].
eapply (chunk_ok_cdata0 src0_msyms); [exact E3_ed2 | destruct (config_len data =? 0); lia |].
intros i Hi. apply HD. destruct (config_len data =? 0); lia. }
eapply (mem_ok_cons src0_msyms); [exact HM1 | reflexivity | |].
+
unfold region_ok, R46. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. unfold E3 at 1 2 3. rewrite E_P_46 by exact HpP.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [| constructor].
eapply (chunk_ok_cdata0 src0_msyms); [apply E_P_ed3 | rewrite length_skipn; lia |].
intros i Hi. unfold E3. rewrite E_P_46 by exact HpP. unfold pP.
replace (ptr_addr L' b0 + 2 + config_len data + i) with (ptr_addr L' b0 + (2 + config_len data + i)) by lia.
rewrite (HD (2 + config_len data + i)) by lia.
rewrite nth_error_skipn. f_equal. lia.
+
intros r' [<- | Hr'].
* unfold extent_disjoint, R46, R13h, block_region. cbn [r_base r_lo r_hi base_val]. rewrite E13'.
unfold E3. rewrite E_P_46 by exact HpP. unfold pP. right. destruct (Z.eqb_spec (config_len data) 0); lia.
* eapply (sep_check_disjoint src0_msyms (aa_MR API) (aa_laws API) AX E3 _ (ss_facts sP) L' A' md b0 cap0 tail R46 47);
[exact H9 | | exact HMR | exact Hin | reflexivity | cbn; lia | | | (first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate]) | exact Hsep | exact Hr'].
-- apply (hdr_anch_ext E2 E3 HAN); [| vm_compute; reflexivity]. intros n Hn. unfold E3. apply E_P_old. lia.
-- cbn [r_lo R46]. unfold E3. rewrite E_P_46 by exact HpP. unfold pP. lia.
-- cbn [r_hi R46]. unfold E3. rewrite E_P_46 by exact HpP. unfold pP. lia.
-
apply facts_ok_add_atom; [exact H9|]. unfold afact_ok, fact_P. cbn [af_lo af_hi af_al2].
unfold E3. rewrite E_P_46 by exact HpP. unfold pP. change (2 ^ 0) with 1. rewrite Z.mod_1_r.
pose proof YM05.alloc_ceiling_val. lia.
Qed.
End P.
End a.
