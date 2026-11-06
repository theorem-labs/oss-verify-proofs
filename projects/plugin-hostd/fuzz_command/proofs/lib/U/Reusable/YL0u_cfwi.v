(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from lib/Reusable/YL0u.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Reusable/YL0u_cfwi.v, with its module paths changed; 2 of its 160 lines of code are new or changed and 2 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YK0p YP0n YM06 YM02.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0x YO0d YO0e YO05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YH00 YH01 YH03 YH02 YN3e YN35 YN3f YN3g YN34.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YN03 YL07 YL01 YL08 YL0d YL0e YL02 YL0a YL0b YL00 YL04 YL0c YL09 YL0k YL0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YL0u YK15_cfw YP03_cfw YN35_cfw YN34b_cfw YL0d_cfwi YL0k_cfw.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract SlotAgree SlotAgreeI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac cdrv_fwrite HS Hch k HF :=
lazymatch type of HS with st_ok _ ?E ?ss ?ms =>
lazymatch type of Hch with fdchan (Z_to_bv 64 ?fd) ?ch ?model =>
lazymatch goal with |- crealizes _ _ (t_emit (map _ ?msg) _) =>
let r := eval vm_compute in (wx_msg_check k ss msg) in
lazymatch r with
| Some (?s2, _) =>
let Hck := fresh "Hck" in
assert (Hck : wx_msg_check k ss msg = Some (s2, fd)) by (vm_compute; reflexivity);
apply (crealizes_writev_msg_by_run E ss ms model ch k msg s2 fd _ HS ltac:(assumption) ltac:(assumption) Hck Hch);
clear Hck HS;
let ms' := fresh "ms" in let ws := fresh "ws" in
let Hsk := fresh "Hsk" in let Hma := fresh "Hma" in
intros ms' ws HS HF Hsk Hma; clear Hsk Hma; cbn [ms_mem mkst pend_at] in HF
| None => fail "cdrv_fwrite: wx_msg_check failed on this state"
end
end end end.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable API : AllocAPI src0_msyms.
Hypothesis AX : AllocExtra src0_msyms (aa_MR API).
Hypothesis FCF : forall fx' : FPState, @free_contract_cfi fx' rc src0_msyms API.
Hypothesis TBL : forall L A mem md, aa_MR API L A mem md -> forall a, static_owned src0_msyms a -> 0 <= a < 2 ^ 64 ->
Mem.ro_addr src0segs (Z_to_bv 64 a) = true -> mbyte src0segs mem a = seg_rom src0segs (Z_to_bv 64 a).
Variables (inp : ProcInput) (data : list byte) (cap0 : Z) (L' : layout) (A' : astate) (b0 : sptr).
Hypothesis Hub : user_blocks A' = [(b0, cap0)].
Hypothesis Hcap0 : 65536 <= cap0 <= 67108864.
Hypothesis HLc : dlen data < cap0.
Hypothesis HW : WF A'.
Hypothesis HB : bounded A'.
Hypothesis Hid : st_init_done A' = true.
Ltac cmsg_free_exit HS HMR Hch Hmd Hin HE13 E ss_sw ss_sf L_sf RS_sf site statics exit_ck a0_lemma Hres :=
let HF := fresh "HF" in let Hr10 := fresh "Hr10" in
let HG00 := fresh "HG00" in let HSA00 := fresh "HSA00" in
lazymatch type of HS with st_ok _ _ ?ss0 _ =>
assert (HG00 : facts_ok E (ss_facts ss0)) by (destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & X); exact X);
assert (HSA00 : stack_anchored E (ss_facts ss0)) by drv_anch
end;
cdrv_fwrite HS Hch K_SW HF;
lazymatch type of HS with st_ok _ ?Eh _ ?msx =>
change (st_ok src0segs Eh ss_sw msx) in HS;
lazymatch type of HF with frame_of _ ?rs0 _ _ =>
apply (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX _ _ _ _ _ E _ src0_keep rs0 HMR HG00 HSA00 ltac:(vm_compute; reflexivity)) in HF end;
clear HMR HG00 HSA00; rename HF into HMR;
let HANh := fresh "HANh" in
assert (HANh : hdr_anch Eh) by (eapply hdr_anch_ext; [eassumption | intros; apply ew_havoc_old; unfold K_SW; lia]);
cdrv_run_to_with src0tbl_ok HS src0_A_free HF;
lazymatch type of HS with st_ok _ _ _ ?msy => change (st_ok src0segs Eh ss_sf msy) in HS end;
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep Eh HS HF HMR;
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS) as Hr10;
eapply (free_site_cf src0_msyms API AX TBL (FCF _) _ ss_sf _ _ L' A' b0 cap0 MAIN_SP src0_keep [] K_SF L_sf RS_sf RA_sf _
HS ltac:(drv_anch) site ltac:(vm_compute; reflexivity) statics HMR HW HB Hid Hin);
[ rewrite Hr10, a0_lemma; cbn [sv_denot]; rewrite Z.add_0_r, (ew_havoc_old _ K_SW _ 14) by (unfold K_SW; lia); rewrite <- HE13, Z_to_bv_bv_unsigned; reflexivity
| exact Hres
| intros kb sz [ ]
| ];
clear Hr10;
let vm2 := fresh "vm2" in let HSA2 := fresh "HSA2" in
intros A2 L2 ms3 md3 g2 HS2 HSA2 HMR2 HW2 HB2 [vm2 Hmd3] Hstab Hhi Hbk _;
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR2) as (Hh2 & Hlz2 & _);
replace (in_fs inp) with (m_fs md3) by (rewrite Hmd3; autorewrite with model; exact (proj2 (proj2 Hmd)));
exact (src0_exit_cf _ _ ms3 md3 2 HS2 ltac:(lia) exit_ck Hh2 Hlz2)
end.
Theorem src0_short_tail_cf : forall E ms md,
hdr_env E data (ptr_addr L' b0) -> hdr_anch E -> dlen data <= 5 ->
st_ok src0segs E ss_h0 ms -> aa_MR API L' A' (ms_mem ms) md -> (II A') -> md_ok inp md ->
crealizes src0_msyms (mkCfg ms md) (diag msg_short (in_fs inp)).
Proof using AX FCF HB HW Hcap0 Hid Hub TBL.
intros E ms md (HEd & HE13 & HE26) HAN HL HS0 HMR Hres Hmd.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hlz & _).
pose proof (proj1 (proj2 Hmd)) as Hch.
assert (Hin : In (b0, cap0) (user_blocks A')) by (rewrite Hub; left; reflexivity).
pose proof (mr_blocks _ _ (aa_laws API) L' A' (ms_mem ms) md b0 cap0 0 HMR Hin ltac:(lia)) as (_ & Hq1 & Hq2 & _).
assert (Hac : alloc_ceiling < 2 ^ 47) by (pose proof YM05.alloc_ceiling_val; lia). unfold dlen in HL.
assert (HS : st_ok src0segs E ss_short ms).
{ apply (st_ok_add_cond src0segs E ss_h0 ms BC_GEU (SLit 5) (SOff 27 0) HS0).
rewrite branch_geu_U, U_SLit, U_SOff, HE26, Z.add_0_r, !zcanon_id by (unfold M64; lia). rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
clear HS0. unfold diag, wr, ex.
cmsg_free_exit HS HMR Hch Hmd Hin HE13 E ss_sw ss_sf L_sf RS_sf site_sf statics_sf exit_sf a0_sf Hres.
Qed.
Theorem src0_to_h1_cf : forall E ms md T,
hdr_env E data (ptr_addr L' b0) -> hdr_anch E -> 6 <= dlen data ->
st_ok src0segs E ss_h0 ms -> aa_MR API L' A' (ms_mem ms) md ->
blk_data src0_msyms (ms_mem ms) (ptr_addr L' b0) data ->
(forall ms', st_ok src0segs E ss_h1 ms' -> aa_MR API L' A' (ms_mem ms') md ->
blk_data src0_msyms (ms_mem ms') (ptr_addr L' b0) data ->
crealizes src0_msyms (mkCfg ms' md) T) ->
crealizes src0_msyms (mkCfg ms md) T.
Proof using AX HLc Hcap0 Hub.
intros E ms md T (HEd & HE13 & HE26) HAN HL HS0 HMR HD K.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hlz & _).
assert (Hin : In (b0, cap0) (user_blocks A')) by (rewrite Hub; left; reflexivity).
pose proof (mr_blocks _ _ (aa_laws API) L' A' (ms_mem ms) md b0 cap0 0 HMR Hin ltac:(lia)) as (_ & Hq1 & Hq2 & _).
assert (Hac : alloc_ceiling < 2 ^ 47) by (pose proof YM05.alloc_ceiling_val; lia). unfold dlen in HL, HLc.
destruct ss_h_facts as (Hpc0 & Hpc1 & _ & _ & _ & _ & _ & Hsep).
apply (st_ok_add_cond_neg src0segs E ss_h0 ms BC_GEU (SLit 5) (SOff 27 0)) in HS0.
2:{ rewrite branch_geu_U, U_SLit, U_SOff, HE26, Z.add_0_r, !zcanon_id by (unfold M64; lia).
rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
change (add_cond ss_h0 (mkAC (neg_bc BC_GEU) (SLit 5) (SOff 27 0))) with ss_h0c in HS0.
assert (HS : st_ok src0segs E ss_h6 ms).
{ destruct HS0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9). unfold st_ok, ss_h6. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
repeat (split; [assumption|]). split; [| exact H9].
eapply (mem_ok_cons src0_msyms); [exact H8 | reflexivity | |].
- unfold region_ok, blkreg6, block_region. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HE13.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [| constructor]. eapply (chunk_ok_cdata0 src0_msyms); [exact HEd | lia |]. intros i Hi. apply HD. lia.
- eapply (sep_check_disjoint src0_msyms (aa_MR API) (aa_laws API) AX E _ (ss_facts ss_h0c) L' A' md b0 cap0 _ blkreg6 14);
[exact H9 | apply HAN; vm_compute; reflexivity | exact HMR | exact Hin | reflexivity | cbn; lia | | | (first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate]) | exact Hsep].
+ cbn [r_lo blkreg6 block_region]. rewrite HE13. lia.
+ cbn [r_hi blkreg6 block_region]. rewrite HE13. lia. }
clear HS0.
cdrv_run_with src0tbl_ok HS HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E ss_h1 msx) in HS end.
lazymatch type of HF with frame_of _ ?rs0 ?m0 ?m1 =>
pose proof (blk_data_after_frame src0_msyms (aa_MR API) (aa_laws API) AX L' A' m0 m1 _ E (ss_facts ss_h1) src0_keep rs0 b0 cap0 (ptr_addr L' b0) data HMR
ltac:(destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & HG0); exact HG0) ltac:(drv_anch) ltac:(vm_compute; reflexivity) HF Hin ltac:(lia) ltac:(lia)) as HD';
specialize (HD' HD); clear HD; rename HD' into HD end.
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep E HS HF HMR.
lazymatch type of HS with st_ok _ _ _ ?msx => exact (K msx HS HMR HD) end.
Qed.
Theorem src0_overrun_tail_cf : forall E ms md,
hdr_env E data (ptr_addr L' b0) -> hdr_anch E -> 6 <= dlen data -> dlen data < 6 + config_len data ->
st_ok src0segs E ss_h1 ms -> aa_MR API L' A' (ms_mem ms) md -> (II A') -> md_ok inp md ->
crealizes src0_msyms (mkCfg ms md) (diag msg_overrun (in_fs inp)).
Proof using AX FCF HB HW Hcap0 Hid Hub TBL.
intros E ms md (HEd & HE13 & HE26) HAN HL Hov HS0 HMR Hres Hmd.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hlz & _).
pose proof (proj1 (proj2 Hmd)) as Hch.
assert (Hin : In (b0, cap0) (user_blocks A')) by (rewrite Hub; left; reflexivity).
pose proof (mr_blocks _ _ (aa_laws API) L' A' (ms_mem ms) md b0 cap0 0 HMR Hin ltac:(lia)) as (_ & Hq1 & Hq2 & _).
assert (Hac : alloc_ceiling < 2 ^ 47) by (pose proof YM05.alloc_ceiling_val; lia). unfold dlen in HL, Hov, HLc.
assert (HS : st_ok src0segs E ss_ov ms).
{ apply (st_ok_add_cond src0segs E ss_h1 ms BC_LTU (SOff 27 0) sv_cl6 HS0).
destruct (list_len2 data ltac:(lia)) as (d0 & d1 & rest & Ed).
pose proof (config_len_bound data) as Hcl.
rewrite branch_ltu_U, (U_cl6 E d0 d1 rest) by (rewrite HEd; exact Ed).
rewrite U_SOff, HE26, Z.add_0_r, zcanon_id by (unfold M64; lia).
apply Z.ltb_lt. rewrite <- Ed. lia. }
clear HS0. unfold diag, wr, ex.
cmsg_free_exit HS HMR Hch Hmd Hin HE13 E ss_swO ss_sfO L_sfO RS_sfO site_sfO statics_sfO exit_sfO a0_sfO Hres.
Qed.
End e.
End d.
