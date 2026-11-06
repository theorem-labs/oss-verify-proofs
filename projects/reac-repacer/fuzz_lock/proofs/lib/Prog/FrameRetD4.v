(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: the twin of lib/Reusable/YL0z.v (return value of the fuzz target 0 or -1) *)
(* Donor: reac-repacer/fuzz_lock, proofs/reac-repacer/fuzz_lock/lib/Reusable/YL0z.v at 901d1549395.
   Module: OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Prog.FrameRetD4. *)
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Prog Require Import FrameRet FrameRetD1 FrameRetD2 FrameRetD3.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YK11 YK0o YK0h YK0i YK14 YK1b YK1a YK15 YK0k YK0n YK0p YP0n YM06 YM02.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YO0i YO0f YO0x YO0d YO0e YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO06.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YH00 YH01 YH03 YH02 YN3e.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YN03 YL07 YL01 YL08 YL0d YL0e YL0f YL02 YL0a YL00 YL04 YL0c YL09 YL05 YL0g YL0k YL0o YL0m YL0u YL0r YL0s.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YI06 YI16 YI14 YI5b YI5c YL0i YL06 YL03 YL0l YL0t GIWalk.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YL11 YL10 YL16 YL17 YL18 YL19 YL12 YL13 YL14 YL15 YL0z.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Section c.
Variable API : AllocAPI src0_msyms.
Hypothesis AX : AllocExtra src0_msyms (aa_MR API).
Variable GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop.
Variable RI : list byte -> nat -> list (Z * Z) -> astate -> Prop.
Variable OUT : list byte -> list byte.
Variable rt : list byte -> Z.
Hypothesis GIL : G_local_T src0segs src0_G GI.
Hypothesis GI0 : forall mem, G_img src0segs src0_G mem -> GI 0%nat [] mem.
Hypothesis LIBX : lib_contract_x_R_all_r src0_msyms API rt RI src0_G src0_R GI OUT LIBPC RA_LIB EMPTY LIB_STACK.
Hypothesis HLS : forall pl fs K, LIBK pl fs K = K (LL (rt pl) fs []).
Hypothesis HR01 : forall pl, rt pl = 0 \/ rt pl = -1.
Hypothesis ARMS : arms_m1.
Hypothesis FRM : frm_zero fp_csr.
Variables (sp tid : word) (a0 path : list byte) (inp : ProcInput) (data : list byte) (rnd : EntryDraw).
Hypothesis HSA0 : forall G, anchored_atoms G = anchored_atoms RD_facts -> stack_anchored (E_main sp [a0; path] (in_envp inp) tid rnd) G.
Hypothesis Hvfs : valid_fs (in_fs inp).
Hypothesis Hsp47 : bv_unsigned sp <= 2 ^ 47.
Lemma run_from_QX_r : forall cap0 L' A' b0 E ms md (K : dleaf * astate -> TSet),
user_blocks A' = [(b0, cap0)] -> 65536 <= cap0 <= 67108864 ->
WF A' -> bounded A' -> st_init_done A' = true ->
6 + config_len data <= dlen data -> dlen data < cap0 ->
run_env E data (ptr_addr L' b0) -> env_top E ->
st_ok src0segs E (if config_len data =? 0 then sQ0 else sQ1) ms ->
aa_MR API L' A' (ms_mem ms) md -> md_invX (in_fs inp) md ->
blk_data src0_msyms (ms_mem ms) (ptr_addr L' b0) data ->
jinv K (driver_tail data (RdLoaded b0 cap0) A') -> gtree mgrant (driver_tail data (RdLoaded b0 cap0) A') ->
leaves (run_RI RI (payload data)) (driver_tail data (RdLoaded b0 cap0) A') ->
(forall r, t_eq (K r) (leaf_shapeX_r data (in_fs inp) r)) ->
realizes src0segs (mkCfg ms md) (tset (driver_tail data (RdLoaded b0 cap0) A') K).
Proof.
intros cap0 L' A' b0 E ms md K Hub Hcap0 HW HB Hid Hok HLc HE HT HS HMR Hmd HD HJ HG HL HK.
destruct (HR01 (payload data)) as [Hr0 | Hrm].
{ (* every call on this payload returns 0: the kit's dispatch, Reusable/YL0z.v run_from_QX, on the payloads where rt is 0 *)
pose proof (lib_contract_x_R_all_of_r src0_msyms API rt RI src0_G src0_R GI OUT LIBPC RA_LIB EMPTY LIB_STACK LIBX) as LIBX0.
assert (HLS0 : forall fs K', LIBK (payload data) fs K' = K' (LL 0 fs [])) by (intros fs K'; rewrite HLS, Hr0; reflexivity).
assert (HK0 : forall r, t_eq (K r) (leaf_shapeX data (in_fs inp) r))
  by (intros r; rewrite <- (leaf_shapeX_r_of_0 data HLS0); apply HK).
assert (HL0 : leaves (run_RI (fun pl j T A => RI pl j T A /\ rt pl = 0) (payload data)) (driver_tail data (RdLoaded b0 cap0) A')).
{ eapply leaves_mono; [| exact HL]. intros [d A] H. unfold run_RI in *. cbn [fst snd] in *.
  destruct d; cbv beta iota in H |- *; try exact I. exact (conj H Hr0). }
clear HK HL.
eapply (run_from_QX API AX GI (fun pl j T A => RI pl j T A /\ rt pl = 0) OUT); eassumption. }
{ (* every call on this payload returns -1: the -1 arms, on the payloads where rt is -1 *)
pose (RIm := fun pl j T A => RI pl j T A /\ rt pl = -1).
pose proof (lib_contract_x_R_all_c_of_r src0_msyms API (-1) rt RI src0_G src0_R GI OUT LIBPC RA_LIB EMPTY LIB_STACK LIBX) as LIBXm.
assert (HLm : leaves (run_RI RIm (payload data)) (driver_tail data (RdLoaded b0 cap0) A')).
{ eapply leaves_mono; [| exact HL]. intros [d A] H. unfold run_RI in *. cbn [fst snd] in *.
  destruct d; cbv beta iota in H |- *; try exact I. exact (conj H Hrm). }
clear HL. rename HLm into HL.
destruct ARMS as (A0E1 & A0M1 & A1E1 & A1E2 & A1E3 & A1E4 & A1M1 & A1M2 & A1M3 & A1M4).
pose proof (config_len_bound data) as Hclb.
destruct (Z.eq_dec (payload_len data) 0) as [Hpl0 | Hplnz].
-
pose proof (res_of_tail_none (run_RI RIm (payload data)) data b0 cap0 A' HL Hok Hpl0) as HRb. cbn [run_RI fst snd] in HRb.
rewrite (driver_tail_run_eq data b0 cap0 A') by (unfold HDR_MIN; lia).
change (tset (ret (DL_run b0 cap0 None) A') K) with (K (DL_run b0 cap0 None, A')).
apply (rz_conseq _ _ (leaf_shapeX_r data (in_fs inp) (DL_run b0 cap0 None, A')) _); [| apply t_eq_sym; apply HK].
destruct (Z.eqb_spec (config_len data) 0) as [Hz | Hz].
+ assert (Hc : calls data = 1%nat) by (unfold calls, cfg_byte; rewrite (proj2 (Z.eqb_eq _ _) Hz); reflexivity).
exact (A0E1 fx rc LS API AX GI RIm OUT GIL GI0 LIBXm FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl0 E ms _ HE HT HS HMR Hmd HRb).
+ pose proof (calls_bound data) as Hcb.
destruct (calls data) as [|[|[|[|[|n]]]]] eqn:Hc; try lia.
* exact (A1E1 fx rc LS API AX GI RIm OUT GIL GI0 LIBXm FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl0 E ms _ HE HT HS HMR Hmd HRb).
* exact (A1E2 fx rc LS API AX GI RIm OUT GIL GI0 LIBXm FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl0 E ms _ HE HT HS HMR Hmd HRb).
* exact (A1E3 fx rc LS API AX GI RIm OUT GIL GI0 LIBXm FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl0 E ms _ HE HT HS HMR Hmd HRb).
* exact (A1E4 fx rc LS API AX GI RIm OUT GIL GI0 LIBXm FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl0 E ms _ HE HT HS HMR Hmd HRb).
-
assert (Hpl : 0 < payload_len data) by (unfold payload_len, HDR_MIN in *; lia).
assert (Heq := driver_tail_loaded_eq data b0 cap0 A'
ltac:(apply Z.ltb_ge; unfold HDR_MIN; lia) ltac:(apply Z.ltb_ge; unfold HDR_MIN; lia) ltac:(apply Z.eqb_neq; exact Hplnz)).
rewrite (tset_bind_eq _ _ _ _ _ Heq).
pose proof (jinv_head_eq _ _ _ _ _ Heq HJ) as HJ'. pose proof (gtree_head_eq _ _ _ _ _ Heq HG) as HG'.
pose proof (res_of_tail_some (run_RI RIm (payload data)) data b0 cap0 A' HL Hok Hplnz) as HRb.
assert (HRb' : forall tr q A2, cpath (malloc (payload_len data) A') tr (Some q, A2) -> RIm (payload data) 0%nat [] A2)
by (intros tr q A2 Hp; exact (HRb tr (Some q, A2) Hp)).
assert (HK' : forall r : option sptr * astate,
t_eq (tset (let '(a, s') := r in payload_k b0 cap0 a s') K) (leaf_shapeX_r data (in_fs inp) (payload_leaf b0 cap0 r))).
{ intros [[q|] s']; cbn [payload_k payload_leaf fst snd]; apply HK. }
destruct (Z.eqb_spec (config_len data) 0) as [Hz | Hz].
+ assert (Hc : calls data = 1%nat) by (unfold calls, cfg_byte; rewrite (proj2 (Z.eqb_eq _ _) Hz); reflexivity).
exact (A0M1 fx rc LS API AX GI RIm OUT GIL GI0 LIBXm FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl E ms _ HE HT HS HMR Hmd HD HRb' _ HJ' HG' HK').
+ pose proof (calls_bound data) as Hcb.
destruct (calls data) as [|[|[|[|[|n]]]]] eqn:Hc; try lia.
* exact (A1M1 fx rc LS API AX GI RIm OUT GIL GI0 LIBXm FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl E ms _ HE HT HS HMR Hmd HD HRb' _ HJ' HG' HK').
* exact (A1M2 fx rc LS API AX GI RIm OUT GIL GI0 LIBXm FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl E ms _ HE HT HS HMR Hmd HD HRb' _ HJ' HG' HK').
* exact (A1M3 fx rc LS API AX GI RIm OUT GIL GI0 LIBXm FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl E ms _ HE HT HS HMR Hmd HD HRb' _ HJ' HG' HK').
* exact (A1M4 fx rc LS API AX GI RIm OUT GIL GI0 LIBXm FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl E ms _ HE HT HS HMR Hmd HD HRb' _ HJ' HG' HK').
}
Qed.
Lemma post_from_h1X_r : forall cap0 L' A' b0 E ms md (K : dleaf * astate -> TSet),
user_blocks A' = [(b0, cap0)] -> 65536 <= cap0 <= 67108864 ->
WF A' -> bounded A' -> st_init_done A' = true ->
6 + config_len data <= dlen data -> dlen data < cap0 ->
hdr_env E data (ptr_addr L' b0) -> hdr_anch E -> env_top E ->
st_ok src0segs E ss_h1 ms -> aa_MR API L' A' (ms_mem ms) md -> md_invX (in_fs inp) md ->
blk_data src0_msyms (ms_mem ms) (ptr_addr L' b0) data ->
jinv K (driver_tail data (RdLoaded b0 cap0) A') -> gtree mgrant (driver_tail data (RdLoaded b0 cap0) A') ->
leaves (run_RI RI (payload data)) (driver_tail data (RdLoaded b0 cap0) A') ->
(forall r, t_eq (K r) (leaf_shapeX_r data (in_fs inp) r)) ->
realizes src0segs (mkCfg ms md) (tset (driver_tail data (RdLoaded b0 cap0) A') K).
Proof.
intros cap0 L' A' b0 E ms md K Hub Hcap0 HW HB Hid Hok HLc HE HAN HT HS HMR Hmd HD HJ HG HL HK.
assert (Hin : In (b0, cap0) (user_blocks A')) by (rewrite Hub; left; reflexivity).
pose proof (mr_blocks _ _ (aa_laws API) L' A' (ms_mem ms) md b0 cap0 0 HMR Hin ltac:(lia)) as (_ & Hq1 & Hq2 & _).
assert (Hac : alloc_ceiling < 2 ^ 47) by (pose proof YM05.alloc_ceiling_val; lia).
pose proof (config_len_bound data) as Hclb.
apply (src0_to_P API AX data cap0 L' A' b0 E md Hub Hcap0 HE HAN ms _ Hok HLc HS HMR HD).
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
apply (src0_P_to_QX API AX data cap0 L' A' b0 md Hub Hok HLc _ ms3 _ HRE HS3 HMR3 HD3).
intros ms4 HS4 HMR4 HD4. clear HS3 HMR3 HD3.
exact (run_from_QX_r cap0 L' A' b0 _ ms4 md K Hub Hcap0 HW HB Hid Hok HLc HRE HTE HS4 HMR4 Hmd HD4 HJ HG HL HK).
Qed.
Lemma post_from_h0X_r : forall cap0 L' A' b0 E ms md (K : dleaf * astate -> TSet),
user_blocks A' = [(b0, cap0)] -> 65536 <= cap0 <= 67108864 ->
WF A' -> bounded A' -> st_init_done A' = true ->
dlen data < cap0 ->
hdr_env E data (ptr_addr L' b0) -> hdr_anch E -> env_top E ->
st_ok src0segs E ss_h0 ms -> aa_MR API L' A' (ms_mem ms) md -> md_invX (in_fs inp) md ->
blk_data src0_msyms (ms_mem ms) (ptr_addr L' b0) data ->
jinv K (driver_tail data (RdLoaded b0 cap0) A') -> gtree mgrant (driver_tail data (RdLoaded b0 cap0) A') ->
leaves (run_RI RI (payload data)) (driver_tail data (RdLoaded b0 cap0) A') ->
(forall r, t_eq (K r) (leaf_shapeX_r data (in_fs inp) r)) ->
realizes src0segs (mkCfg ms md) (tset (driver_tail data (RdLoaded b0 cap0) A') K).
Proof.
intros cap0 L' A' b0 E ms md K Hub Hcap0 HW HB Hid HLc HE HAN HT HS HMR Hmd0 HD HJ HG HL HK.
pose proof (md_invX_inv _ _ Hmd0 : md_ok inp md) as Hmd.
pose proof (config_len_bound data) as Hclb.
assert (Hnn : 0 <= dlen data) by (unfold dlen; lia).
destruct (Z_lt_le_dec (dlen data) 6) as [Hshort | Hhdr].
-
rewrite (driver_tail_short_eq data b0 cap0 A') by (unfold HDR_MIN; exact Hshort).
change (tset (ret DL_short A') K) with (K (DL_short, A')).
apply (rz_conseq _ _ (leaf_shapeX_r data (in_fs inp) (DL_short, A')) _); [| apply t_eq_sym; apply HK].
cbn [leaf_shapeX_r leaf_shape fst].
exact (src0_short_tail API AX inp data cap0 L' A' b0 Hub Hcap0 HW HB Hid E ms md HE HAN ltac:(lia) HS HMR Hmd).
-
apply (src0_to_h1 API AX data cap0 L' A' b0 Hub Hcap0 HLc E ms md _ HE HAN Hhdr HS HMR HD).
intros ms2 HS2 HMR2 HD2. clear HS HMR HD.
destruct (Z_lt_le_dec (dlen data) (6 + config_len data)) as [Hov | Hok].
+
rewrite (driver_tail_overrun_eq data b0 cap0 A') by (unfold HDR_MIN; lia).
change (tset (ret DL_overrun A') K) with (K (DL_overrun, A')).
apply (rz_conseq _ _ (leaf_shapeX_r data (in_fs inp) (DL_overrun, A')) _); [| apply t_eq_sym; apply HK].
cbn [leaf_shapeX_r leaf_shape fst].
exact (src0_overrun_tail API AX inp data cap0 L' A' b0 Hub Hcap0 HW HB Hid E ms2 md HE HAN Hhdr Hov HS2 HMR2 Hmd).
+ exact (post_from_h1X_r cap0 L' A' b0 E ms2 md K Hub Hcap0 HW HB Hid Hok HLc HE HAN HT HS2 HMR2 Hmd0 HD2 HJ HG HL HK).
Qed.
Theorem src0_postX_r : forall K : dleaf * astate -> TSet,
(forall r, t_eq (K r) (leaf_shapeX_r data (in_fs inp) r)) ->
POST API sp tid a0 path inp data rnd (run_RI RI (payload data)) K.
Proof.
intros K HK. unfold POST. cbv zeta beta.
intros cap' bufp' A' Lc' J' g' len0 w ms' md' HLc Hcap Hlen0 Hub HW HB Hid HS Hw HL0 HMR Hmd0 HD HJ HG HL.
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
drv_run_with src0tbl_ok HS HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E ss_h0 msx) in HS end.
lazymatch type of HF with frame_of _ ?rs0 ?m0 ?m1 =>
pose proof (blk_data_after_frame src0_msyms (aa_MR API) (aa_laws API) AX Lc' A' m0 m1 _ E (ss_facts ss_h0) src0_keep rs0 bufp' cap' (ptr_addr Lc' bufp') data HMR
ltac:(destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & HG0); exact HG0) ltac:(drv_anch) ltac:(vm_compute; reflexivity) HF Hin ltac:(lia) ltac:(unfold dlen in HLc; lia)) as HD';
specialize (HD' HD); clear HD; rename HD' into HD end.
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep E HS HF HMR.
lazymatch type of HS with st_ok _ _ _ ?msx =>
assert (HT : env_top E) by (subst E; unfold env_top; rewrite ew_ewset_other by lia; rewrite ew_lp; cbn; exact Hsp47);
exact (post_from_h0X_r cap' Lc' A' bufp' E msx md' K Hub ltac:(lia) HW HB Hid HLc HE HAN HT HS HMR Hmd HD HJ HG HL HK) end.
Qed.
End c.
End b.
