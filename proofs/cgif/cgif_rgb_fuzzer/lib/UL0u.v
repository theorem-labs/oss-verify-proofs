(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0p YK0i YK0j YK14 YK1b YK1a YK15 YK0l YK0o YK0q YQ0k YN06 YN02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ0a YQ04 YQ0d YQ05 YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e YP07.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH05 UH07 UH06 UO3p.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO04 YL05 YL01 UL06 YL0b YL0c YL0d YL02 YL08 YL00 YL03 YL0a YL07 YL04 YL0e UL0g UL0k UL0i UL0h UL0p UL0n UL0o.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UL0w UL0v UL11 UL12 UL13 UL14 UL0x UL0y UL0z UL10.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma driver_tail_short_eq : forall data buf cap s,
dlen data < HDR_MIN -> driver_tail data (RdLoaded buf cap) s = ret DL_short s.
Proof. intros data buf cap s H. unfold driver_tail. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity. Qed.
Lemma driver_tail_overrun_eq : forall data buf cap s,
HDR_MIN <= dlen data -> dlen data < HDR_MIN + config_len data ->
driver_tail data (RdLoaded buf cap) s = ret DL_overrun s.
Proof.
intros data buf cap s H1 H2. unfold driver_tail.
rewrite (proj2 (Z.ltb_ge _ _) H1), (proj2 (Z.ltb_lt _ _) H2). reflexivity.
Qed.
Lemma driver_tail_run_eq : forall data buf cap s,
HDR_MIN <= dlen data -> HDR_MIN + config_len data <= dlen data -> payload_len data = 0 ->
driver_tail data (RdLoaded buf cap) s = ret (DL_run buf cap None) s.
Proof.
intros data buf cap s H1 H2 H3. unfold driver_tail.
rewrite (proj2 (Z.ltb_ge _ _) H1), (proj2 (Z.ltb_ge _ _) H2), (proj2 (Z.eqb_eq _ _) H3). reflexivity.
Qed.
Section c.
Variable API : AllocAPI ubs2_msyms.
Hypothesis AX : AllocExtra ubs2_msyms (aa_MR API).
Hypothesis LIB : lib_contract_all ubs2_msyms API LIBPC RA_LIB EMPTY LIB_STACK_RGB.
Hypothesis FRM : frm_zero fp_csr.
Variables (sp tid : word) (a0 path : list byte) (inp : ProcInput) (data : list byte) (rnd : EntryDraw).
Hypothesis HSA0 : forall G, anchored_atoms G = anchored_atoms RD_facts -> stack_anchored (E_main sp [a0; path] (in_envp inp) tid rnd) G.
Lemma run_from_Q : forall cap0 L' A' b0 E ms md (K : dleaf * astate -> TSet),
user_blocks A' = [(b0, cap0)] -> 65536 <= cap0 <= 67108864 ->
WF A' -> bounded A' -> st_init_done A' = true ->
6 + config_len data <= dlen data -> dlen data < cap0 ->
run_env E data (ptr_addr L' b0) ->
st_ok ubs2segs E (if config_len data =? 0 then sQ0 else sQ1) ms ->
aa_MR API L' A' (ms_mem ms) md -> md_inv (in_fs inp) md ->
jinv K (driver_tail data (RdLoaded b0 cap0) A') -> gtree mgrant (driver_tail data (RdLoaded b0 cap0) A') ->
(forall r, t_eq (K r) (leaf_shape data (in_fs inp) r)) ->
realizes ubs2segs (mkCfg ms md) (tset (driver_tail data (RdLoaded b0 cap0) A') K).
Proof.
intros cap0 L' A' b0 E ms md K Hub Hcap0 HW HB Hid Hok HLc HE HS HMR Hmd HJ HG HK.
pose proof (config_len_bound data) as Hclb.
destruct (Z.eq_dec (payload_len data) 0) as [Hpl0 | Hplnz].
-
rewrite (driver_tail_run_eq data b0 cap0 A') by (unfold HDR_MIN; lia).
change (tset (ret (DL_run b0 cap0 None) A') K) with (K (DL_run b0 cap0 None, A')).
apply (rz_conseq _ _ (leaf_shape data (in_fs inp) (DL_run b0 cap0 None, A')) _); [| apply t_eq_sym; apply HK].
destruct (Z.eqb_spec (config_len data) 0) as [Hz | Hz].
+ assert (Hc : calls data = 1%nat) by (unfold calls, cfg_byte; rewrite (proj2 (Z.eqb_eq _ _) Hz); reflexivity).
exact (ubs2_run_0E1 API AX LIB FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok Hz Hc Hpl0 E ms _ HE HS HMR Hmd).
+ pose proof (calls_bound data) as Hcb.
destruct (calls data) as [|[|[|[|[|n]]]]] eqn:Hc; try lia.
* exact (ubs2_run_1E1 API AX LIB FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl0 E ms _ HE HS HMR Hmd).
* exact (ubs2_run_1E2 API AX LIB FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl0 E ms _ HE HS HMR Hmd).
* exact (ubs2_run_1E3 API AX LIB FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl0 E ms _ HE HS HMR Hmd).
* exact (ubs2_run_1E4 API AX LIB FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl0 E ms _ HE HS HMR Hmd).
-
assert (Hpl : 0 < payload_len data) by (unfold payload_len, HDR_MIN in *; lia).
assert (Heq := driver_tail_loaded_eq data b0 cap0 A'
ltac:(apply Z.ltb_ge; unfold HDR_MIN; lia) ltac:(apply Z.ltb_ge; unfold HDR_MIN; lia) ltac:(apply Z.eqb_neq; exact Hplnz)).
rewrite (tset_bind_eq _ _ _ _ _ Heq).
pose proof (jinv_head_eq _ _ _ _ _ Heq HJ) as HJ'. pose proof (gtree_head_eq _ _ _ _ _ Heq HG) as HG'.
assert (HK' : forall r : option sptr * astate,
t_eq (tset (let '(a, s') := r in payload_k b0 cap0 a s') K) (leaf_shape data (in_fs inp) (payload_leaf b0 cap0 r))).
{ intros [[q|] s']; cbn [payload_k payload_leaf fst snd]; apply HK. }
destruct (Z.eqb_spec (config_len data) 0) as [Hz | Hz].
+ assert (Hc : calls data = 1%nat) by (unfold calls, cfg_byte; rewrite (proj2 (Z.eqb_eq _ _) Hz); reflexivity).
exact (ubs2_run_0M1 API AX LIB FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl E ms _ HE HS HMR Hmd _ HJ' HG' HK').
+ pose proof (calls_bound data) as Hcb.
destruct (calls data) as [|[|[|[|[|n]]]]] eqn:Hc; try lia.
* exact (ubs2_run_1M1 API AX LIB FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl E ms _ HE HS HMR Hmd _ HJ' HG' HK').
* exact (ubs2_run_1M2 API AX LIB FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl E ms _ HE HS HMR Hmd _ HJ' HG' HK').
* exact (ubs2_run_1M3 API AX LIB FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl E ms _ HE HS HMR Hmd _ HJ' HG' HK').
* exact (ubs2_run_1M4 API AX LIB FRM data (in_fs inp) cap0 L' A' b0 Hub Hcap0 HW HB Hid Hok HLc Hz Hc Hpl E ms _ HE HS HMR Hmd _ HJ' HG' HK').
Qed.
Lemma post_from_h1 : forall cap0 L' A' b0 E ms md (K : dleaf * astate -> TSet),
user_blocks A' = [(b0, cap0)] -> 65536 <= cap0 <= 67108864 ->
WF A' -> bounded A' -> st_init_done A' = true ->
6 + config_len data <= dlen data -> dlen data < cap0 ->
hdr_env E data (ptr_addr L' b0) -> hdr_anch E ->
st_ok ubs2segs E ss_h1 ms -> aa_MR API L' A' (ms_mem ms) md -> md_ok inp md ->
blk_data ubs2_msyms (ms_mem ms) (ptr_addr L' b0) data ->
jinv K (driver_tail data (RdLoaded b0 cap0) A') -> gtree mgrant (driver_tail data (RdLoaded b0 cap0) A') ->
(forall r, t_eq (K r) (leaf_shape data (in_fs inp) r)) ->
realizes ubs2segs (mkCfg ms md) (tset (driver_tail data (RdLoaded b0 cap0) A') K).
Proof.
intros cap0 L' A' b0 E ms md K Hub Hcap0 HW HB Hid Hok HLc HE HAN HS HMR Hmd HD HJ HG HK.
assert (Hin : In (b0, cap0) (user_blocks A')) by (rewrite Hub; left; reflexivity).
pose proof (mr_blocks _ _ (aa_laws API) L' A' (ms_mem ms) md b0 cap0 0 HMR Hin ltac:(lia)) as (_ & Hq1 & Hq2 & _).
assert (Hac : alloc_ceiling < 2 ^ 47) by (pose proof YN05.alloc_ceiling_val; lia).
pose proof (config_len_bound data) as Hclb.
apply (ubs2_to_P API AX data cap0 L' A' b0 E md Hub Hcap0 HE HAN ms _ Hok HLc HS HMR HD).
intros ms3 HS3 HMR3 HD3. clear HS HMR HD.
destruct HE as (HEd & HE13 & HE26).
assert (HRE : run_env (E_P E data (ptr_addr L' b0 + 2 + config_len data)) data (ptr_addr L' b0)).
{ unfold run_env. split; [| split; [| split; [| split]]].
- rewrite E_P_ed by lia. exact HEd.
- rewrite E_P_old by lia. exact HE13.
- rewrite E_P_old by lia. exact HE26.
- apply E_P_46. lia.
- apply (hdr_anch_ext E _ HAN). intros n Hn. apply E_P_old. lia. }
apply (ubs2_P_to_Q API AX data L' A' b0 md Hok _ ms3 _ HRE HS3 HMR3).
intros ms4 HS4 HMR4. clear HS3 HMR3 HD3.
exact (run_from_Q cap0 L' A' b0 _ ms4 md K Hub Hcap0 HW HB Hid Hok HLc HRE HS4 HMR4 Hmd HJ HG HK).
Qed.
Lemma post_from_h0 : forall cap0 L' A' b0 E ms md (K : dleaf * astate -> TSet),
user_blocks A' = [(b0, cap0)] -> 65536 <= cap0 <= 67108864 ->
WF A' -> bounded A' -> st_init_done A' = true ->
dlen data < cap0 ->
hdr_env E data (ptr_addr L' b0) -> hdr_anch E ->
st_ok ubs2segs E ss_h0 ms -> aa_MR API L' A' (ms_mem ms) md -> md_ok inp md ->
blk_data ubs2_msyms (ms_mem ms) (ptr_addr L' b0) data ->
jinv K (driver_tail data (RdLoaded b0 cap0) A') -> gtree mgrant (driver_tail data (RdLoaded b0 cap0) A') ->
(forall r, t_eq (K r) (leaf_shape data (in_fs inp) r)) ->
realizes ubs2segs (mkCfg ms md) (tset (driver_tail data (RdLoaded b0 cap0) A') K).
Proof.
intros cap0 L' A' b0 E ms md K Hub Hcap0 HW HB Hid HLc HE HAN HS HMR Hmd HD HJ HG HK.
pose proof (config_len_bound data) as Hclb.
assert (Hnn : 0 <= dlen data) by (unfold dlen; lia).
destruct (Z_lt_le_dec (dlen data) 6) as [Hshort | Hhdr].
-
rewrite (driver_tail_short_eq data b0 cap0 A') by (unfold HDR_MIN; exact Hshort).
change (tset (ret DL_short A') K) with (K (DL_short, A')).
apply (rz_conseq _ _ (leaf_shape data (in_fs inp) (DL_short, A')) _); [| apply t_eq_sym; apply HK].
cbn [leaf_shape fst].
exact (ubs2_short_tail API AX inp data cap0 L' A' b0 Hub Hcap0 HW HB Hid E ms md HE HAN ltac:(lia) HS HMR Hmd).
-
apply (ubs2_to_h1 API AX data cap0 L' A' b0 Hub Hcap0 HLc E ms md _ HE HAN Hhdr HS HMR HD).
intros ms2 HS2 HMR2 HD2. clear HS HMR HD.
destruct (Z_lt_le_dec (dlen data) (6 + config_len data)) as [Hov | Hok].
+
rewrite (driver_tail_overrun_eq data b0 cap0 A') by (unfold HDR_MIN; lia).
change (tset (ret DL_overrun A') K) with (K (DL_overrun, A')).
apply (rz_conseq _ _ (leaf_shape data (in_fs inp) (DL_overrun, A')) _); [| apply t_eq_sym; apply HK].
cbn [leaf_shape fst].
exact (ubs2_overrun_tail API AX inp data cap0 L' A' b0 Hub Hcap0 HW HB Hid E ms2 md HE HAN Hhdr Hov HS2 HMR2 Hmd).
+ exact (post_from_h1 cap0 L' A' b0 E ms2 md K Hub Hcap0 HW HB Hid Hok HLc HE HAN HS2 HMR2 Hmd HD2 HJ HG HK).
Qed.
Theorem ubs2_post : forall K : dleaf * astate -> TSet,
(forall r, t_eq (K r) (leaf_shape data (in_fs inp) r)) ->
POST API sp tid a0 path inp data rnd K.
Proof.
intros K HK. unfold POST. cbv zeta beta.
intros cap' bufp' A' Lc' J' g' len0 w ms' md' HLc Hcap Hlen0 Hub HW HB Hid HS Hw HL0 HMR Hmd HD HJ HG.
unfold MAX_INPUT in Hcap. subst len0.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hlz & _).
assert (Hin : In (bufp', cap') (user_blocks A')) by (rewrite Hub; left; reflexivity).
pose proof (mr_blocks _ _ (aa_laws API) Lc' A' (ms_mem ms') md' bufp' cap' 0 HMR Hin ltac:(lia)) as (_ & Hq1 & Hq2 & _).
assert (Hac : alloc_ceiling < 2 ^ 47) by (pose proof YN05.alloc_ceiling_val; lia).
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
drv_run_with ubs2tbl_ok HS HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok ubs2segs E ss_h0 msx) in HS end.
lazymatch type of HF with frame_of _ ?rs0 ?m0 ?m1 =>
pose proof (blk_data_after_frame ubs2_msyms (aa_MR API) (aa_laws API) AX Lc' A' m0 m1 _ E (ss_facts ss_h0) ubs2_keep rs0 bufp' cap' (ptr_addr Lc' bufp') data HMR
ltac:(destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & HG0); exact HG0) ltac:(drv_anch) ltac:(vm_compute; reflexivity) HF Hin ltac:(lia) ltac:(unfold dlen in HLc; lia)) as HD';
specialize (HD' HD); clear HD; rename HD' into HD end.
drv_mr (MR_after_frame ubs2_msyms (aa_MR API) (aa_laws API) AX) ubs2_keep E HS HF HMR.
lazymatch type of HS with st_ok _ _ _ ?msx =>
exact (post_from_h0 cap' Lc' A' bufp' E msx md' K Hub ltac:(lia) HW HB Hid HLc HE HAN HS HMR Hmd HD HJ HG HK) end.
Qed.
End c.
End b.
