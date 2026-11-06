(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/Q/YW0a.v, with its module names changed; 15 of its 38 lines of code are new or changed and 50 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/Q/YT01.v, with its module paths and module names changed; 208 of its 230 lines of code are new or changed and 16 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK15 YK0n YP0n YM06 YK0s YM02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a YO0b YO0c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YH00 YH03 YH02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0g YO0w YO0s YO0u YO15 YO10 YO0t YO0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN03 YN02_cf YN2b YN08_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN0b_cf YN07_cf YN0a_cf YN1y_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import AllocRealloc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.Q Require Import YW04_cf YW0e_cf YW07_cf YW0b_cf YW08_cf YW09_cf YY00_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.Q Require Import YX00_cf YX01_cf YX02_cf YX03_cf YX04_cf YX05_cf YX06_cf YX07_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM06_cf YO0d_cf YN2b_cf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma small_tree A g am idx fr n : WF A -> usedX [] A g am -> 0 <= idx <= am_last am -> ss_fr (nth_slot am idx) = Some fr ->
am_sc am < 48 -> 0 <= n < 2 ^ 62 ->
realloc (Some (frame_ptr am idx fr)) n A =
if ra_c1 am (fr_off fr) n then IRet (Some (frame_ptr am idx fr), A_ip A g am idx fr n) else realloc_move (frame_ptr am idx fr) n A.
Proof.
intros HW Hu Hi Hfr Hsc Hn.
unfold realloc. replace (size_overflows n) with false by (unfold size_overflows; symmetry; apply Z.leb_gt; lia).
unfold bind. rewrite (ra_ffe _ A (g, idx) (find_frame_in_spec [] None U0 A HW g am idx fr Hu Hi Hfr)). cbn [ibind fst snd].
rewrite (ra_getm g A am (proj1 (usedX_MT _ _ _ _ Hu))). cbn [ibind]. rewrite Hfr. cbv beta iota zeta.
unfold ra_c1. destruct ((n <=? stride_of am - IB - UNIT * fr_off fr) && (n <? MMAP_THRESHOLD) && (am_sc am <=? size_to_class n + 1)).
- reflexivity.
- replace ((48 <=? am_sc am) && (MMAP_THRESHOLD <=? n)) with false by (symmetry; apply andb_false_intro1; apply Z.leb_gt; lia). reflexivity.
Qed.
Definition ip_nc (nc : ncase) : Prop := nc = NSmall true \/ exists b1, nc = NMid b1 true.
Section b.
Hypothesis FB : OBL_fb_gen.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (g : sptr) (am : ameta) (idx : Z) (fr : frame) (n : Z) (a : sptr) (ka : Z) (rg : YO0i.region).
Hypothesis HC : small_ctx L A regs mem md g am idx fr n a ka rg.
Local Abbreviation E := (ES L regs g am idx fr a rg n).
Local Abbreviation PP := (ptr_addr L (frame_ptr am idx fr)).
Local Abbreviation KK := (kcase_of am).
Local Abbreviation RC := (rcase_of (reserved_of am fr)).
Lemma Hmd8 : m_halted md = None /\ m_vm_lazy md = [] /\ m_vm_materialized md = [].
Proof using HC. exact (mc_md _ _ _ _ _ (MS L A regs mem md g am idx fr n a ka rg HC)). Qed.
Definition STK8 (x : Z) : Prop := spZ regs - 8256 <= x < spZ regs.
Definition RAW8 (m : word -> option byte) : Prop :=
forall x, 0 <= x < 2 ^ 64 -> ~ STK8 x -> m (Z_to_bv 64 x) = mem (Z_to_bv 64 x).
Lemma raw_frame rs m0 m1 : forallb wr_stk rs = true -> RAW8 m0 -> frame_of E rs m0 m1 -> RAW8 m1.
Proof using HC.
intros Hw R0 HF x Hx Ns. rewrite <- (R0 x Hx Ns). apply HF. rewrite lit64_small by exact Hx. intros W.
apply (wr_stack_only _ _ _ Hw) in W. rewrite (base_SPS L A regs mem md g am idx fr n a ka rg HC) in W. apply Ns. exact W.
Qed.
Lemma raw_entry m1 : frame_of E (entry_memS KK RC) mem m1 -> RAW8 m1.
Proof using HC. intros HF. apply (raw_frame _ mem m1 (wr_entry_mem KK RC)); [intros x _ _; reflexivity | exact HF]. Qed.
Lemma to_malloc ss4 ms4 :
st_ok src0segs E ss4 ms4 -> ss_pc ss4 = src0_A_libc_malloc_impl -> ss_resv ss4 = None ->
view MV ss4 = arr_view RC -> In stk1 (ss_mem ss4) -> RAW8 (ms_mem ms4) ->
mreal_cf src0segs (mkCfg ms4 md) (realloc_move (frame_ptr am idx fr) n A)
(realloc_leaf src0_msyms (MRx src0_msyms) L A regs mem md (frame_ptr am idx fr) (fr_n fr) n).
Proof using FB HC.
intros HS Hpc Hrv Hv Hst RAW. destruct (arrival_fbS L A regs mem md g am idx fr n a ka rg HC ss4 ms4 HS Hpc Hrv Hv Hst RAW) as (SH & FBA).
rewrite SH. exact (FB _ _ _ _ _ _ _ _ _ _ FBA).
Qed.
Lemma in_stk1_mem_at r nc : In stk1 (mem_at r nc).
Proof. destruct nc; cbn [mem_at head_memS app]; repeat (first [left; reflexivity | right]). Qed.
Lemma ip_frame_eq x : PP - 3 < x < PP -> forall mf,
bytes_at src0_msyms mf (PP - 2) 2 (hdr_off16 am idx fr) -> present mf x -> mf (Z_to_bv 64 x) = mem (Z_to_bv 64 x).
Proof using HC.
intros Hx mf Bf [b Pb].
pose proof (FPS L A regs mem md g am idx fr n a ka rg HC) as FP. pose proof (fp_c_p2 _ _ _ _ FP) as B0.
assert (EP : fv_p (vS L regs g am idx fr a rg) = PP).
{ pose proof (XS_P L A regs mem md g am idx fr n a ka rg HC) as V. rewrite <- V. unfold xvS. cbn. reflexivity. }
change (fv_off (vS L regs g am idx fr a rg)) with (hdr_off16 am idx fr) in B0. rewrite EP in B0.
assert (Hm : present mem x).
{ apply (slot_present src0_msyms L A mem md g am idx fr (MS L A regs mem md g am idx fr n a ka rg HC)
(sx_used _ _ _ _ _ _ _ _ _ _ _ _ _ HC) (sx_idx _ _ _ _ _ _ _ _ _ _ _ _ _ HC) (sx_fr _ _ _ _ _ _ _ _ _ _ _ _ _ HC)
(sx_kind _ _ _ _ _ _ _ _ _ _ _ _ _ HC)).
pose proof (geom7 L A regs mem md g am idx fr n a ka rg HC) as (_ & _ & G3 & _). unfold PI, ENDI. lia. }
destruct Hm as [b' Pb']. rewrite Pb, Pb'.
assert (Hk : (Z.to_nat (x - (PP - 2)) < 2)%nat) by lia.
pose proof (Bf _ Hk) as F1. pose proof (B0 _ Hk) as F0.
rewrite Z2Nat.id in F1, F0 by lia. replace (PP - 2 + (x - (PP - 2))) with x in F1, F0 by lia.
unfold mbyte in F1, F0. cbn [ms_segs src0_msyms] in F1. rewrite Pb in F1. rewrite Pb' in F0. congruence.
Qed.
Theorem ip_finish nc t msf : nc_ok am fr n nc -> ip_nc nc -> t = rcase_of (RSS am fr n) ->
st_ok src0segs E (SX KK RC nc t) msf ->
(forall x, 0 <= x < 2 ^ 64 -> ~ STK8 x -> ~ (PP - 3 <= x < PP) -> ~ TWS L am idx fr n x -> ms_mem msf (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) ->
SR_cfv src0segs (mkCfg msf md)
(realloc_leaf src0_msyms (MRx src0_msyms) L A regs mem md (frame_ptr am idx fr) (fr_n fr) n
(Some (frame_ptr am idx fr), A_ip A g am idx fr n)).
Proof using HC.
intros Hok Hnc Ht HS FR.
destruct Hmd8 as (Hh & Hlz & _).
pose proof (fin_readS L A regs mem md g am idx fr n a ka rg HC nc t msf Hok Hnc Ht HS) as FRD. cbv zeta in FRD.
destruct FRD as (B4 & B3 & B2 & BPN & B45 & WS & PRS & RP & A0 & E1 & PCf & Rvf).
pose proof (sx_pre _ _ _ _ _ _ _ _ _ _ _ _ _ HC) as PRE.
pose proof PRE as (MX & HWA & HBA & Hret & Hal & Hceil & Hsp63 & Hstk & Htp & Herrw & _).
pose proof (geom7 L A regs mem md g am idx fr n a ka rg HC) as (G1 & G2 & G3 & GI & GN & GS & GO).
pose proof (nc_c1 am fr n nc Hok) as C1. assert (C1' : ra_c1 am (fr_off fr) n = true) by (rewrite C1; destruct Hnc as [->|[b1 ->]]; reflexivity).
assert (ERSV : RSVI am fr n = RSS am fr n) by reflexivity.
assert (ERC : RCI am fr n = RCS am fr n) by reflexivity.
assert (ETW : forall x, TWI L am idx fr n x <-> TWS L am idx fr n x) by (intros x; unfold TWI, TWS; rewrite ERSV; tauto).
assert (ERRI : forall x, errno_addr src0_msyms <= x < errno_addr src0_msyms + 4 -> in_img1 x).
{ intros x Hx. apply src0_img_range. apply src0_errno_img. exact Hx. }
assert (MS : ip_memspec src0_msyms L A mem g am idx fr n (ms_mem msf) (scratch_k src0_msyms REALLOC_STACK regs)).
{ split.
- intros x Hx. apply (src0_scratch_hi regs x Hceil Hx).
- unfold PI. rewrite ERC. exact B3.
- intros H. unfold PI. exact (BPN H).
- intros H. unfold ENDI. exact (B45 H).
- intros x [->|Hx]; apply PRS; [left; unfold PI; lia | right; apply ETW; exact Hx].
- intros x Hx N1 N2 N3. unfold PI in N1.
destruct (Z_lt_le_dec x (PP - 3)) as [L1|L1]; [|destruct (Z_lt_le_dec x PP) as [L2|L2]].
+ apply FR; [exact Hx | intros S; apply N3; left; exact S | lia | intros T; apply N2; apply ETW; exact T].
+ apply (ip_frame_eq x ltac:(lia) (ms_mem msf) B2). apply PRS. left. lia.
+ apply FR; [exact Hx | intros S; apply N3; left; exact S | lia | intros T; apply N2; apply ETW; exact T]. }
destruct (realloc_ip_leaf src0_msyms L A mem md g am idx fr n (ms_mem msf) (scratch_k src0_msyms REALLOC_STACK regs) MX
(sx_used _ _ _ _ _ _ _ _ _ _ _ _ _ HC) (sx_idx _ _ _ _ _ _ _ _ _ _ _ _ _ HC) (sx_fr _ _ _ _ _ _ _ _ _ _ _ _ _ HC)
(sx_kind _ _ _ _ _ _ _ _ _ _ _ _ _ HC) ltac:(pose proof (sx_n _ _ _ _ _ _ _ _ _ _ _ _ _ HC); lia) C1' MS)
as (MX3 & WF3 & BND3 & FRM3 & BLK3 & Pnz & CNT3 & UB3).
destruct (SX_shape KK RC nc t (kc_small L A regs mem md g am idx fr n a ka rg HC) Hnc) as (Hpc3 & Hrv3 & Hcv3 & _).
assert (V1 : sr_get (ss_regs (SX KK RC nc t)) 1 = SOff 1 0).
{ pose proof Hcv3 as V. unfold callee_view, callee_view0, view in V. cbn [map] in V.
apply (f_equal (fun l => List.nth 0 l (SLit 0))) in V. cbn [List.nth] in V. rewrite lit5 in V by lia. cbn [nat_to_reg] in V. exact V. }
eapply (SR_realloc_ret E _ msf md _ HS Hrv3 Hpc3 V1); [rewrite E1; exact Hret | exact Hh | exact Hlz |].
unfold realloc_leaf. exists L, (ms_regs msf), (ms_mem msf), md. cbn [fst snd].
split; [rewrite E1; reflexivity|].
split.
- unfold call_post_k. change (ms_segs src0_msyms) with src0segs.
split; [exact MX3|]. split; [exact WF3|]. split; [exact BND3|]. split; [apply layout_le_refl|].
split; [intros; reflexivity|]. split; [exact RP|]. split; [exists (m_vmmaps md); apply with_vmmaps_self'|].
split; [| split; [exact BLK3|]].
+ intros x Hx _ _ N3 _. apply FRM3; [exact Hx | exact N3].
+ intros x [Hs|He].
* apply WS. exact Hs.
* pose proof (ERRI x He) as Ix. pose proof (errno_lowS x He) as [X1 X2].
assert (Eq : ms_mem msf (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
{ apply FR; [exact X1 | unfold STK8; unfold REALLOC_STACK, ALLOC_STACK in Hceil; lia | intros Hp; apply (GN x ltac:(lia)); exact Ix |].
intros T. unfold TWS in T. apply (GN x); [destruct T as [[HR0 ->]|[HR5 T]]; pose proof (END_eq L am idx fr) as EQ8; pose proof (sx_n _ _ _ _ _ _ _ _ _ _ _ _ _ HC); unfold RSS, avail_of in *; lia | exact Ix]. }
apply (proj1 (proj2 (same_views src0segs mem (ms_mem msf) x Eq))). apply Herrw. exact He.
- split; [exact A0|]. split; [exact Pnz|]. split; [exact UB3|].
intros i Hi. exact (CNT3 i Hi).
Qed.
Theorem small_main :
mreal_cf src0segs (mkCfg (mkst regs (Z_to_bv 64 src0_A_realloc) mem (seg_rom src0segs)) md)
(realloc (Some (frame_ptr am idx fr)) n A)
(realloc_leaf src0_msyms (MRx src0_msyms) L A regs mem md (frame_ptr am idx fr) (fr_n fr) n).
Proof using FB HC.
destruct Hmd8 as (Hh & Hlz & _).
pose proof (sx_n _ _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hn.
pose proof (kc_small L A regs mem md g am idx fr n a ka rg HC) as Hk.
rewrite (small_tree A g am idx fr n (HWS L A regs mem md g am idx fr n a ka rg HC) (sx_used _ _ _ _ _ _ _ _ _ _ _ _ _ HC)
(sx_idx _ _ _ _ _ _ _ _ _ _ _ _ _ HC) (sx_fr _ _ _ _ _ _ _ _ _ _ _ _ _ HC) (sx_sc _ _ _ _ _ _ _ _ _ _ _ _ _ HC) Hn).
destruct (nc_cover am fr n ltac:(lia)) as [nc Hok].
rewrite (nc_c1 am fr n nc Hok).
assert (Hrange : nc_lo nc <= n <= nc_hi nc).
{ destruct nc as [| |ge|b1 ge]; cbn in Hok |- *; unfold MMAP_THRESHOLD in *; lia. }
pose proof (entry_st_okS L A regs mem md g am idx fr n a ka rg HC nc Hrange (nc_facts_ok L A regs mem md g am idx fr n a ka rg HC nc Hok)) as HS0.
assert (HWR : forall x, PP - 4 <= x <= ptr_addr L (slot_end am idx) -> writable_at src0segs mem x).
{ intros x Hx. apply present_writable.
apply (slot_present src0_msyms L A mem md g am idx fr (MS L A regs mem md g am idx fr n a ka rg HC)
(sx_used _ _ _ _ _ _ _ _ _ _ _ _ _ HC) (sx_idx _ _ _ _ _ _ _ _ _ _ _ _ _ HC) (sx_fr _ _ _ _ _ _ _ _ _ _ _ _ _ HC)
(sx_kind _ _ _ _ _ _ _ _ _ _ _ _ _ HC)). unfold PI, ENDI. exact Hx. }
assert (IPX : forall ms1, ip_nc nc -> st_ok src0segs E (SIP KK RC nc) ms1 -> RAW8 (ms_mem ms1) ->
SR_cfv src0segs (mkCfg ms1 md) (realloc_leaf src0_msyms (MRx src0_msyms) L A regs mem md (frame_ptr am idx fr) (fr_n fr) n
(Some (frame_ptr am idx fr), A_ip A g am idx fr n))).
{ intros ms1 Hnc HS1 RAW1. set (t := rcase_of (RSS am fr n)).
pose proof (exit_st_okS L A regs mem md g am idx fr n a ka rg HC nc t ms1 Hok Hnc eq_refl HWR HS1 RAW1) as HSX.
eapply SR_cfv_bind; [exact (SX_run E ms1 md Hh Hlz KK RC nc t Hk Hnc HSX)|].
intros c' (msf & -> & HSf & HFf).
apply (ip_finish nc t msf Hok Hnc eq_refl HSf).
exact (fin_frameS L A regs mem md g am idx fr n a ka rg HC nc t (ms_mem ms1) (ms_mem msf) Hok Hnc eq_refl RAW1 HFf). }
destruct nc as [| |[]|b1 []].
- apply (mreal_cf_SR_pre src0segs _ _ _ _ (SA_run E _ md Hh Hlz KK RC NBig Hk HS0)).
intros c' (ms1 & -> & HS1 & HF1).
destruct (SA_shape_arr KK RC NBig Hk eq_refl) as (Hpc1 & Hrv1 & Hv1 & Hm1).
apply (to_malloc _ ms1 HS1 Hpc1 Hrv1 Hv1); [rewrite Hm1; apply in_stk1_mem_at | exact (raw_entry _ HF1)].
- apply (mreal_cf_SR_pre src0segs _ _ _ _ (SA_run E _ md Hh Hlz KK RC NOver Hk HS0)).
intros c' (ms1 & -> & HS1 & HF1).
destruct (SA_shape_arr KK RC NOver Hk eq_refl) as (Hpc1 & Hrv1 & Hv1 & Hm1).
apply (to_malloc _ ms1 HS1 Hpc1 Hrv1 Hv1); [rewrite Hm1; apply in_stk1_mem_at | exact (raw_entry _ HF1)].
- cbn [mreal_cf]. eapply SR_cfv_bind; [exact (SA_run E _ md Hh Hlz KK RC (NSmall true) Hk HS0)|].
intros c' (ms1 & -> & HS1 & HF1). exact (IPX ms1 (or_introl eq_refl) HS1 (raw_entry _ HF1)).
- apply (mreal_cf_SR_pre src0segs _ _ _ _ (SA_run E _ md Hh Hlz KK RC (NSmall false) Hk HS0)).
intros c' (ms1 & -> & HS1 & HF1).
destruct (SA_shape_arr KK RC (NSmall false) Hk eq_refl) as (Hpc1 & Hrv1 & Hv1 & Hm1).
apply (to_malloc _ ms1 HS1 Hpc1 Hrv1 Hv1); [rewrite Hm1; apply in_stk1_mem_at | exact (raw_entry _ HF1)].
- cbn [mreal_cf]. eapply SR_cfv_bind; [exact (SA_run E _ md Hh Hlz KK RC (NMid b1 true) Hk HS0)|].
intros c' (ms1 & -> & HS1 & HF1). pose proof (raw_entry _ HF1) as RAW1.
pose proof (mid_st_okS L A regs mem md g am idx fr n a ka rg HC b1 true ms1 Hok HS1 RAW1) as HSM.
eapply SR_cfv_bind; [exact (SB_run E ms1 md Hh Hlz KK RC b1 true Hk HSM)|].
intros c2 (ms2 & -> & HS2 & HF2).
exact (IPX ms2 (or_intror (ex_intro _ b1 eq_refl)) HS2 (raw_frame _ _ _ (wr_mid_mem KK RC b1 true Hk) RAW1 HF2)).
- apply (mreal_cf_SR_pre src0segs _ _ _ _ (SA_run E _ md Hh Hlz KK RC (NMid b1 false) Hk HS0)).
intros c' (ms1 & -> & HS1 & HF1). pose proof (raw_entry _ HF1) as RAW1.
pose proof (mid_st_okS L A regs mem md g am idx fr n a ka rg HC b1 false ms1 Hok HS1 RAW1) as HSM.
apply (mreal_cf_SR_pre src0segs _ _ _ _ (SB_run E ms1 md Hh Hlz KK RC b1 false Hk HSM)).
intros c2 (ms2 & -> & HS2 & HF2).
destruct (SB_shape_arr KK RC b1 Hk) as (Hpc2 & Hrv2 & Hv2 & Hm2).
apply (to_malloc _ ms2 HS2 Hpc2 Hrv2 Hv2); [rewrite Hm2; apply in_stk1_mem_at |].
exact (raw_frame _ _ _ (wr_mid_mem KK RC b1 false Hk) RAW1 HF2).
Qed.
End b.
Theorem realloc_small : OBL_fb_gen ->
forall pc L A regs mem md p nold n g am idx fr,
ms_realloc src0_msyms = Some pc ->
call_pre_k src0_msyms (MRx src0_msyms) REALLOC_STACK L A regs mem md ->
In (p, nold) (user_blocks A) ->
getr regs 10 = Z_to_bv 64 (ptr_addr L p) -> getr regs 11 = Z_to_bv 64 n ->
0 <= n < 2 ^ 62 ->
usedX [] A g am -> 0 <= idx <= am_last am -> ss_fr (nth_slot am idx) = Some fr -> fr_kind fr = FUser ->
fr_n fr = nold -> p = frame_ptr am idx fr -> am_sc am < 48 ->
mreal_cf (ms_segs src0_msyms) (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom (ms_segs src0_msyms))) md)
(realloc (Some p) n A)
(realloc_leaf src0_msyms (MRx src0_msyms) L A regs mem md p nold n).
Proof.
intros FB pc L A regs mem md p nold n g am idx fr Hpc PRE Hin H10 H11 Hn Hu Hidx Hfr Hk Hnold Hp Hsc.
cbn [ms_realloc src0_msyms] in Hpc. injection Hpc as <-. subst p nold.
pose proof (MRx_MRc _ _ _ _ _ (proj1 PRE)) as MR. pose proof (mc_wf _ _ _ _ _ MR) as HWA.
pose proof (proj1 (usedX_MT _ _ _ _ Hu)) as Mg.
destruct (meta_in_area A g (MUsed am) HWA (In_of_mlookup _ _ _ Mg)) as (a & ka & Hain & Hka & Eg).
destruct (used_group_region [] None U0 A g am HWA Hu) as (rg & Hrg & Hkd & Hl & Ho & Hext & _).
assert (HC : small_ctx L A regs mem md g am idx fr n a ka rg) by (split; auto).
change (ms_segs src0_msyms) with src0segs.
exact (small_main FB L A regs mem md g am idx fr n a ka rg HC).
Qed.
End a.
