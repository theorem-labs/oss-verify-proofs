(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the read-loop lemmas of fuzz_preset's asan driver over preset's second allocator
   instance ARcf (lib/Reusable/YG0ncf.v), ported from proofs/cgif/cgif_file_fuzzer/lib/A/AD24.v and AD25.v (relocated
   here as lib/A/AD24.v, AD25.v): every donor lemma that mentions AR, with `AR tfibsegs B ly S W mem md` ->
   `ARcf tfibsegs B ly S [] W mem md` (ghost head set Hp = []), cgif's AR_laws -> a Theorem Labs lane's AR_laws_cf, proved
   (AR_laws_ok_cf, lib/Reusable/YG0lawscf.v, a Let, so no lemma takes it), its fields by name (al_* -> alc_*, Hp after
   S), cgif's read_check_tfa / memcpy_site_tfa -> lane CwPreA's read_check_tfa_cf / memcpy_site_tfa_cf
   (lib/A/PresetD1preA.v), cgif's AR_after_run / AR_model_same / AR_with_fds / AR_same_but_materialized /
   range_addressable_of_block' / shadow_hull_vis_of_block' -> lane CwLoopB's _cf lemmas (lib/A/PresetD1rAx.v).
   Names: the donor's + `_cf`; each lemma carries its donor file:line. The AR-free lemmas of AD24.v / AD25.v (eagree,
   winP, U_want, rd_to_RW, srr_read_win, region_ok_errno, regs_kept_CHK, ...) are cited from there, not copied.
   MEMNORM (lane MnPrefix, a Theorem Labs lane, 2026-10-29): rd_step_pos_cf, rd_step_eof_cf, rd_chk_cf and rd_cpy_cf take
   `YAkMemnorm.memnorm tfibsegs (ms_mem ms)` of the full overlay as their last premise and give memnorm of the end
   memory, so the read loop (lib/A/PresetD2runARd0mnPf.v) keeps it as an invariant: the runs go through YA0oInv's
   srr_run_with_inv / srr_run_to_with_inv at P := memnorm (laws YSRrMemnorm.srr_inv_laws_memnorm_k), the read node's
   write by YAkMemnormWb.memnorm_read_win, the close node and the hand steps keep the memory, and the read check /
   memcpy sites by the memnorm keep that ends their posts (lib/A/PresetD1preA.v).
   Nothing in this file is a proof of a function (rule 24: the driver layer of a port). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0d YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK00 YK0h YK14 YK1b YK15 YK18 YK0p YP0n YK0s YM02 YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0g YN3q YN3v YI04 YL0a YL0b YL09 YK04 YA0i YA0n YA0o YA0p YA0m YK09 YA0e YG00 YG01 YG0f YG0v YG0n YG0d YCe5.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB12 AF0l AB1h AB13 AF0m AD2j AD2i AD1t AD1y AD20 AD1v AD26 AD24 AD21.
(* The donor AD25.v's AR-free facts (rs_in_img, rs_not_owned_static, eagree, winP, ...) are cited from it. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AD25.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YImgTop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PresetD1sitesA PresetD1preA PresetD1rAx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YC80x YAkMemnorm YAkMemnormWb YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0oInv.
Import ListNotations.
Open Scope Z_scope.
(* lia here needs the Euclidean division equations; set locally, after the last import (cw-lanes-brief 23:40Z). *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape} {ci : CfImg} {cp : CfParams}.
Section Rd.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Let ARL : AR_laws_cf tfibsegs B := AR_laws_ok_cf tfibsegs B.
(* AD24.v:22 *)
Lemma tfib_const_val_cf : forall ly S W mem md i a w v,
ARcf tfibsegs B ly S [] W mem md ->
nth_error Tfib_const_abs i = Some (ACell (ANum a) w (AV (ANum v))) ->
val_mem tfibsegs (mrestrict (w_H W) mem) a w v.
Proof.
intros ly S W mem md i a w v HAR Hi k Hk.
pose proof (amc_const _ _ _ _ _ (proj1 HAR)) as HC. rewrite (ts_const B HB) in HC.
assert (Hin : In (ACell (ANum a) w (AV (ANum v))) (Tfib_const ly)).
{ unfold Tfib_const. apply in_or_app. right. apply in_or_app. left. exact (nth_error_In _ _ Hi). }
pose proof (proj1 (Forall_forall _ _) HC _ Hin) as Hc. unfold cell_holds in Hc. cbn [c_at c_w c_val aeval] in Hc.
specialize (Hc k Hk). unfold aview in Hc.
destruct (mbyte tfibsegs (mrestrict (w_H W) mem) (a + Z.of_nat k)) as [b|] eqn:E; [|discriminate Hc]. cbn in Hc.
injection Hc as Hc. f_equal. apply bv_eq. rewrite Hc, Z_to_bv_unsigned. symmetry.
change (YO0f.le_byte v w k) with (YG0f.le_byte v w k). unfold YG0f.le_byte.
unfold bv_wrap. change (bv_modulus 8) with 256%Z. apply Z.mod_small. apply Z.mod_pos_bound. lia.
Qed.
(* AD24.v:38 *)
Lemma region_ok_const1_cf : forall E ly S W mem md,
ARcf tfibsegs B ly S [] W mem md -> region_ok tfibsegs E (mrestrict (w_H W) mem) R_inited.
Proof.
intros E ly S W mem md HAR.
(* PROVISIONAL: 0xabb98 (= 703384) is __asan::asan_inited, the core's AD20.v:47 R_inited / AF0m.v Tfib_const_abs
   entry 51; no generated name yet (re-pin list). *)
pose proof (tfib_const_val_cf ly S W mem md 51 0xabb98 1 1 HAR eq_refl) as V.
split; [cbn; lia|]. split; [cbn; lia|]. split; [cbn; intros; lia|].
constructor; [|constructor]. intros i Hi. cbn [c_off c_val R_inited base_val r_base] in *. cbn in Hi.
eexists. split; [reflexivity|].
specialize (V (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in V by lia. replace (0 + 703384 + i) with (703384 + i) by lia.
rewrite V. f_equal. apply bv_eq. unfold byte_of_word. cbn [sv_denot]. rewrite u64_lit by lia. assert (i = 0) as -> by lia. reflexivity.
Qed.
(* AD24.v:49 *)
Lemma region_ok_const2_cf : forall E ly S W mem md,
ARcf tfibsegs B ly S [] W mem md -> region_ok tfibsegs E (mrestrict (w_H W) mem) R_realrd.
Proof.
intros E ly S W mem md HAR.
(* PROVISIONAL: 0xa3d60 (= 671072) is __interception::real_read and 0xa09b8 musl's read, the core's AD20.v:48
   R_realrd / AF0m.v Tfib_const_abs entry 72; no generated names yet (re-pin list). *)
pose proof (tfib_const_val_cf ly S W mem md 72 0xa3d60 8 0xa09b8 HAR eq_refl) as V.
split; [cbn; lia|]. split; [cbn; lia|]. split; [cbn; intros; lia|].
constructor; [|constructor]. intros i Hi. cbn [c_off c_val R_realrd base_val r_base] in *. cbn in Hi.
eexists. split; [reflexivity|].
specialize (V (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in V by lia. replace (0 + 671072 + i) with (671072 + i) by lia.
rewrite V. f_equal. apply bv_eq. unfold byte_of_word. cbn [sv_denot]. rewrite u64_lit by lia.
rewrite (le_byte_small 0xa09b8 8 (Z.to_nat i)) by lia. rewrite Z2Nat.id by lia. reflexivity.
Qed.
(* AD25.v:65 *)
Lemma rs_not_owned_cf : forall ly S W mem md x, ARcf tfibsegs B ly S [] W mem md -> RS_LO <= x < RS_HI -> ~ aowned B ly S x.
Proof.
intros ly S W mem md x HAR Hx Ho.
apply (proj1 (alc_owned_image _ _ ARL ly S [] W mem md x HAR (rs_in_img x Hx))) in Ho.
rewrite (ts_owned B HB) in Ho. apply Exists_exists in Ho as (h & Hin & Hz).
pose proof (proj1 (forallb_forall _ _) rs_not_owned_static h Hin) as Hc. cbn beta in Hc.
unfold in_zr in Hz. apply orb_prop in Hc as [Hc|Hc]; apply Z.leb_le in Hc; lia.
Qed.
(* AD25.v:73 *)
Lemma AR_after_win_write_cf : forall ly S W mem md md' (a : Z) bs,
ARcf tfibsegs B ly S [] W mem md -> RS_LO <= a -> a + Z.of_nat (length bs) <= RS_HI ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
ARcf tfibsegs B ly S [] W (wbytes mem (Z_to_bv 64 a) bs) md'.
Proof.
intros ly S W mem md md' a bs HAR Hlo Hhi Hv Hl He.
assert (Hau : bv_unsigned (Z_to_bv 64 a) = a) by (unfold RS_LO, RS_HI in *; apply u64_lit; lia).
apply (alc_frame _ _ ARL ly S [] W mem md _ md' HAR); [| | exact Hv | exact Hl | exact He |].
3:{
intros x Hx _. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, RS_LO, RS_HI in *.
apply wbytes_above; unfold w64; rewrite Hau, u64_lit by lia; lia. }
- intros x Hx Ho. unfold aview, mbyte, mrestrict.
assert (Hout : x < a \/ a + Z.of_nat (length bs) <= x).
{ destruct (Z.lt_ge_cases x a); [left; lia|]. destruct (Z.le_gt_cases (a + Z.of_nat (length bs)) x); [right; lia|].
exfalso. exact (rs_not_owned_cf ly S W mem md x HAR ltac:(lia) Ho). }
destruct (w_H W (Z_to_bv 64 x)); [reflexivity|]. unfold RS_LO, RS_HI in *.
destruct Hout as [Hout|Hout].
+ rewrite wbytes_below; [reflexivity | rewrite Hau; lia | rewrite Hau, u64_lit by lia; lia].
+ rewrite wbytes_above; [reflexivity | rewrite Hau, u64_lit by lia; lia].
- intros x Hv0. unfold aview, mbyte, mrestrict in *. destruct (w_H W (Z_to_bv 64 x)); [exact Hv0|].
destruct (mem (Z_to_bv 64 x)) as [b0|] eqn:Em.
+ pose proof (wbytes_grows bs mem (Z_to_bv 64 a) (Z_to_bv 64 x) ltac:(rewrite Em; discriminate)) as G.
destruct (wbytes mem (Z_to_bv 64 a) bs (Z_to_bv 64 x)); [cbn; discriminate | exfalso; exact (G eq_refl)].
+ destruct (wbytes mem (Z_to_bv 64 a) bs (Z_to_bv 64 x)); [cbn; discriminate | exact Hv0].
Qed.
Section f.
Variables (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (a0 p : list byte).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv [a0; p].
Hypothesis Hve : valid_envp (in_envp inp).
#[local] Notation EL := (YP08.E0 sp [a0; p] (in_envp inp) xw xd).
#[local] Notation usp := (bv_unsigned sp).
Let HWXi : wx_segs_nowrap tfibsegs := Hwx_tfa.
(* AD25.v's AR-free Section f facts, at this section's variables (as AD23.v:121 cites them). *)
#[local] Notation eagree := (AD25.eagree sp inp xw xd a0 p).
#[local] Notation eagree_0 := (AD25.eagree_0 sp inp xw xd a0 p).
#[local] Notation eagree_6 := (AD25.eagree_6 sp inp xw xd a0 p Hsp Hva Hve).
#[local] Notation winP := (AD25.winP sp Hsp).

(* AD25.v:204 *)
Lemma add_rt_cf : forall E ss (W : world tfibsegs) ms ly S md,
eagree E -> st_ok tfibsegs E ss (restrict (w_H W) ms) -> ARcf tfibsegs B ly S [] W (ms_mem ms) md ->
forallb (fun r1 => forallb (ext_chk r1) RT_REGIONS) (ss_mem ss) = true ->
st_ok tfibsegs E (with_rt ss) (restrict (w_H W) ms).
Proof.
intros E ss W ms ly S md HE HS HAR Hext. pose proof Hsp as (Ulo & Uhi & U16). pose proof (eagree_0 E HE) as E0'.
unfold with_rt. apply (st_ok_app_regions E ss (restrict (w_H W) ms) RT_REGIONS HS rt_wf).
- cbn [ms_mem restrict]. constructor; [apply (region_ok_const1_cf E ly S W (ms_mem ms) md HAR)|].
constructor; [apply (region_ok_const2_cf E ly S W (ms_mem ms) md HAR)|]. constructor; [apply region_ok_errno | constructor].
- cbn. unfold extent_disjoint. cbn. repeat split; lia.
- intros r1 r2 Hr1 Hr2.
pose proof (proj1 (forallb_forall _ _) Hext r1 Hr1) as X. pose proof (proj1 (forallb_forall _ _) X r2 Hr2) as Y. unfold ext_chk in Y.
pose proof (proj1 (forallb_forall _ _) rt_abs r2 Hr2) as Z2. cbn beta in Z2.
unfold extent_disjoint. destruct (r_base r2); [discriminate Z2|]. apply andb_prop in Z2 as [Z2a Z2b]. apply Z.leb_le in Z2a. apply Z.leb_le in Z2b.
destruct (r_base r1) as [[|n]|]; try discriminate Y; cbn [base_val].
+ apply Z.leb_le in Y. rewrite E0'. unfold sp_window_lo in Ulo. right. lia.
+ apply orb_prop in Y as [Y|Y]; apply Z.leb_le in Y; lia.
Qed.
(* AD25.v:303 *)
Lemma ARmd_sbm_cf : forall ly S W memx md0 md2 fds,
same_but_materialized (with_fds fds md0) md2 -> ARcf tfibsegs B ly S [] W memx md0 -> ARcf tfibsegs B ly S [] W memx md2.
Proof.
intros ly S W memx md0 md2 fds Hs HA.
apply (AR_same_but_materialized_cf B ly S [] W memx (with_fds fds md0) md2); [| exact Hs]. apply AR_with_fds_cf. exact HA.
Qed.
(* AD25.v:309 *)
Lemma rd_step_pos_cf : forall E (W : world tfibsegs) ms md ly S (pth : list byte) data (len cap want : Z),
eagree E -> st_ok tfibsegs E S_RW (restrict (w_H W) ms) ->
bv_unsigned (ew E A_LEN) = len -> bv_unsigned (ew E A_CAP) = cap -> bv_unsigned (ew E A_WANT) = want ->
ARcf tfibsegs B ly S [] W (ms_mem ms) md -> top_ok usp ly ->
0 <= len -> 1 <= want <= 65536 -> len + want <= cap -> cap <= 2 ^ 26 ->
m_fds md = APSG.fds3 (FdFile pth (Z_to_bv 64 len)) -> fs_lookup (m_fs md) pth = Some data -> len < Z.of_nat (length data) ->
YAkMemnorm.memnorm tfibsegs (ms_mem ms) ->
let bs := file_read data (Z_to_bv 64 len) (Z_to_bv 64 want) in
let n := Z.of_nat (length bs) in
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => (exists mem0 md1,
let mem1 := wbytes mem0 (Z_to_bv 64 RS_LO) bs in
1 <= n <= want
/\ AI tfibsegs (w_H W) (w_A W) md1 /\ ARcf tfibsegs B ly S [] W mem1 md1
/\ m_fds md1 = APSG.fds3 (FdFile pth (Z_to_bv 64 (len + n))) /\ m_fs md1 = m_fs md
/\ (forall i, 0 <= i < n -> mem1 (Z_to_bv 64 (RS_LO + i)) = nth_error bs (Z.to_nat i))
/\ (forall x : word, bv_unsigned x < RS_LO \/ RS_LO + n <= bv_unsigned x -> mem1 x = mem0 x)
/\ frame_of E LH_mem (ms_mem ms) mem0
/\ frame_of E LH_mem (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem0)
/\ at_CHK E W n mem1 md1 W' c')
/\ exists ms' md', c' = mkCfg ms' md' /\ YAkMemnorm.memnorm tfibsegs (ms_mem ms')).
Proof.
intros E W ms md ly S pth data len cap want HE HS E58 E59 E77 HAR HTOP Hlen0 Hwant Hlw Hcap Hfds Hfs Hdl HMN bs n.
pose proof (YSRrMemnorm.srr_inv_laws_memnorm_k tfibsegs) as PLAW.
pose proof HWXi as HWX. pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp.
pose proof (u64_range (ew E A_LEN)) as R58. rewrite E58 in R58.
pose proof (eagree_0 E HE) as E0'. pose proof (top_ok_ceil _ _ HTOP) as HCT.
pose proof S_RE_shape as (_ & RErv & REat & _). pose proof skel_iter as (SK1 & SK2 & _).
pose proof (proj1 win_ok_iter) as WOK. pose proof (proj1 (proj2 win_ok_iter)) as WOKre.
assert (Hn : 1 <= n <= want).
{ subst n bs. rewrite file_read_length. rewrite !u64_lit by lia. lia. }
srr_run_with_inv tfibtbl_lp_ok PLAW HS HMN.
lazymatch type of HS with st_ok_ecall _ _ _ (restrict _ ?msx) => rename HS into HSE; set (ms1 := msx) in * end.
rename HF into HF1. rename HFr into HFr1.
pose proof (st_ok_ecall_shape_r tfibsegs (w_H W) E S_RE ms1 HSE eq_refl) as (rg & mm & Em & _ & HMM & _).
assert (Emm : ms_mem ms1 = mm) by (rewrite Em; reflexivity).
assert (Hwin1 : forall a, usp - 65536 <= a < usp -> apresent (w_H W) (ms_mem ms1) a).
{ apply (winP E S_RE ms1 W (or_intror HSE) E0'). do 3 eexists; reflexivity. }
assert (HAR1 : ARcf tfibsegs B ly S [] W (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat md)).
{ apply (AR_after_run_cf B HB ARL ly S [] W E LH_mem (ms_mem ms) (ms_mem ms1) md mat HAR WOK); [rewrite E0'; exact Ulo | rewrite E0'; exact HCT | exact HF1 |].
rewrite E0'. intros a Ha. exact (apresent_some' _ _ _ (Hwin1 a Ha)). }
eapply SRr_bind.
{ apply (srr_read_win E S_RE ms1 W _ (Z_to_bv 64 3) pth (Z_to_bv 64 len) data bs RS_LO want HSE RErv).
- reflexivity.
- reflexivity.
- reflexivity.
- rewrite wvb_fds', Hfds. reflexivity.
- rewrite wvb_fs'. exact Hfs.
- reflexivity.
- eval_sr_get. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E77.
- lia.
- subst bs. eval_sr_get. cbn [sv_denot]. rewrite Z.add_0_r, <- E77, !Z_to_bv_bv_unsigned. reflexivity.
- exact (proj1 rs_win_check).
- exact (proj2 rs_win_check).
- unfold RS_LO. lia.
- unfold RS_LO. lia. }
intros W1 c1 Hwle (-> & regs & md2 & Ems1 & -> & Hregs & HG & Hmem & HAI2 & Hs & Hvm & Heu & Hbytes' & Hfr' & Hlen').
(* the read node's write keeps memnorm (the window at RS_LO is in writable segments) *)
assert (HMN2 : YAkMemnorm.memnorm tfibsegs (wbytes (ms_mem ms1) (Z_to_bv 64 RS_LO) bs)).
{ apply (YAkMemnormWb.memnorm_read_win tfibsegs (ms_mem ms1) RS_LO bs HMN (proj2 rs_win_check)); unfold RS_LO; lia. }
assert (Hnw : len_word bs = Z_to_bv 64 n) by (unfold len_word; subst n; reflexivity).
pose proof (st_ok_resume_atom tfibsegs A_N fact_n E S_RE regs _ (len_word bs) Hregs Hmem HG REat
ltac:(rewrite Hnw; cbn; rewrite u64_lit by lia; lia) ltac:(cbn; lia) ltac:(cbn; rewrite Z.mod_1_r; reflexivity)) as HS2.
rewrite Hnw in HS2 |- *. rewrite <- restrict_mkst_fx in HS2.
pose proof (same_but_materialized_frame _ _ Hs) as (_ & _ & Hlz & _ & _ & _ & _ & _ & Hfds2 & _ & _ & Hfs2 & _ & _ & _ & _ & _).
assert (HAR2 : ARcf tfibsegs B ly S [] W (wbytes (ms_mem ms1) (Z_to_bv 64 RS_LO) bs) md2).
{ apply (AR_after_win_write_cf ly S W (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat md) md2 RS_LO bs HAR1 ltac:(lia)
ltac:(unfold RS_LO, RS_HI; lia)).
- rewrite Hvm. destruct md; reflexivity.
- rewrite Hlz. destruct md; reflexivity.
- rewrite Heu. unfold eager_used. destruct md; reflexivity. }
assert (Hoff : (Z_to_bv 64 len + Z_to_bv 64 n)%bv = Z_to_bv 64 (len + n)).
{ apply bv_eq. rewrite bv_add_unsigned, !u64_lit by lia. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite !Z.mod_small by lia. reflexivity. }
srr_run_to_with_inv tfibtbl_lp_ok PLAW HS2 HMN2 A_CHK.
apply SRr_ret. split; [| do 2 eexists; split; [reflexivity | exact HMN2]].
exists (ms_mem ms1), md2. cbv zeta.
split; [exact Hn|]. split; [exact HAI2|]. split; [exact HAR2|].
split. { rewrite Hfds2, with_fds_fds, wvb_fds', Hfds, Hnw, Hoff. unfold fd_insert, APSG.fds3. f_equal. }
split. { rewrite Hfs2, with_fds_fs, wvb_fs'. reflexivity. }
split; [exact Hbytes'|]. split; [intros x Hx; apply Hfr'; lia|].
split; [exact HF1|]. split; [exact HFr1|].
split; [reflexivity|]. eexists. eexists. split; [reflexivity|]. split; [exact HS2|]. split; [exact HF | exact HFr].
Qed.
(* AD25.v:386 *)
Lemma rd_step_eof_cf : forall E (W : world tfibsegs) ms md ly S (pth : list byte) data (len cap want : Z),
eagree E -> st_ok tfibsegs E S_RW (restrict (w_H W) ms) ->
bv_unsigned (ew E A_LEN) = len -> bv_unsigned (ew E A_CAP) = cap -> bv_unsigned (ew E A_WANT) = want ->
ARcf tfibsegs B ly S [] W (ms_mem ms) md -> top_ok usp ly ->
0 <= len -> 1 <= want <= 65536 ->
m_fds md = APSG.fds3 (FdFile pth (Z_to_bv 64 len)) -> fs_lookup (m_fs md) pth = Some data -> len = Z.of_nat (length data) ->
YAkMemnorm.memnorm tfibsegs (ms_mem ms) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms' md',
c' = mkCfg ms' md' /\ st_ok tfibsegs E S_HDR (restrict (w_H W) ms')
/\ AI tfibsegs (w_H W) (w_A W) md' /\ ARcf tfibsegs B ly S [] W (ms_mem ms') md'
/\ m_fds md' = APSG.fds_std /\ m_fs md' = m_fs md
/\ frame_of E LH_mem (ms_mem ms) (ms_mem ms')
/\ frame_of E LH_mem (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms'))
/\ YAkMemnorm.memnorm tfibsegs (ms_mem ms')).
Proof.
intros E W ms md ly S pth data len cap want HE HS E58 E59 E77 HAR HTOP Hlen0 Hwant Hfds Hfs Hdl HMN.
pose proof (YSRrMemnorm.srr_inv_laws_memnorm_k tfibsegs) as PLAW.
pose proof HWXi as HWX. pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp.
pose proof (u64_range (ew E A_LEN)) as R58. rewrite E58 in R58.
pose proof (eagree_0 E HE) as E0'. pose proof (top_ok_ceil _ _ HTOP) as HCT.
pose proof S_RE_shape as (_ & RErv & REat & _). pose proof skel_iter as (SK1 & SK2 & SK3 & SK4 & SK5 & SK6 & _).
pose proof win_ok_iter as (WOK & WOKre & _ & _ & WOKcl).
set (bs := file_read data (Z_to_bv 64 len) (Z_to_bv 64 want)).
assert (Hbs0 : bs = []) by (subst bs; apply file_read_eof; rewrite u64_lit by lia; lia).
srr_run_with_inv tfibtbl_lp_ok PLAW HS HMN.
lazymatch type of HS with st_ok_ecall _ _ _ (restrict _ ?msx) => rename HS into HSE; set (ms1 := msx) in * end.
rename HF into HF1. rename HFr into HFr1.
assert (HAR1 : ARcf tfibsegs B ly S [] W (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat md)).
{ apply (AR_after_run_cf B HB ARL ly S [] W E LH_mem (ms_mem ms) (ms_mem ms1) md mat HAR WOK); [rewrite E0'; exact Ulo | rewrite E0'; exact HCT | exact HF1 |].
rewrite E0'. intros a Ha. apply (apresent_some' (w_H W)). apply (winP E S_RE ms1 W (or_intror HSE) E0'); [| exact Ha]. do 3 eexists; reflexivity. }
eapply SRr_bind.
{ apply (srr_read_win E S_RE ms1 W _ (Z_to_bv 64 3) pth (Z_to_bv 64 len) data bs RS_LO want HSE RErv).
- reflexivity.
- reflexivity.
- reflexivity.
- rewrite wvb_fds', Hfds. reflexivity.
- rewrite wvb_fs'. exact Hfs.
- reflexivity.
- eval_sr_get. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E77.
- lia.
- subst bs. eval_sr_get. cbn [sv_denot]. rewrite Z.add_0_r, <- E77, !Z_to_bv_bv_unsigned. reflexivity.
- exact (proj1 rs_win_check).
- exact (proj2 rs_win_check).
- unfold RS_LO. lia.
- unfold RS_LO. lia. }
intros W1 c1 Hwle (-> & regs & md2 & Ems1 & -> & Hregs & HG & Hmem & HAI2 & Hs & Hvm & Heu & _ & _ & _).
rewrite Hbs0 in *. cbn [wbytes len_word length Z.of_nat] in *.
pose proof (same_but_materialized_frame _ _ Hs) as (_ & _ & Hlz & _ & _ & _ & _ & _ & Hfds2 & _ & _ & Hfs2 & _ & _ & _ & _ & _).
assert (ARmd2 : forall memx, ARcf tfibsegs B ly S [] W memx (with_vm_backing (m_vm_lazy md) mat md) -> ARcf tfibsegs B ly S [] W memx md2).
{ intros memx HA. apply (AR_model_same_cf B ly S [] W memx (with_vm_backing (m_vm_lazy md) mat md) md2 HA).
- rewrite Hvm. destruct md; reflexivity.
- rewrite Hlz. destruct md; reflexivity.
- rewrite Heu. unfold eager_used. destruct md; reflexivity. }
pose proof (st_ok_resume_sv tfibsegs E S_RE regs (mrestrict (w_H W) (ms_mem ms1)) (SLit 0) (Z_to_bv 64 0) Hregs Hmem HG eq_refl) as HS2.
rewrite <- restrict_mkst_fx in HS2. change (Z_to_bv 64 (Z.of_nat 0)) with (Z_to_bv 64 0).
(* the eof read writes no byte (bs = []), so the memory is ms1's *)
srr_run_with_inv tfibtbl_lp_ok PLAW HS2 HMN.
lazymatch type of HS2 with st_ok_ecall _ _ _ (restrict _ ?msx) => rename HS2 into HSC; set (msB := msx) in * end.
rename HF into HF2. rename HFr into HFr2.
pose proof (st_ok_ecall_shape_r tfibsegs (w_H W) E _ msB HSC eq_refl) as (regs2 & mem2 & Em2 & Hregs2 & Hmem2 & HG2).
(* the close node keeps the memory *)
assert (HMNB : YAkMemnorm.memnorm tfibsegs mem2) by (rewrite Em2 in HMN; exact HMN).
assert (HAR3 : ARcf tfibsegs B ly S [] W (ms_mem msB) (with_vm_backing (m_vm_lazy md2) mat0 md2)).
{ apply (AR_after_run_cf B HB ARL ly S [] W E (ss_mem S_RE) (ms_mem ms1) (ms_mem msB) md2 mat0 (ARmd2 _ HAR1) WOKre);
[rewrite E0'; exact Ulo | rewrite E0'; exact HCT | exact HF2 |].
rewrite E0'. intros a Ha. apply (apresent_some' (w_H W)). apply (winP E _ msB W (or_intror HSC) E0'); [| exact Ha]. do 3 eexists; reflexivity. }
apply SRr_use_AI. intros HAI3. cbn [cfg_model] in HAI3. rewrite Em2.
destruct (node_close_lazy tfibsegs (w_H W) (w_A W) regs2 (Z_to_bv 64 (ss_pc S_CL)) mem2 (seg_rom tfibsegs) (with_vm_backing (m_vm_lazy md2) mat0 md2)
(Z_to_bv 64 3) (FdFile pth (Z_to_bv 64 len + Z_to_bv 64 0)%bv) HAI3) as [Hn3 HAI4].
{ rewrite (Hregs2 17%bv). reflexivity. }
{ rewrite (Hregs2 10%bv). reflexivity. }
{ reflexivity. }
{ rewrite wvb_fds', Hfds2, with_fds_fds, wvb_fds', Hfds. unfold fd_insert, APSG.fds3. cbn -[Z_to_bv bv_add]. reflexivity. }
apply (SRr_node tfibsegs W _ unit _ tt _ Hn3); [intros [] _; exact HAI4|]. intros [].
pose proof (st_ok_resume_sv tfibsegs E S_CL regs2 (mrestrict (w_H W) mem2) (SLit 0) (Z_to_bv 64 0) Hregs2 Hmem2 HG2 eq_refl) as HS4.
rewrite <- restrict_mkst_fx in HS4.
srr_run_with_inv tfibtbl_lp_ok PLAW HS4 HMNB.
apply SRr_use_AI. intros HAI5. cbn [cfg_model] in HAI5.
apply SRr_ret. split; [reflexivity|]. eexists. eexists. split; [reflexivity|]. split; [exact HS4|].
assert (Emem2 : ms_mem msB = mem2) by (rewrite Em2; reflexivity).
split; [exact HAI5|].
split.
{ apply (AR_after_run_cf B HB ARL ly S [] W E (ss_mem S_CL) mem2 _ _ _ (AR_with_fds_cf B ly S [] W mem2 _ _ ltac:(rewrite <- Emem2; exact HAR3)) WOKcl);
[rewrite E0'; exact Ulo | rewrite E0'; exact HCT | exact HF |].
rewrite E0'. intros a Ha. apply (apresent_some' (w_H W)). apply (winP E S_HDR _ W (or_introl HS4) E0'); [| exact Ha]. do 3 eexists; reflexivity. }
split. { rewrite wvb_fds', with_fds_fds, wvb_fds', Hfds2, with_fds_fds, wvb_fds', Hfds. unfold fd_remove, fd_insert, APSG.fds3, APSG.fds_std. cbn -[Z_to_bv bv_add]. reflexivity. }
split. { rewrite wvb_fs', with_fds_fs, wvb_fs', Hfs2, with_fds_fs, wvb_fs'. reflexivity. }
split; [| split; [| exact HMNB]].
- apply (frame_of_trans E LH_mem (ss_mem S_RE) _ _ _ (eq_sym SK1) HF1).
apply (frame_of_trans E (ss_mem S_RE) (ss_mem S_CL) _ _ _ ltac:(rewrite SK1, SK5; reflexivity) HF2). rewrite Emem2. exact HF.
- apply (frame_of_trans E LH_mem (ss_mem S_RE) _ _ _ (eq_sym SK1) HFr1).
apply (frame_of_trans E (ss_mem S_RE) (ss_mem S_CL) _ _ _ ltac:(rewrite SK1, SK5; reflexivity) HFr2). rewrite Emem2. exact HFr.
Qed.
(* AD25.v:475 *)
Lemma rd_dir_cf : forall E (W : world tfibsegs) ms md ly S (want : Z),
eagree E -> st_ok tfibsegs E S_RW (restrict (w_H W) ms) ->
bv_unsigned (ew E A_WANT) = want -> 1 <= want <= 65536 ->
ARcf tfibsegs B ly S [] W (ms_mem ms) md -> top_ok usp ly ->
m_fds md = APSG.fds3 FdDir ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms' md',
c' = mkCfg ms' md' /\ st_ok tfibsegs E S_DIR (restrict (w_H W) ms')
/\ AI tfibsegs (w_H W) (w_A W) md' /\ ARcf tfibsegs B ly S [] W (ms_mem ms') md'
/\ m_fds md' = m_fds md /\ m_fs md' = m_fs md
/\ frame_of E LH_mem (ms_mem ms) (ms_mem ms')
/\ frame_of E LH_mem (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms'))).
Proof.
intros E W ms md ly S want HE HS E77 Hwant HAR HTOP Hfds.
pose proof HWXi as HWX. pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp.
pose proof (eagree_0 E HE) as E0'. pose proof (top_ok_ceil _ _ HTOP) as HCT.
pose proof S_RE_shape as (_ & RErv & REat & _). pose proof skel_iter as (SK1 & _).
pose proof win_ok_iter as (WOK & WOKre & _). pose proof S_DIR_facts as (_ & _ & _ & _ & _ & _ & _ & SKd).
srr_run_with tfibtbl_lp_ok HS.
lazymatch type of HS with st_ok_ecall _ _ _ (restrict _ ?msx) => rename HS into HSE; set (ms1 := msx) in * end.
rename HF into HF1. rename HFr into HFr1.
assert (HAR1 : ARcf tfibsegs B ly S [] W (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat md)).
{ apply (AR_after_run_cf B HB ARL ly S [] W E LH_mem (ms_mem ms) (ms_mem ms1) md mat HAR WOK); [rewrite E0'; exact Ulo | rewrite E0'; exact HCT | exact HF1 |].
rewrite E0'. intros a Ha. apply (apresent_some' (w_H W)). apply (winP E S_RE ms1 W (or_intror HSE) E0'); [| exact Ha]. do 3 eexists; reflexivity. }
pose proof (st_ok_ecall_shape_r tfibsegs (w_H W) E _ ms1 HSE eq_refl) as (regs & mem & Em & Hregs & Hmem & HG).
apply SRr_use_AI. intros HAI1. cbn [cfg_model] in HAI1. rewrite Em.
destruct (node_read_dir_lazy tfibsegs (w_H W) (w_A W) regs (Z_to_bv 64 (ss_pc S_RE)) mem (seg_rom tfibsegs) (with_vm_backing (m_vm_lazy md) mat md)
(Z_to_bv 64 3) HAI1) as [Hn HAI2].
{ rewrite (Hregs 17%bv). reflexivity. }
{ rewrite (Hregs 10%bv). reflexivity. }
{ reflexivity. }
{ rewrite wvb_fds', Hfds. reflexivity. }
{ pose proof E77 as E77'. unfold A_WANT in E77'.
rewrite (Hregs 11%bv), (Hregs 12%bv). eval_sr_get. cbn [sv_denot]. rewrite !Z.add_0_r, E77'.
unfold access_okb, TASK_SIZE, RS_LO. rewrite !u64_lit by lia. apply andb_true_intro; split; apply Z.leb_le; lia. }
apply (SRr_node tfibsegs W _ unit _ tt _ Hn); [intros [] _; exact HAI2|]. intros [].
pose proof (st_ok_resume_sv tfibsegs E S_RE regs (mrestrict (w_H W) mem) (SLit (2 ^ 64 - 21)) (errno_ret EISDIR) Hregs Hmem HG
ltac:(rewrite errno_EISDIR; reflexivity)) as HS2.
rewrite <- restrict_mkst_fx in HS2.
assert (Emm : mem = ms_mem ms1) by (rewrite Em; reflexivity).
srr_run_with tfibtbl_lp_ok HS2.
apply SRr_use_AI. intros HAI3. cbn [cfg_model] in HAI3.
apply SRr_ret. split; [reflexivity|]. eexists. eexists. split; [reflexivity|]. split; [exact HS2|].
split; [exact HAI3|].
split.
{ apply (AR_after_run_cf B HB ARL ly S [] W E (ss_mem S_RE) mem _ _ _ ltac:(rewrite Emm; exact HAR1) WOKre); [rewrite E0'; exact Ulo | rewrite E0'; exact HCT | exact HF |].
rewrite E0'. intros a Ha. apply (apresent_some' (w_H W)). apply (winP E S_DIR _ W (or_introl HS2) E0'); [| exact Ha]. do 3 eexists; reflexivity. }
split; [rewrite ?wvb_fds'; reflexivity|]. split; [rewrite ?wvb_fs'; reflexivity|].
split.
- apply (frame_of_trans E LH_mem (ss_mem S_RE) _ _ _ (eq_sym SK1) HF1). rewrite <- Emm. exact HF.
- apply (frame_of_trans E LH_mem (ss_mem S_RE) _ _ _ (eq_sym SK1) HFr1). rewrite <- Emm. exact HFr.
Qed.
(* The bss zero-shadow entry of the REGENERATED table (lib/A/AF0m.v Tfib_zero_shadow) that covers the read state
   [RS_LO, RS_HI): found in the table by computation and cited through it, so no address literal here (the donor's
   pair (0xa7200, 0x600000 - 0xa7200), AD25.v:527, is cgif's). *)
Definition rs_zsh : Z * Z :=
match find (fun z => ((fst z <=? RS_LO) && (RS_HI <=? fst z + snd z))%bool) Tfib_zero_shadow with
| Some z => z
| None => (0, 0)
end.
Lemma rs_zsh_facts : In rs_zsh Tfib_zero_shadow /\ fst rs_zsh mod 8 = 0 /\ snd rs_zsh mod 8 = 0 /\
fst rs_zsh <= RS_LO /\ RS_HI <= fst rs_zsh + snd rs_zsh /\
shadow_of_addr SHADOW_OFF (fst rs_zsh) <= shadow_addr RS_LO / 8 * 8 /\
shadow_addr (RS_HI - 1) / 8 * 8 + 8 <= shadow_of_addr SHADOW_OFF (fst rs_zsh) + snd rs_zsh / 8.
Proof.
split.
{ unfold rs_zsh. destruct (find _ Tfib_zero_shadow) as [z|] eqn:E; [exact (proj1 (find_some _ _ E)) |].
vm_compute in E. discriminate E. }
split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
split; [apply Z.leb_le; vm_compute; reflexivity|]. split; [apply Z.leb_le; vm_compute; reflexivity|].
split; apply Z.leb_le; vm_compute; reflexivity.
Qed.
(* AD25.v:527 *)
Lemma rs_zero_shadow_cf : forall ly S W mem md, ARcf tfibsegs B ly S [] W mem md ->
zero_shadow (aview tfibsegs (w_H W) mem) SHADOW_OFF (fst rs_zsh) (snd rs_zsh).
Proof.
intros ly S W mem md HAR.
apply (alc_zshadow _ _ ARL ly S [] W mem md rs_zsh HAR).
unfold zero_shadow_ranges. right. rewrite (ts_zsh B HB). exact (proj1 rs_zsh_facts).
Qed.
(* AD25.v:534 *)
Lemma rs_range_addressable_cf : forall ly S W mem md n, ARcf tfibsegs B ly S [] W mem md -> 0 <= n -> RS_LO + n <= RS_HI ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF RS_LO n.
Proof.
intros ly S W mem md n HAR Hn Hle x Hx. pose proof rs_zsh_facts as (_ & A1 & A2 & L1 & L2 & _).
apply (zero_shadow_range _ SHADOW_OFF (fst rs_zsh) (snd rs_zsh) A1 A2 (rs_zero_shadow_cf ly S W mem md HAR) x).
lia.
Qed.
(* AD25.v:541 *)
Lemma rs_shadow_hull_vis_cf : forall ly S W mem md n, ARcf tfibsegs B ly S [] W mem md -> 0 < n -> RS_LO + n <= RS_HI ->
shadow_hull_vis (aview tfibsegs (w_H W) mem) RS_LO n.
Proof.
intros ly S W mem md n HAR Hn Hle s Hs. pose proof (rs_zero_shadow_cf ly S W mem md HAR) as Z0.
pose proof rs_zsh_facts as (_ & A1 & A2 & L1 & L2 & H1 & H2).
replace s with (shadow_of_addr SHADOW_OFF (fst rs_zsh) + (s - shadow_of_addr SHADOW_OFF (fst rs_zsh))) by lia.
rewrite Z0; [discriminate|].
assert (M : shadow_addr (RS_LO + n - 1) / 8 * 8 <= shadow_addr (RS_HI - 1) / 8 * 8).
{ unfold shadow_addr. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
lia.
Qed.
(* AD25.v:549 *)
Lemma rd_chk_cf : forall E (W : world tfibsegs) ms md ly S (n len cap : Z),
read_check_tfa_cf B ->
let E2 := ewset E A_N (Z_to_bv 64 n) in
eagree E -> st_ok tfibsegs E2 S_CHK (restrict (w_H W) ms) ->
ARcf tfibsegs B ly S [] W (ms_mem ms) md -> top_ok usp ly -> 1 <= n <= 65536 ->
YAkMemnorm.memnorm tfibsegs (ms_mem ms) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 A_CHK_END) mem' (seg_rom tfibsegs)) md'
/\ st_ok tfibsegs (havoc E2 K_CHK (map (getr regs') CLOB_CHK)) S_CHK' (restrict (w_H W) (mkst regs' (Z_to_bv 64 A_CHK_END) mem' (seg_rom tfibsegs)))
/\ ARcf tfibsegs B ly S [] W mem' md'
/\ same_but_materialized md md'
/\ (forall a, 0 <= a < 2 ^ 64 -> ~ (usp + ICPT_SP - ESTACK <= a < usp + ICPT_SP) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) (ms_mem ms) a)
/\ (forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) mem' a)
/\ YAkMemnorm.memnorm tfibsegs mem').
Proof.
intros E W ms md ly S n len cap RCHK E2 HE HS HAR HTOP Hn HMN.
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp.
assert (E2_0 : bv_unsigned (ew E2 0) = usp) by (subst E2; rewrite ew_ewset_other by (unfold A_N; lia); exact (eagree_0 E HE)).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E2 S_CHK ms HS eq_refl) as Hshape.
set (regs := ms_regs ms) in *. set (mem := ms_mem ms) in *.
(* PROVISIONAL: 0x44a8c = __interceptor_read+0x50, the read check's return address (the core's S_CHK state);
   no generated name yet (re-pin list). *)
assert (R1 : getr regs 1%bv = w64 0x44a8c) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E2 S_CHK ms 1%bv HS); reflexivity).
assert (R3 : getr regs 3%bv = w64 TFIB_GP) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E2 S_CHK ms 3%bv HS); reflexivity).
assert (R4 : getr regs 4%bv = w64 TFIB_TP) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E2 S_CHK ms 4%bv HS); reflexivity).
assert (R2 : getr regs 2%bv = Z_to_bv 64 (usp + ICPT_SP)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E2 S_CHK ms 2%bv HS). eval_sr_get. cbn [sv_denot]. rewrite E2_0. reflexivity. }
assert (R10 : getr regs 10%bv = w64 n).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E2 S_CHK ms 10%bv HS). eval_sr_get. cbn [sv_denot]. subst E2. unfold A_N. rewrite ew_ewset_same, u64_lit by lia. rewrite Z.add_0_r. reflexivity. }
assert (R9 : getr regs 9%bv = w64 RS_LO) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E2 S_CHK ms 9%bv HS); reflexivity).
assert (Hsp' : spZ regs = usp + ICPT_SP) by (unfold spZ; rewrite R2; unfold ICPT_SP; rewrite u64_lit by (unfold sp_window_lo in Ulo; lia); lia).
pose proof (st_ok_mem_ok tfibsegs E2 S_CHK _ HS) as HM. cbn [restrict ms_mem] in HM. fold mem in HM.
assert (Hwin : forall a, usp - 65536 <= a < usp - 128 -> apresent (w_H W) mem a).
{ intros a Ha. eapply (win_present sp Hsp E2 (w_H W) mem (ss_mem S_CHK)); [exact HM | left; reflexivity | exact E2_0 | lia | lia | cbn; lia]. }
rewrite Hshape. change (Z_to_bv 64 (ss_pc S_CHK)) with (w64 A_CHK). fold regs mem.
change (mkCfg (mkst regs (w64 A_CHK) mem (seg_rom tfibsegs)) md) with (cfg_at tfibsegs A_CHK regs mem md).
eapply SRr_mono.
{ apply (RCHK ly S W regs mem md n RS_LO).
- split; [exact HAR|]. split; [unfold top_ok in *; tauto|]. split; [rewrite R1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity|].
split; [rewrite Hsp'; unfold ICPT_SP; replace (usp + (-128 - 2128)) with (usp + (-141) * 16) by lia; rewrite Z.mod_add by lia; exact U16|].
split; [rewrite Hsp'; unfold ICPT_SP, sp_window_lo in *; lia|]. split; [rewrite Hsp'; unfold top_ok, ICPT_SP in *; lia|].
split; [rewrite Hsp'; intros a Ha; apply Hwin; unfold ESTACK, ICPT_SP in Ha; lia|].
split; [rewrite (ts_gp B HB); exact R3 | rewrite (ts_tp B HB); exact R4].
- exact R10.
- exact R9.
- lia.
- unfold RS_LO; lia.
- unfold RS_LO; lia.
- left. unfold RS_LO, kLowMemEnd. lia.
- apply (rs_range_addressable_cf ly S W mem md n HAR); [lia | unfold RS_LO, RS_HI; lia].
- apply (rs_shadow_hull_vis_cf ly S W mem md n HAR); [lia | unfold RS_LO, RS_HI; lia]. }
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & -> & HAR' & HP & Hs & Ha0 & Hfr & Hpres & HMNK).
split; [reflexivity|]. exists regs', mem', md'. split; [reflexivity|].
rewrite Hshape, restrict_mkst_fx in HS. fold regs mem in HS.
assert (HST : st_ok tfibsegs (havoc E2 K_CHK (map (getr regs') CLOB_CHK)) S_CHK'
(mkst regs' (Z_to_bv 64 A_CHK_END) (mrestrict (w_H W) mem') (seg_rom tfibsegs))).
{ unfold S_CHK'.
apply (st_ok_splice_havoc tfibsegs K_CHK E2 S_CHK regs regs' (w64 A_CHK) A_CHK_END (mrestrict (w_H W) mem) (mrestrict (w_H W) mem')
_ [(10%bv : bv 5, SOff A_N 0)] CLOB_CHK HS).
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- exact (regs_kept_CHK regs regs' HP).
- constructor; [| constructor]. cbn [fst snd]. split; [reflexivity|]. rewrite Ha0. cbn [sv_denot]. subst E2. unfold A_N. rewrite ew_ewset_same, u64_lit by lia. rewrite Z.add_0_r. reflexivity.
-
assert (SCR : forall a, 0 <= a < 2 ^ 64 -> ~ (usp + ICPT_SP - ESTACK <= a < usp + ICPT_SP) ->
mbyte tfibsegs (mrestrict (w_H W) mem') a = mbyte tfibsegs (mrestrict (w_H W) mem) a).
{ intros a HaR Ha. apply (mbyte_of_aview tfibsegs). apply Hfr; [exact HaR | rewrite Hsp'; exact Ha]. }
destruct HM as (Hwf & Hok & Hpd).
split; [vm_compute; reflexivity|]. split.
+ pose proof (Forall_inv Hok) as Hr0. pose proof (Forall_inv_tail Hok) as Hrs0.
change (ss_mem S_CHK') with (hd R_errno (ss_mem S_CHK') :: tl (ss_mem S_CHK')). constructor.
*
apply (region_ok_transport_chunks E2 (mrestrict (w_H W) mem) (mrestrict (w_H W) mem')).
-- eapply region_ok_sub; [| cbn; lia | exact Hr0]. repeat split; cbn; try lia. intros c Hc. cbn in Hc |- *. tauto.
-- intros c i Hc Hi. cbn [r_base base_val]. rewrite E2_0. cbn [r_chunks hd] in Hc. unfold sp_window_lo, sp_window_hi in Ulo, Uhi.
repeat (destruct Hc as [<-|Hc]; [cbn in Hi |- *; apply SCR; unfold ESTACK, ICPT_SP; lia|]). destruct Hc.
-- cbn [r_wlo r_whi r_base base_val]. rewrite E2_0. intros o Ho. apply (apresent_writable tfibsegs). apply Hpres. apply Hwin. lia.
*
change (tl (ss_mem S_CHK')) with (tl (ss_mem S_CHK)).
assert (HMt : mem_ok tfibsegs E2 (mrestrict (w_H W) mem) (tl (ss_mem S_CHK))).
{ split; [vm_compute; reflexivity|]. split; [exact Hrs0 | exact (proj2 Hpd)]. }
assert (TAIL : forallb (fun r => match r_base r with Some 0%nat => (-128 <=? r_lo r) | Some _ => false
| None => (0 <=? r_lo r) && (r_hi r <=? YImgTop.IMG_TOP) end)%bool (tl (ss_mem S_CHK)) = true) by (vm_compute; reflexivity).
assert (HK : Forall (region_kept tfibsegs E2 (mrestrict (w_H W) mem) (mrestrict (w_H W) mem')) (tl (ss_mem S_CHK))).
{ apply Forall_forall. intros r Hr.
pose proof (proj1 (forallb_forall _ _) TAIL r Hr) as Hc. cbn beta in Hc.
pose proof (proj1 (Forall_forall _ _) Hrs0 r Hr) as (B1 & B2 & _).
assert (OFF : forall a, base_val E2 (r_base r) + r_lo r <= a < base_val E2 (r_base r) + r_hi r -> ~ (usp + ICPT_SP - ESTACK <= a < usp + ICPT_SP)).
{ intros a Ha. destruct (r_base r) as [[|k]|]; try discriminate Hc; cbn [base_val] in Ha, B1, B2.
- apply Z.leb_le in Hc. rewrite E2_0 in Ha. unfold ESTACK, ICPT_SP. lia.
- apply andb_prop in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2. unfold ESTACK, ICPT_SP, sp_window_lo, YImgTop.IMG_TOP in *. lia. }
split; intros a Ha; [apply SCR; [lia | apply OFF; exact Ha]|].
intros Hw. exact (wview_grows tfibsegs _ _ _ (mem_grows_of_apresent (w_H W) mem mem' Hpres) Hw). }
exact (proj1 (proj2 (mem_ok_kept tfibsegs E2 _ (mrestrict (w_H W) mem') (tl (ss_mem S_CHK)) HMt ltac:(vm_compute; reflexivity) HK))).
+ apply (pairwise_disjoint_extents E2 (ss_mem S_CHK) (ss_mem S_CHK')); [vm_compute; reflexivity | exact Hpd]. }
rewrite <- restrict_mkst_fx in HST. split; [exact HST|]. split; [exact HAR'|]. split; [exact Hs|].
split; [intros a HaR Ha; apply Hfr; [exact HaR | rewrite Hsp'; exact Ha] | split; [exact Hpres | exact (HMNK HMN)]].
Qed.
(* AD25.v:704 *)
Lemma rd_cpy_cf : forall E3 (W : world tfibsegs) ms md ly S (pb : sptr) (n buf len cap : Z) (data bs : list byte),
memcpy_site_tfa_cf B ->
eagree E3 -> st_ok tfibsegs E3 S_CP (restrict (w_H W) ms) ->
bv_unsigned (ew E3 A_BUF) = buf -> bv_unsigned (ew E3 A_LEN) = len -> bv_unsigned (ew E3 A_N) = n ->
ARcf tfibsegs B ly S [] W (ms_mem ms) md -> top_ok usp ly ->
blocks S = [(pb, cap)] -> sptr_addr B ly pb = buf -> 0 <= len -> 1 <= n <= 65536 -> len + n <= cap -> cap <= 2 ^ 26 ->
blk (w_H W) (ms_mem ms) buf len data -> Z.of_nat (length bs) = n ->
(forall i, 0 <= i < n -> ms_mem ms (Z_to_bv 64 (RS_LO + i)) = nth_error bs (Z.to_nat i)) ->
(forall j, (j < length bs)%nat -> nth_error bs j = nth_error data (Z.to_nat len + j)%nat) ->
YAkMemnorm.memnorm tfibsegs (ms_mem ms) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists regs4 mem4 md4,
c' = mkCfg (mkst regs4 (Z_to_bv 64 RA_CP) mem4 (seg_rom tfibsegs)) md4
/\ st_ok tfibsegs (havoc E3 K_CP (map (getr regs4) CLOB)) S_CPp (restrict (w_H W) (mkst regs4 (Z_to_bv 64 RA_CP) mem4 (seg_rom tfibsegs)))
/\ ARcf tfibsegs B ly S [] W mem4 md4 /\ same_but_materialized md md4
/\ blk (w_H W) mem4 buf (len + n) data
/\ (forall a, 0 <= a < 2 ^ 64 -> ~ (buf + len <= a < buf + len + n) -> ~ (usp - 128 - ESTACK <= a < usp - 128) -> aview tfibsegs (w_H W) mem4 a = aview tfibsegs (w_H W) (ms_mem ms) a)
/\ (forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) mem4 a)
/\ YAkMemnorm.memnorm tfibsegs mem4).
Proof.
intros E3 W ms md ly S pb n buf len cap data bs MCPY HE HS E46 E58 E78 HAR HTOP Hbl Hpb Hlen0 Hn Hle Hcap HBLK Hbs Hrs Hslice HMN.
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp. pose proof (eagree_0 E3 HE) as E0'. pose proof (eagree_6 E3 HE) as E6'.
assert (Hin : In (buf, cap) (ablocks B ly S)) by (unfold ablocks; rewrite Hbl, <- Hpb; left; reflexivity).
pose proof (alc_blocks _ _ ARL ly S [] W (ms_mem ms) md buf cap HAR Hin) as (Hbufm & Hb4096 & Hbce & Happ & Hbytes & _).
assert (Hcapr : cap <= req_size cap) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia).
pose proof (YM05.ceil_le_top _ (top_ok_ceil _ _ HTOP)) as CLE. unfold stack_max_size in CLE.
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR. unfold ASAN_CEIL in CR.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E3 S_CP ms HS eq_refl) as Hshape.
set (regs := ms_regs ms) in *. set (mem := ms_mem ms) in *.
pose proof S_CP_facts as (_ & Fra & Fa0 & Fa1 & Fa2 & _ & Fsp).
assert (R1 : getr regs 1%bv = w64 RA_CP) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E3 S_CP ms 1%bv HS), Fra; reflexivity).
assert (R3 : getr regs 3%bv = w64 TFIB_GP) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E3 S_CP ms 3%bv HS); reflexivity).
assert (R4 : getr regs 4%bv = w64 TFIB_TP) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E3 S_CP ms 4%bv HS); reflexivity).
assert (R2 : getr regs 2%bv = Z_to_bv 64 (usp + -128)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E3 S_CP ms 2%bv HS), Fsp. cbn [sv_denot]. rewrite E0'. reflexivity. }
assert (R10 : getr regs 10%bv = w64 (buf + len)).
{ pose proof E46 as E46'. pose proof E58 as E58'. unfold A_BUF in E46'. unfold A_LEN in E58'.
rewrite (st_ok_restrict_reg tfibsegs (w_H W) E3 S_CP ms 10%bv HS), Fa0. rewrite (denot_lit_U E3). unfold w64. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff. rewrite !Z.add_0_r. first [rewrite E46 | rewrite E46']. first [rewrite E58 | rewrite E58'].
rewrite (zcanon_id buf), (zcanon_id len) by (unfold M64; lia).
apply zcanon_id. unfold M64; lia. }
assert (R11 : getr regs 11%bv = w64 RS_LO) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E3 S_CP ms 11%bv HS), Fa1; reflexivity).
assert (R12 : getr regs 12%bv = w64 n).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E3 S_CP ms 12%bv HS), Fa2. cbn [sv_denot]. pose proof E78 as E78'. unfold A_N in E78'.
rewrite Z.add_0_r. first [rewrite E78 | rewrite E78']. reflexivity. }
assert (Hsp' : spZ regs = usp - 128) by (unfold spZ; rewrite R2; rewrite u64_lit by (unfold sp_window_lo in Ulo; lia); lia).
pose proof (st_ok_mem_ok tfibsegs E3 S_CP _ HS) as HM. cbn [restrict ms_mem] in HM. fold mem in HM.
assert (Hwin : forall a, usp - 65536 <= a < usp - 128 -> apresent (w_H W) mem a).
{ intros a Ha. eapply (win_present sp Hsp E3 (w_H W) mem (ss_mem S_CP)); [exact HM | left; reflexivity | exact E0' | lia | lia | cbn; lia]. }
assert (NIMG : forall a, buf <= a < buf + req_size cap -> ~ in_img tfibsegs a).
{ intros a Ha. exact (proj2 (alc_client_img _ _ ARL ly S [] W mem md a HAR (or_introl (ex_intro _ buf (ex_intro _ cap (conj Hin Ha)))))). }
rewrite Hshape. change (Z_to_bv 64 (ss_pc S_CP)) with (w64 A_icpt_memcpy). fold regs mem.
change (mkCfg (mkst regs (w64 A_icpt_memcpy) mem (seg_rom tfibsegs)) md) with (cfg_at tfibsegs A_icpt_memcpy regs mem md).
change A_icpt_memcpy with (pc_wrap_memcpy Tfib_code). rewrite <- (ts_code B HB).
eapply SRr_mono.
{ apply (MCPY ly S W regs mem md (buf + len) RS_LO n).
- split; [exact HAR|]. split; [unfold top_ok in *; tauto|]. split; [rewrite R1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity|].
split; [rewrite Hsp'; replace (usp - 128) with (usp + (-8) * 16) by lia; rewrite Z.mod_add by lia; exact U16|].
split; [rewrite Hsp'; unfold sp_window_lo in *; lia|]. split; [rewrite Hsp'; unfold top_ok in HTOP; lia|].
split; [rewrite Hsp'; intros a Ha; apply Hwin; unfold ESTACK in Ha; lia|].
split; [rewrite (ts_gp B HB); exact R3 | rewrite (ts_tp B HB); exact R4].
- exact R10.
- exact R11.
- exact R12.
- lia.
- lia.
- lia.
-   intros a Ha. split; [| split].
+ apply (apresent_writable tfibsegs). exact (proj1 (Hbytes a ltac:(lia))).
+ exact (proj2 (Hbytes a ltac:(lia))).
+ rewrite Hsp'. unfold ESTACK. lia.
-   unfold amem_range. destruct Happ as [_ [Hlow | [Hh1 Hh2]]].
+ left. unfold kLowShadowBeg, kLowMemEnd in *. lia.
+ right. unfold kHighMemEnd in *. lia.
- apply (range_addressable_of_block'_cf B ARL ly S W mem md buf cap); [exact HAR | exact Hin | lia | lia].
- intros _. apply (shadow_hull_vis_of_block'_cf B ARL ly S [] W mem md buf cap); [exact HAR | exact Hin | lia | lia | lia].
- unfold RS_LO; lia.
- unfold RS_LO; lia.
-
intros a Ha. split.
+ unfold aview, mbyte, mrestrict. rewrite (seg_win_visible W RS_LO 65536 a (proj2 rs_win_check)) by (unfold RS_LO in *; lia).
specialize (Hrs (a - RS_LO) ltac:(lia)). replace (RS_LO + (a - RS_LO)) with a in Hrs by lia. fold mem in Hrs. rewrite Hrs.
destruct (nth_error bs (Z.to_nat (a - RS_LO))) eqn:En; [cbn; discriminate | apply nth_error_None in En; lia].
+ rewrite Hsp'. unfold RS_LO, ESTACK, sp_window_lo in *. lia.
-   destruct (Z.le_gt_cases (buf + len + n) RS_LO) as [|Hgt]; [left; exact H|]. right.
destruct (Z.le_gt_cases (RS_LO + n) (buf + len)) as [|Hgt2]; [lia|]. exfalso.
destruct (Z.le_gt_cases RS_LO (buf + len)) as [Hc|Hc].
+ apply (NIMG (buf + len) ltac:(lia)). apply rs_in_img. unfold RS_LO, RS_HI in *. lia.
+ apply (NIMG RS_LO ltac:(lia)). apply rs_in_img. unfold RS_LO, RS_HI. lia.
- left. unfold RS_LO, kLowMemEnd. lia.
- apply (rs_range_addressable_cf ly S W mem md n HAR); [lia | unfold RS_LO, RS_HI; lia].
- intros _. apply (rs_shadow_hull_vis_cf ly S W mem md n HAR); [lia | unfold RS_LO, RS_HI; lia]. }
cbv beta. intros W' c' _ (-> & regs4 & mem4 & md4 & -> & HAR4 & HP & Hs & Ha0 & Hcp & Hfr & Hpres & HMNK).
unfold raZ. rewrite R1. unfold w64. rewrite u64_lit by (unfold RA_CP; lia).
split; [reflexivity|]. exists regs4, mem4, md4. split; [reflexivity|].
rewrite Hshape, restrict_mkst_fx in HS. fold regs mem in HS.
assert (HST : st_ok tfibsegs (havoc E3 K_CP (map (getr regs4) CLOB)) S_CPp (mkst regs4 (Z_to_bv 64 RA_CP) (mrestrict (w_H W) mem4) (seg_rom tfibsegs))).
{ rewrite <- (proj1 S_eq_certs). unfold drv_after. change (junk_upd K_CP CLOB) with ([] ++ junk_upd K_CP CLOB).
apply (st_ok_splice_havoc tfibsegs K_CP E3 S_CP regs regs4 (w64 A_icpt_memcpy) RA_CP (mrestrict (w_H W) mem) (mrestrict (w_H W) mem4)
(WIN (-128) :: rs_CP) [] CLOB HS).
- exact (proj1 cp_checks).
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- reflexivity.
- exact (proj1 (proj2 (proj2 (proj2 cp_checks)))).
- cbn [map app]. apply regs_preserved_frame. apply aregs_regs_preserved. exact HP.
- constructor.
-
assert (SCR : forall a, 0 <= a < 2 ^ 64 -> ~ (buf + len <= a < buf + len + n) -> ~ (usp - 128 - ESTACK <= a < usp - 128) ->
mbyte tfibsegs (mrestrict (w_H W) mem4) a = mbyte tfibsegs (mrestrict (w_H W) mem) a).
{ intros a H0 H1 H2. apply (mbyte_of_aview tfibsegs). apply Hfr; [exact H0 | exact H1 | rewrite Hsp'; exact H2]. }
destruct HM as (Hwf & Hok & Hpd).
split; [exact (proj1 (proj2 cp_checks))|]. split.
+ pose proof (Forall_inv Hok) as Hr0. pose proof (Forall_inv_tail Hok) as Hrs0.
constructor.
*
split; [cbn [base_val r_base r_lo WIN]; rewrite E0'; unfold sp_window_lo in Ulo; lia|].
split; [cbn [base_val r_base r_hi WIN]; rewrite E0'; lia|]. split; [| constructor].
cbn [r_wlo r_whi r_base base_val WIN]. rewrite E0'. intros o Ho. apply (apresent_writable tfibsegs). apply Hpres. apply Hwin. lia.
* assert (Hsub : submem rs_CP (ss_mem S_CP)).
{ rewrite (proj2 (proj2 (proj2 (proj2 (proj2 cp_checks))))). change (ss_mem S_CP) with (hd R_errno (ss_mem S_CP) :: tl (ss_mem S_CP)). apply submem_drop. apply submem_filter. }
assert (HMt : mem_ok tfibsegs E3 (mrestrict (w_H W) mem) rs_CP).
{ apply (mem_ok_sub tfibsegs E3 _ _ rs_CP Hsub). 2:{ split; [exact Hwf|]. split; [exact Hok | exact Hpd]. }
pose proof (proj1 (proj2 cp_checks)) as W2. cbn in W2. apply andb_prop in W2. tauto. }
assert (HK : Forall (region_kept tfibsegs E3 (mrestrict (w_H W) mem) (mrestrict (w_H W) mem4)) rs_CP).
{ apply Forall_forall. intros r Hr.
pose proof (proj1 (forallb_forall _ _) (proj1 (proj2 (proj2 (proj2 (proj2 cp_checks))))) r Hr) as Hc. unfold drv_keep_ok in Hc.
pose proof (proj1 (Forall_forall _ _) (proj1 (proj2 HMt)) r Hr) as (B1 & B2 & _).
assert (OFF : forall a, base_val E3 (r_base r) + r_lo r <= a < base_val E3 (r_base r) + r_hi r ->
~ (buf + len <= a < buf + len + n) /\ ~ (usp - 128 - ESTACK <= a < usp - 128)).
{ intros a Ha. destruct (r_base r) as [[|[|[|[|[|[|[|k]]]]]]]|]; try discriminate Hc; cbn [base_val] in Ha, B1, B2.
- apply andb_prop in Hc as [Hc _]. apply Z.leb_le in Hc. rewrite E0' in Ha. unfold ESTACK, sp_window_lo in *. lia.
- apply andb_prop in Hc as [Hc _]. apply Z.leb_le in Hc. pose proof (u64_range (ew E3 6)). unfold ESTACK, sp_window_lo in *. lia.
- apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc1 Hc2].
apply Z.leb_le in Hc1. apply Z.leb_le in Hc2. split; [| unfold ESTACK, sp_window_lo in *; lia].
intros Hab. apply (NIMG a ltac:(lia)). apply in_img_hull. lia. }
split; intros a Ha; [apply SCR; [lia | apply OFF; exact Ha | apply OFF; exact Ha]|].
intros Hw. exact (wview_grows tfibsegs _ _ _ (mem_grows_of_apresent (w_H W) mem mem4 Hpres) Hw). }
exact (proj1 (proj2 (mem_ok_kept tfibsegs E3 _ (mrestrict (w_H W) mem4) rs_CP HMt ltac:(pose proof (proj1 (proj2 cp_checks)) as W2; cbn in W2; apply andb_prop in W2; tauto) HK))).
+
assert (Hsub : submem rs_CP (ss_mem S_CP)).
{ rewrite (proj2 (proj2 (proj2 (proj2 (proj2 cp_checks))))). change (ss_mem S_CP) with (hd R_errno (ss_mem S_CP) :: tl (ss_mem S_CP)). apply submem_drop. apply submem_filter. }
assert (HMt : mem_ok tfibsegs E3 (mrestrict (w_H W) mem) rs_CP).
{ apply (mem_ok_sub tfibsegs E3 _ _ rs_CP Hsub). 2:{ split; [exact Hwf|]. split; [exact Hok | exact Hpd]. }
pose proof (proj1 (proj2 cp_checks)) as W2. cbn in W2. apply andb_prop in W2. tauto. }
split; [| exact (proj2 (proj2 HMt))].
pose proof (proj1 (proj2 (proj2 (proj2 (proj2 cp_checks))))) as Hchk. clear - Hchk E0' E6' Ulo. unfold sp_window_lo in Ulo.
induction rs_CP as [|r rs IH]; cbn; [exact I|]. cbn in Hchk. apply andb_prop in Hchk as [Hc Hchk].
split; [|exact (IH Hchk)]. unfold extent_disjoint. cbn [r_base r_lo r_hi WIN base_val]. rewrite E0'.
unfold drv_keep_ok in Hc. destruct (r_base r) as [[|[|[|[|[|[|[|k]]]]]]]|]; try discriminate Hc; cbn [base_val].
* apply andb_prop in Hc as [Hc _]. apply Z.leb_le in Hc. rewrite E0'. left. lia.
* apply andb_prop in Hc as [Hc _]. apply Z.leb_le in Hc. left. pose proof (u64_range (ew E3 6)). lia.
* apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [_ Hc]. apply Z.leb_le in Hc. right. lia. }
rewrite <- restrict_mkst_fx in HST. split; [exact HST|]. split; [exact HAR4|]. split; [exact Hs|].
split; [| split; [intros a H0 H1 H2; apply Hfr; [exact H0 | exact H1 | rewrite Hsp'; exact H2] | split; [exact Hpres | exact (HMNK HMN)]]].
intros i Hi. destruct (Z.lt_ge_cases i len) as [Hil|Hil].
- rewrite <- (HBLK i ltac:(lia)). apply (restrict_of_aview (w_H W) mem mem4 (buf + i)); [lia | apply NIMG; lia |].
apply Hfr; [lia | lia | rewrite Hsp'; unfold ESTACK; lia].
- pose proof (Hcp (i - len) ltac:(lia)) as X. replace (buf + len + (i - len)) with (buf + i) in X by lia.
pose proof (Hrs (i - len) ltac:(lia)) as Y. rewrite (Hslice (Z.to_nat (i - len)) ltac:(lia)) in Y.
replace (Z.to_nat len + Z.to_nat (i - len))%nat with (Z.to_nat i) in Y by lia.
destruct (nth_error data (Z.to_nat i)) as [b|] eqn:En.
+ apply (restrict_some_of_aview (w_H W) mem4 (buf + i) b); [lia | apply NIMG; lia |]. rewrite X.
unfold aview, mbyte, mrestrict. rewrite (seg_win_visible W RS_LO 65536 (RS_LO + (i - len)) (proj2 rs_win_check)) by (unfold RS_LO in *; lia).
fold mem. rewrite Y. reflexivity.
+ exfalso. pose proof (Hslice (Z.to_nat (i - len)) ltac:(lia)) as Z1.
replace (Z.to_nat len + Z.to_nat (i - len))%nat with (Z.to_nat i) in Z1 by lia. rewrite En in Z1.
apply nth_error_None in Z1. lia.
Qed.
End f.
End Rd.
End e.

Print Assumptions rd_step_pos_cf.
Print Assumptions rd_step_eof_cf.
Print Assumptions rd_chk_cf.
Print Assumptions rd_cpy_cf.
