(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the proof of tfib_post_P_cf_A of lib/A/PresetD2runA.v (fuzz_preset's asan
   image), ported from proofs/cgif/cgif_file_fuzzer/lib/A (relocated here as lib/A):
     AD2b.v:72-145  tfib_to_P       -> tfib_to_P_cf
     AD2c.v:87-163  tfib_post_P_at  -> tfib_post_P_at_cf, tfib_post_P -> tfib_post_P_cf.
   The RUNQ proof (AD2d.v) is lib/A/PresetD2runQAPf.v.
   The changes are the statement file's (PresetD2runA.v header (1)-(6)): AR -> ARcf at Hp = [] with a8's proved laws
   AR_laws_ok_cf (lib/Reusable/YG0lawscf.v); the event bounds are dropped; the tail is CwSites' tail_at_pinv_A B NP
   (lib/A/PresetD1sitesA.v), whose non-primary room NP S and xs_placed_cf pass unchanged along the symbolic runs (no
   allocator call between the header and the loop / the payload malloc); FINV -> PINV at 0 0, kept across a driver
   run by CwPinvA's PROVED finv_run_pinv_A_holds (lib/A/PresetPinvAPf.v:117).
   The donors' AR-free lemmas (hdr_regions_ok, ...) are cited from the donor files; the two runs pb_run / bq_run are
   their memnorm twins (lib/A/AD2mnSeg.v, at P := YAkMemnorm.memnorm tfibsegs with
   YSRrMemnorm.srr_inv_laws_memnorm_k), so the tail's memnorm of the full overlay reaches RUNQ's tail (lane MnPrefix).
   Nothing in this file is a proof of a function (rule 24: the driver layer of a port). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0d YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK00 YK0h YK14 YK1b YK15 YK18 YK0p YP0n YK0s YM02 YP0m YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0g YP0e YN3q YN3v YI04 YL0a YL09 YL02 YL04 YK04 YA0i YA0n YA0o YA0p YA0m YK09 YA0e YG00 YG01 YG0f YG0v YG0n YG0d YCe5.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB12 AF0l AB1h AB13 AF0m AD2j AD2i AD1t AD20 AD1v AD1y AD26 AD24.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import ACeg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AD21 AD25 AD23 AD2h AD1w AD2f AD2b AD2g AD1s AD2c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf YGcfRoomPre YGcfTok YG07cf YGcfXs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PresetD1sitesA PresetD2runA PresetD1rAx PresetPinvA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PresetPinvAPf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD2mnSeg.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PresetCfnA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallStackUp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetStkUpA.
Module PCA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PresetCfnA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section pf.
Let Hfinv_run : finv_run_pinv_A := finv_run_pinv_A_holds.   (* CwPinvA, lib/A/PresetPinvAPf.v:117 *)

(* ---------------------------------------------------------------------- *)
(* 1. POSTP: AD2b.v:72 tfib_to_P, AD2c.v:87 tfib_post_P_at.                *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape} {ci : CfImg} {cp : CfParams}.
Section d.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Let ARL : AR_laws_cf tfibsegs B := AR_laws_ok_cf tfibsegs B.
Variable iface_room_np : astate -> Prop.
Variable NR : ProcInput -> Prop.
Hypothesis RUNQ : run_Q_tfa_cf (LS := LS) B iface_room_np NR.
Variables (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (a0 p : list byte).
Hypothesis Hargv : in_argv inp = [a0; p].
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv [a0; p].
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hvfs : valid_fs (in_fs inp).
Hypothesis HNR : NR inp.
#[local] Notation EL := (YP08.E0 sp [a0; p] (in_envp inp) xw xd).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation envp := (in_envp inp).

(* AD2b.v:72 *)
Lemma tfib_to_P_cf : forall ws (W : world tfibsegs) ms md ly S data (pb : sptr) cap,
let E' := edset (havoc EL K_M1 ws) 2 data in
let buf := sptr_addr B ly pb in
6 + config_len data <= dlen data ->
tail_at_pinv_A B iface_room_np S_P E' sp inp a0 p data W ms md ly S pb cap ->
st_ok tfibsegs (E_P E' data (buf + 2 + config_len data)) (if config_len data =? 0 then ssP0 else ssP1) (restrict (w_H W) ms)
/\ bv_unsigned (ew (E_P E' data (buf + 2 + config_len data)) K_PP) = buf + 2 + config_len data.
Proof.
intros ws W ms md ly S data pb cap E' buf Hok (HS & E41 & E42 & HR & HAI & HAR & HRK & HTOP & Hbl & Hcap & HLc & HBLK & Hfs & Hfds & Hminv & HPI & HXS & _).
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp. pose proof (proj1 (@YM05.alloc_ceiling_value rc)) as CV.
pose proof (top_ok_ceil _ _ HTOP) as HCT. pose proof (YM05.ceil_le_top _ HCT) as CLE. unfold stack_max_size in CLE.
pose proof (config_len_bound data) as Hcl. fold buf in E41, HBLK. unfold dlen in *.
assert (Hin : In (buf, cap) (ablocks B ly S)) by (unfold ablocks; rewrite Hbl; left; reflexivity).
pose proof (alc_blocks _ _ ARL ly S [] W (ms_mem ms) md _ _ HAR Hin) as (_ & Hb4096 & Hbce & _).
assert (Hcap' : cap <= req_size cap) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia).
assert (NIMG : forall a, buf <= a < buf + cap -> ~ in_img tfibsegs a).
{ intros a Ha. assert (Ha' : buf <= a < buf + req_size cap) by lia.
exact (proj2 (alc_client_img _ _ ARL ly S [] W (ms_mem ms) md a HAR (or_introl (ex_intro _ _ (ex_intro _ cap (conj Hin Ha')))))). }
set (pP := buf + 2 + config_len data). set (E3 := E_P E' data pP).
assert (HpP : 0 <= pP < 2 ^ 64) by (subst pP; lia).
assert (E3_60 : bv_unsigned (ew E3 161) = pP) by (subst E3; apply E_P_161; exact HpP).
assert (E3_41 : bv_unsigned (ew E3 A_BUF) = buf) by (subst E3; rewrite E_P_old by (unfold A_BUF; lia); exact E41).
assert (E3_42 : bv_unsigned (ew E3 A_LEN) = Z.of_nat (length data)) by (subst E3; rewrite E_P_old by (unfold A_LEN; lia); exact E42).
assert (E3_0 : bv_unsigned (ew E3 0) = usp) by (subst E3 E'; rewrite E_P_old by lia; cbn [ew edset]; rewrite ew_havoc_old by (unfold K_M1; lia); reflexivity).
assert (Ed2 : ed E3 2 = data) by (subst E3 E'; rewrite E_P_ed by lia; reflexivity).
destruct (list_len2p data ltac:(lia)) as (d0 & d1 & rest & Ed).
assert (Hd : ed E3 2 = d0 :: d1 :: rest) by (rewrite Ed2; exact Ed).
split; [| exact E3_60].
pose proof S_Pm_facts as (Hmem & Hpc & Hrv & Hregs & Hfacts & Hwfm).
assert (HS1 : st_ok tfibsegs E' S_Pm (restrict (w_H W) ms)).
{ destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9). unfold st_ok. rewrite Hpc, Hrv, Hregs, Hfacts.
repeat (split; [assumption|]). split; [| exact H9].
apply (mem_ok_sub tfibsegs E' _ (ss_mem S_P)); [rewrite Hmem; apply submem_app_r | exact Hwfm | exact H8]. }
pose proof (st_ok_agree_pd tfibsegs _ _ E' E3 S_Pm _ HS1 (E_P_agree E' data pP) S_Pm_pd) as HS2. clear HS1.
destruct HS2 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
assert (HS3 : st_ok tfibsegs E3 (mkSS (ss_pc S_Pm) (sr_set (ss_regs S_Pm) 10%bv (SOff 161 0)) (ss_mem S_Pm) None
(mkFacts ((161%nat, fact_P) :: f_atoms (ss_facts S_Pm)) (f_conds (ss_facts S_Pm)) (f_alias (ss_facts S_Pm))))
(restrict (w_H W) ms)).
{ unfold st_ok. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts]. repeat (split; [assumption|]). split; [| split; [exact H8|]].
- intros r. destruct (decide (r = 10%bv)) as [->|Hne].
+ rewrite sr_get_set_same by reflexivity. rewrite (H7 10%bv). rewrite Hregs, (proj1 (proj2 (proj2 (proj2 S_P_regs)))).
rewrite (denot_lit_U E3 (SOff 161 0)), (denot_lit_U E3 (SAlu ALU_ADD (SOff A_BUF 2) sv_cl)). f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, (U_cl E3 d0 d1 rest Hd), E3_41, E3_60, <- Ed.
rewrite (zcanon_id (buf + 2)) by (unfold M64; lia). rewrite !zcanon_id by (unfold M64; lia). subst pP. lia.
+ rewrite sr_get_set_other by exact Hne. apply H7.
- apply facts_ok_add_atom; [exact H9|]. unfold afact_ok, fact_P. cbn [af_lo af_hi af_al2]. rewrite E3_60.
change (2 ^ 0) with 1. rewrite Z.mod_1_r. subst pP. lia. }
set (h := if config_len data =? 0 then 2 else 3).
assert (Hh : 2 <= h <= 3) by (subst h; destruct (config_len data =? 0); lia).
assert (HS4 : st_ok tfibsegs E3 (mkSS (ss_pc S_Pm) (sr_set (ss_regs S_Pm) 10%bv (SOff 161 0)) (ss_mem S_Pm ++ [RBh h; R161]) None
(mkFacts ((161%nat, fact_P) :: f_atoms (ss_facts S_Pm)) (f_conds (ss_facts S_Pm)) (f_alias (ss_facts S_Pm))))
(restrict (w_H W) ms)).
{ apply (st_ok_app_regions E3 _ (restrict (w_H W) ms) [RBh h; R161] HS3 (RBh_wf h Hh)).
- cbn [ms_mem restrict]. apply (hdr_regions_ok E3 (w_H W) (ms_mem ms) data buf pP h E3_41 E3_60 Ed2); try assumption; try (unfold dlen; lia).
subst E3. apply E_P_ed3.
- cbn. split; [| exact (conj I I)]. split; [| exact I].
unfold extent_disjoint. cbn [base_val r_base r_lo r_hi RBh R161]. rewrite E3_41, E3_60. left. subst pP h.
destruct (Z.eqb_spec (config_len data) 0); lia.
- intros r1 r2 Hr1 Hr2.
pose proof (proj1 (forallb_forall _ _) S_Pm_hext r1 Hr1) as Y. unfold hext_chk in Y.
pose proof (proj1 (forallb_forall _ _) S_Pm_hlo r1 Hr1) as Y2. cbn beta in Y2.
assert (LO : forall lo2 hi2, buf <= lo2 -> hi2 <= buf + cap ->
base_val E3 (r_base r1) + r_hi r1 <= lo2 \/ hi2 <= base_val E3 (r_base r1) + r_lo r1).
{ intros lo2 hi2 Hlo2 Hhi2. destruct (r_base r1) as [[|[|[|[|[|[|[|n]]]]]]]|]; try discriminate Y; cbn [base_val].
+ apply Z.leb_le in Y. rewrite E3_0. unfold sp_window_lo in Ulo. right. lia.
+ apply Z.leb_le in Y. subst E3 E'. rewrite E_P_old by lia. cbn [ew edset]. rewrite ew_havoc_old by (unfold K_M1; lia).
pose proof (AD2b.EL6 sp inp xw xd a0 p Hsp Hva Hve) as R6. unfold sp_window_lo in Ulo. right. lia.
+ apply Z.leb_le in Y. apply Z.leb_le in Y2.
destruct (Z.le_gt_cases (r_hi r1) lo2) as [|Hgt]; [left; lia|]. destruct (Z.le_gt_cases hi2 (r_lo r1)) as [|Hgt2]; [right; lia|].
exfalso. apply (NIMG (Z.max buf YImgTop.IMG_LO)); [unfold YImgTop.IMG_LO; lia|]. apply in_img_hull. unfold YImgTop.IMG_LO; lia. }
unfold extent_disjoint. destruct Hr2 as [<- | [<- | []]]; cbn [base_val r_base r_lo r_hi RBh R161]; [rewrite E3_41 | rewrite E3_60]; apply LO; subst pP; lia. }
subst h. rewrite Hpc, Hregs, Hfacts in HS4. pose proof ssP_eq as [Q2 Q3].
destruct (config_len data =? 0); [rewrite <- Q2 | rewrite <- Q3]; exact HS4.
Qed.

(* AD2c.v:87 *)
Theorem tfib_post_P_at_cf : forall ws (W : world tfibsegs) ms md ly S data (pb : sptr) cap,
fs_lookup (in_fs inp) p = Some data -> 6 + config_len data <= dlen data ->
tail_at_pinv_A B iface_room_np S_P (edset (havoc EL K_M1 ws) 2 data) sp inp a0 p data W ms md ly S pb cap ->
YGcallStackUp.astack_up_x tfibsegs ly W usp (ms_mem ms) ->
srealizes tfibsegs (mkCfg ms md) (run_shape (LS := LS) (payload data) (calls data) (in_fs inp)).
Proof.
intros ws W ms md ly S data pb cap Hlk Hok HT HUP0.
pose proof (YSRrMemnorm.srr_inv_laws_memnorm_k tfibsegs) as PLAW.
pose proof (tfib_to_P_cf ws W ms md ly S data pb cap Hok HT) as [HSP E60].
destruct HT as (HS & E41 & E42 & HR & HAI & HAR & HRK & HTOP & Hbl & Hcap & HLc & HBLK & Hfs & Hfds & Hminv & HPI & HXS & HMN).
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp.
pose proof (top_ok_ceil _ _ HTOP) as HCT. pose proof (YM05.ceil_le_top _ HCT) as CLE. unfold stack_max_size in CLE.
set (E' := edset (havoc EL K_M1 ws) 2 data) in *. set (buf := sptr_addr B ly pb) in *.
set (E3 := E_P E' data (buf + 2 + config_len data)) in *.
pose proof (config_len_bound data) as Hcl. unfold dlen in *.
assert (Hin : In (buf, cap) (ablocks B ly S)) by (unfold ablocks; rewrite Hbl; left; reflexivity).
pose proof (alc_blocks _ _ ARL ly S [] W (ms_mem ms) md _ _ HAR Hin) as (_ & Hb4096 & Hbce & _).
assert (Hcap' : cap <= req_size cap) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia).
assert (NIMG : forall a, buf <= a < buf + cap -> ~ in_img tfibsegs a).
{ intros a Ha. assert (Ha' : buf <= a < buf + req_size cap) by lia.
exact (proj2 (alc_client_img _ _ ARL ly S [] W (ms_mem ms) md a HAR (or_introl (ex_intro _ _ (ex_intro _ cap (conj Hin Ha')))))). }
assert (E3_0 : bv_unsigned (ew E3 0) = usp) by (subst E3 E'; rewrite E_P_old by lia; cbn [ew edset]; rewrite ew_havoc_old by (unfold K_M1; lia); reflexivity).
assert (E3_41 : bv_unsigned (ew E3 A_BUF) = buf) by (subst E3; rewrite E_P_old by (unfold A_BUF; lia); exact E41).
assert (E3_42 : bv_unsigned (ew E3 A_LEN) = Z.of_nat (length data)) by (subst E3; rewrite E_P_old by (unfold A_LEN; lia); exact E42).
assert (Ed2 : ed E3 2 = data) by (subst E3 E'; rewrite E_P_ed by lia; reflexivity).
destruct (list_len3 data ltac:(lia)) as (d0 & d1 & d2 & rest & Ed).
assert (Hd' : ed E3 2 = d0 :: d1 :: (d2 :: rest)) by (rewrite Ed2; exact Ed).
assert (UCL : U E3 sv_cl00 = config_len data).
{ unfold sv_cl00. rewrite !U_add0. transitivity (config_len (d0 :: d1 :: d2 :: rest)); [exact (U_cl E3 d0 d1 (d2 :: rest) Hd') | rewrite <- Ed; reflexivity]. }
set (c0 := config_len data =? 0) in *.
apply (SRr_srealizes tfibsegs W (mkCfg ms md) _ _ (AD2mnSeg.pb_run_mn _ PLAW c0 E3 W ms md HSP HMN) HAI).
intros W0 c' _ HAI1 [(-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1) (msA & mdA & EcA & HMN1)]. injection EcA as <- <-. cbn [cfg_model] in HAI1.
assert (HS2 : st_ok tfibsegs E3 (add_cond (if c0 then sB0 else sB1) (if c0 then cond_CL0 else cond_CL1)) (restrict (w_H W) ms1)).
{ subst c0. destruct (Z.eqb_spec (config_len data) 0) as [Hz|Hnz].
- apply (st_ok_add_cond tfibsegs E3 sB0 _ BC_EQ sv_cl00 (SLit 0) HS1). rewrite branch_eq_U, UCL, U_SLit, Hz. reflexivity.
- apply (st_ok_add_cond tfibsegs E3 sB1 _ BC_NE sv_cl00 (SLit 0) HS1). rewrite branch_ne_U, UCL, U_SLit. change (zcanon 0) with 0.
apply Bool.negb_true_iff. apply Z.eqb_neq. exact Hnz. }
apply (SRr_srealizes tfibsegs W _ _ _ (AD2mnSeg.bq_run_mn _ PLAW c0 E3 W ms1 _ HS2 HMN1) HAI1).
intros W1 c2 _ HAI2 [(-> & ms2 & mat2 & -> & HS3 & HF2 & HFr2) (msB & mdB & EcB & HMN2)]. injection EcB as <- <-. cbn [cfg_model] in HAI2.
rewrite wvb_collapse in HAI2 |- *.
assert (HS4 : st_ok tfibsegs E3 (sQ c0 (Z.of_nat (calls data))) (restrict (w_H W) ms2)).
{ unfold sQ. subst c0. destruct (Z.eqb_spec (config_len data) 0) as [Hz|Hnz]; [exact HS3|].
unfold sQ1k. apply (st_ok_setreg E3 sQ1 _ 21%bv (SLit (Z.of_nat (calls data))) HS3 eq_refl).
pose proof sBQ_facts as (_ & _ & _ & _ & _ & _ & _ & Q20 & _). rewrite Q20.
rewrite (denot_lit_U E3 (SLit _)), (denot_lit_U E3 sv_calls). f_equal. rewrite U_SLit, (U_calls E3 data d0 d1 d2 rest Ed2 Ed Hnz).
pose proof (calls_bound data). apply zcanon_id. unfold M64. lia. }
pose proof skel_B as [SK0 SK1].
assert (SK : skeleton (ss_mem (if c0 then sB0 else sB1)) = skeleton (ss_mem (if c0 then ssP0 else ssP1))) by (destruct c0; [exact SK0 | exact SK1]).
assert (WOK : forallb drv_win_ok (ss_mem (if c0 then ssP0 else ssP1)) = true) by (destruct c0; [exact ssP0_win_ok | exact ssP1_win_ok]).
assert (HF : frame_of E3 (ss_mem (if c0 then ssP0 else ssP1)) (ms_mem ms) (ms_mem ms2)).
{ apply (frame_of_trans E3 _ _ _ _ _ eq_refl HF1). exact (frame_of_skel' E3 _ _ _ _ (eq_sym SK) HF2). }
assert (HFr : frame_of E3 (ss_mem (if c0 then ssP0 else ssP1)) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms2))).
{ apply (frame_of_trans E3 _ _ _ _ _ eq_refl HFr1). exact (frame_of_skel' E3 _ _ _ _ (eq_sym SK) HFr2). }
(* #102 (lane StackDrv): the live stack above usp across pb_run / bq_run (their frame is below usp) *)
assert (HUP2 : YGcallStackUp.astack_up_x tfibsegs ly W usp (ms_mem ms2))
by exact (PresetStkUpA.stk_up_frame E3 _ ly W (ms_mem ms) (ms_mem ms2) usp WOK E3_0 ltac:(lia) HTOP HF HUP0).
pose proof (st_ok_mem_ok tfibsegs E3 _ _ HS4) as HM4. cbn [restrict ms_mem] in HM4.
assert (Hwin : forall a, usp - 65536 <= a < usp -> apresent (w_H W) (ms_mem ms2) a).
{ intros a Ha. unfold sQ, sQ1k, setreg_ in HM4. cbn [ss_mem] in HM4.
destruct c0; destruct (Z.lt_ge_cases a (usp - 128)).
- eapply (win_present sp Hsp E3 (w_H W) (ms_mem ms2) (ss_mem sQ0)); [exact HM4 | left; reflexivity | exact E3_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E3 (w_H W) (ms_mem ms2) (ss_mem sQ0)); [exact HM4 | right; left; reflexivity | exact E3_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E3 (w_H W) (ms_mem ms2) (ss_mem sQ1)); [exact HM4 | left; reflexivity | exact E3_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E3 (w_H W) (ms_mem ms2) (ss_mem sQ1)); [exact HM4 | right; left; reflexivity | exact E3_0 | lia | lia | cbn; lia]. }
apply (RUNQ sp inp xw xd ws W ms2 _ ly S a0 p data pb cap Hargv Hsp Hva Hve Hvfs HNR Hlk ltac:(unfold dlen; lia)); [| exact HUP2 | exact E60].
split; [exact HS4|]. split; [exact E3_41|]. split; [exact E3_42|]. split.
{ eapply (runs_at_frame E3 (ss_facts (sQ c0 (Z.of_nat (calls data)))) (ss_mem (if c0 then ssP0 else ssP1)));
[exact (st_ok_facts_ok tfibsegs E3 _ _ HS4) | | exact HFr | rewrite E3_0; lia | exact HR].
unfold sQ, sQ1k, setreg_. cbn [ss_facts]. pose proof wbs_Q as [WQ0 WQ1]. destruct c0; [exact WQ0 | exact WQ1]. }
split; [exact HAI2|]. split.
{ apply (AR_after_run_cf B HB ARL ly S [] W E3 _ (ms_mem ms) (ms_mem ms2) md mat2 HAR WOK); [rewrite E3_0; exact Ulo | rewrite E3_0; exact HCT | exact HF |].
rewrite E3_0. intros a Ha. exact (apresent_some' _ _ _ (Hwin a Ha)). }
split; [exact HRK|]. split; [exact HTOP|]. split; [exact Hbl|]. split; [exact Hcap|]. split; [unfold dlen; lia|]. split.
{ unfold dlen. apply (blk_of_frame_r _ _ _ _ _ buf (Z.of_nat (length data)) data usp HFr WOK E3_0 Ulo); [intros a Ha; apply NIMG; lia | lia | lia | exact HBLK]. }
split; [rewrite wvb_fs'; exact Hfs |]. split; [rewrite wvb_fds'; exact Hfds |]. split; [exact Hminv|]. split; [| split; [exact HXS | exact HMN2]].
exact (Hfinv_run (w_H W) E3 _ (ms_mem ms) (ms_mem ms2) usp 0 0 HFr WOK E3_0 Ulo HPI).
Qed.
End d.

(* AD2c.v:159 *)
Theorem tfib_post_P_cf (B : asyms) (iface_room_np : astate -> Prop) (NR : ProcInput -> Prop) (HB : TfibSyms B)
(RUNQ : run_Q_tfa_cf (LS := LS) B iface_room_np NR) : post_P_tfa_cf (LS := LS) B iface_room_np NR.
Proof.
intros sp inp xw xd ws W ms md ly S a0 p data pb cap Hargv Hsp Hva Hve Hvfs HNR Hlk Hok HT HUP0.
exact (tfib_post_P_at_cf B HB iface_room_np NR RUNQ sp inp xw xd a0 p Hargv Hsp Hva Hve Hvfs HNR ws W ms md ly S data pb cap Hlk Hok HT HUP0).
Qed.
End c.

(* ---------------------------------------------------------------------- *)
(* 3. The closed results of PresetD2runA.v section 3.                      *)
Theorem tfib_post_P_cf_A_holds : tfib_post_P_cf_A.
Proof.
intros fx rc LS ci cp B iface_room_np NR HB RUNQ.
exact (tfib_post_P_cf (LS := LS) B iface_room_np NR HB RUNQ).
Qed.
End pf.

Print Assumptions tfib_post_P_cf_A_holds.
