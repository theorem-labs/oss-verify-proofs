(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the third segment of sup_pool_config's ASan walk (plugin-hostd/fuzz_command): from
   the call of xstrdup (0x8bdb4) through arg_i, whose printf may change the FP state, to the last segment
   (sup_pool_config_w4.v) at the FP state arg_i returned, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v .. ACh8.v (a seed, the symbolic run to a call, the callee's
   contract through cl_callS, the state after the call). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YC5d YG0q YI67.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdChk CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c arg_i_c rec_shape_of_c answer_c hand_back_c mix_call_c sup_pool_config_c PaNoChain PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
RecBLemmas sup_pool_config_s1 sup_pool_config_s2 sup_pool_config_s3 sup_pool_config_s4 sup_pool_config_s5
sup_pool_config_d sup_pool_config_w4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HY : spc_hyps B MT.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Lemma spc_seg_dup : forall ly S W regs mem md ch pn max name R O,
spc_pre B MT ly S W regs mem md ch pn max name R O ->
spc_cont_D B MT ly S W regs mem md R O name max.
Proof.
intros ly S W regs mem md ch pn max name R O HPRE lyB SBs rdB lyc Sc Wc memc mdc regs1 s O0 F HMID.
spc_unpack HY.
destruct HPRE as (HFN & HFR0 & HROD & HRO & H10 & Hpn & H11 & Hmax & HSTR & HREP & HFR8 & HEV & HLIVE & HMOK).
pose proof HFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
set (sp0 := spZ regs) in *.
set (c := spc_slot R) in *. set (x := sarg name) in *.
destruct HMID as (HJ & HBL & HFO & HO0 & HFS & HBB & HMLE & HFRM & HREPB & HKB & HKO & HNC & HFN14 & HNA0 & HSTRc & HTAILc &
  R2 & R8 & R9 & R18 & R19 & R20 & R21 & RK).
pose proof HJ as (HARc & Hlyc & _ & HWc & _ & Hfrc & Hnevc & _).
destruct (spc_rep_ncalls B ly S _ R O HREP) as [_ Hlen16].
pose proof (spc_slot_okR R Hlen16) as Hc. fold c in Hc.
destruct (spc_slot_bounds c Hc) as [Hcb Hc8].
assert (HSTKv : SUP_POOL_CONFIG_STK = 16592) by (vm_compute; reflexivity).
rewrite HSTKv in *.
assert (Hsp46 : 2 ^ 46 <= sp0 - 64) by lia.
(* the seed *)
destruct (spc_seed B LAWS HB SPC_DUP spc_regsD spc_slot_fn0 Wc regs regs1 memc sp0 0 c lyc Sc mdc HARc
  ltac:(vm_compute; reflexivity) Hsp46 ltac:(lia) Hsp16 Hc
  ltac:(rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; reflexivity)) as [HS SHOK].
{ exact (spc_regs_okD regs regs1 c ltac:(lia) R9 R19 R20 R21). }
{ exact HFRM. }
{ intros a Ha. apply (cmd_prog_writable lyc Sc Wc memc mdc a HARc). exact (spc_slot_PG c a Hc Ha). }
{ unfold spc_slot_fn0. constructor; [|constructor; [|constructor]].
  - apply (chunk_ok_val SEGS _ _ c 4 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
    exact (val_mem_view SEGS (w_H Wc) memc (c + 4) 4 0 HNA0).
  - apply (chunk_ok_val SEGS _ _ c 0 4 (SLit REC_POOL_CONFIG) REC_POOL_CONFIG); [reflexivity | cbn; unfold REC_POOL_CONFIG; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_view SEGS (w_H Wc) memc c 4 REC_POOL_CONFIG HFN14). }
set (E := Eimg (Ereg regs1 (spc_extra regs 0 c))) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
paj_run_tok RUN HS HJ SHOK SPC_SPAN.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen; [reflexivity | | | apply awr_ok_nil].
  - destruct (spc_E_lit regs regs1 0 c) as (_ & _ & E34). fold E in E34. rewrite E34.
    apply unsigned_lit_small. unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia.
  - intros a Ha. cbn [YP09.r_wlo YP09.r_whi spc_slot_rg] in Ha.
    exact (spc_awr_slot B HB cmd_prog_img _ _ _ _ _ _ _ _ c a Hc ltac:(unfold CALL_SIZE in *; lia)). }
pmkst HS. spc_md.
(* 0x8bdb8: the call of xstrdup on s *)
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r) by exact (spc_E_reg regs regs1 0 c).
destruct (spc_E_lit regs regs1 0 c) as (E32 & _ & E34). fold E in E32, E34.
assert (B34 : base_val E (Some 34%nat) = c)
  by (cbn [base_val]; rewrite E34; apply unsigned_lit_small; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
assert (B34u : bv_unsigned (ew E 34) = c) by exact B34.
rewrite (EE 2%nat 2%bv eq_refl), R2 in P2. rewrite (EE 3%nat 3%bv eq_refl) in P3. rewrite (EE 4%nat 4%bv eq_refl) in P4.
rewrite (EE 8%nat 8%bv eq_refl), R8 in P8. rewrite (EE 18%nat 18%bv eq_refl), R18 in P10.
assert (P3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3; exact (eq_trans (RK 3 ltac:(cbn; tauto)) Hgp)).
assert (P4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4; exact (eq_trans (RK 4 ltac:(cbn; tauto)) Htp)).
pose proof Hlyc as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
(* the memory at the call differs from memc only in the slot *)
assert (KS : forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + CALL_SIZE) -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn. apply (recb_run_keeps_m E _ (w_H Wc) memc (ms_mem ms) a HFr Ha).
  intros Hw. apply Hn. exact (spc_wrange_slot E c _ a B34 Hw). }
destruct (spc_argA_slot B RLO RHI LAWS cmd_prog_img cmd_ro_prog_apart lyc Sc Wc memc (ms_mem ms) mdc c s x HARc Hc KS HSTRc HTAILc)
  as [HARGT HTAILT].
(* the budgets of the rest of the call *)
set (t := snd (sup_pool_config_m R name max)) in *.
assert (HMN : 0 <= mo_free MT /\ (forall n, 0 <= n -> 0 <= mo_malloc MT n))
  by (split; [exact (mo_free_nonneg MT MTL) | exact (mo_malloc_nonneg MT MTL)]).
assert (XMX : 0 <= XM_XSTRDUP MT x) by (unfold XM_XSTRDUP; apply (proj2 HMN); lia).
assert (XMI : 0 <= XM_ARG_I MT max) by (unfold XM_ARG_I, XM_XSTRDUP; apply (proj2 HMN); lia).
assert (XMA : 0 <= XM_ANSWER MT t).
{ unfold XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP. pose proof (proj2 HMN (Z.of_nat (length t) + 1) ltac:(lia)). lia. }
assert (HEVX : st_nev Sc + EV_XSTRDUP <= EV_MAX).
{ unfold EV_SUP_POOL_CONFIG, EV_ARG_I, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in *. lia. }
assert (HLIVEX : blocks_bytes Sc + LIVE_XSTRDUP x <= LIVE_MAX).
{ unfold LIVE_SUP_POOL_CONFIG, LIVE_ARG_I, LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XSTRDUP in *. fold x t in HLIVE. lia. }
assert (HMOKX : mo_ok MT Sc (XM_XSTRDUP MT x)).
{ apply (mok_station MT S Sc (XM_SUP_POOL_CONFIG MT R name max) (rec_spill_frees R * mo_free MT) _ MTL HMOK HMLE XMX).
  unfold XM_SUP_POOL_CONFIG. fold x t. lia. }
assert (HRODT : arodata_okP SEGS RLO RHI B (rdW Wc (ms_mem ms))).
{ exact (spc_aro B MT HY _ _ O ly S W mem md _ _ _ _ _ _ _ HAR (spc_rep_in B ly S _ R O HREP) HJ HROD). }
assert (SX : SIG CS_xstrdup = BASE + AF_xstrdup).
{ rewrite (SIGP CS_xstrdup ltac:(unfold cmd_prog_syms; repeat (first [left; reflexivity | right]))). f_equal. }
rewrite SX.
eapply SRr_bind.
{ eapply (cl_callS B LAWS Wc (ms_regs ms) (ms_mem ms) _ SUP_POOL_CONFIG_STK sp0 (spc_FP O) ly S W mem md [] lyc Sc _
    (rec_spill_frees R) XSTRDUP_STK [] EV_XSTRDUP (-64) (getr (ms_regs ms) 1) []).
  - exact HJ.
  - unfold spZ. rewrite P2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - reflexivity.
  - lia.
  - unfold XSTRDUP_STK, ASTACK. lia.
  - rewrite spc_stk. unfold REC_CALLS_FREE_STK, XSTRDUP_STK, ARG_I_STK, REC_SHAPE_OF_STK, ANSWER_STK, MIX_CALL_STK,
      HAND_BACK_STK, ASTACK, ESTACK. lia.
  - exact P3'.
  - exact P4'.
  - reflexivity.
  - rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite P1, unsigned_lit_small by lia. lia.
  - unfold s0Z. rewrite P8. apply spc_achain_max; [exact Hmax | lia].
  - intros HPRE1. unfold cfg_at in *.
    exact (TXSTRDUP fx lyc Sc Wc (ms_regs ms) (ms_mem ms) _ [] s x HPRE1 HRODT P10 (or_introl HARGT) HTAILT HEVX HLIVEX HMOKX).
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
(* back at 0x8bdbc with p1 = xstrdup's copy of x *)
cbv beta. intros W2 c2 HW2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJx & HP & (p1 & X10 & Xp & Xperm & Xfr & Xblk & Xcopy & Xstr & Xbb & Xmle)).
pose proof HJx as (HAR2 & _ & _ & _ & _ & Xfrs & _ & _ & XK394 & XKB & XKI & _).
assert (E2u : bv_unsigned (ew E 2) = sp0 - 64) by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
assert (XKPG : forall a, Exists (in_zr a) recb_PG -> rdW W2 mem2 a = rdW Wc (ms_mem ms) a).
{ intros a HPG. destruct (spc_prog_unowned B HB a HPG) as [Hown Herr].
  apply XKI; [exact (cmd_prog_img a HPG) | exact Hown | exact Herr|].
  apply fp_spares_closed; [apply sink_closed_pos; constructor | exact (inFP_nil a)]. }
jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W2) mem2) HP [0; 1]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. constructor; [|constructor; [|constructor]]; split;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val spc_frame spc_slot_rg]; intros a Ha.
  - rewrite E2u in Ha. apply (mbyte_of_aview SEGS). apply XK394; [lia | lia | exact (inFP_nil a)].
  - lia.
  - first [rewrite B34 in Ha | rewrite B34u in Ha]. apply (mbyte_of_aview SEGS). apply XKPG. exact (spc_slot_PG c a Hc ltac:(unfold CALL_SIZE in *; lia)).
  - first [rewrite B34 in Ha | rewrite B34u in Ha]. intros _. apply (cmd_prog_writable ly2 S2 W2 mem2 md2 a HAR2).
    exact (spc_slot_PG c a Hc ltac:(unfold CALL_SIZE in *; lia)). }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
set (E2 := havoc E 48 (map (getr regs2) CLOB)) in *.
assert (HEI2 : img_env VAL A_LIM E2) by (apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall k, (k < 48)%nat -> ew E2 k = ew E k) by (intros k Hk; apply ew_havoc_old; exact Hk).
assert (SHOK2 : sh_ok SEGS SPC_Bx SPC_SH E2 (mrestrict (w_H W2) mem2)).
{ apply (spc_sh_ok B LAWS HB ly2 S2 W2 mem2 md2 E2 c HAR2); [rewrite OLD2 by lia; exact E32 | rewrite OLD2 by lia; exact E34 | exact Hc]. }
assert (B34' : base_val E2 (Some 34%nat) = c) by (cbn [base_val]; rewrite OLD2 by lia; exact B34).
rewrite P1.
paj_run_tok RUN HS HJ2 SHOK2 SPC_SPAN.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen; [reflexivity | exact B34' | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi spc_slot_rg] in Ha.
  exact (spc_awr_slot B HB cmd_prog_img _ _ _ _ _ _ _ _ c a Hc ltac:(unfold CALL_SIZE in *; lia)). }
pmkst HS. spc_md.
(* the run wrote only the slot *)
assert (K32 : forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + CALL_SIZE) -> rdW W2 (ms_mem ms0) a = rdW W2 mem2 a).
{ intros a Ha Hn. match goal with HFr : frame_of E2 _ _ _ |- _ => apply (recb_run_keeps_m E2 _ (w_H W2) mem2 (ms_mem ms0) a HFr Ha) end.
  intros Hw. apply Hn. exact (spc_wrange_slot E2 c _ a B34' Hw). }
(* xstrdup kept g_rec, record.spill and every block it did not make *)
assert (K21b : forall p n i, In (p, n) (ablocks B lyc Sc) -> 0 <= i < req_size n ->
  rdW W2 mem2 (p + i) = rdW Wc (ms_mem ms) (p + i)).
{ intros p n i Hin Hi. apply (XKB p n i); [exact Hin | apply (Permutation_in _ (Permutation_sym Xperm)); right; exact Hin | exact Hi | exact (inFP_nil _)]. }
(* 0x8bdf8: the call of arg_i on (c, max); the slot holds REC_POOL_CONFIG, nargs 1 and p1 *)
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
rewrite !OLD2 in Q2, Q3, Q4, Q8, Q10, Q11 by lia.
rewrite (EE 2%nat 2%bv eq_refl), R2 in Q2. rewrite (EE 3%nat 3%bv eq_refl) in Q3. rewrite (EE 4%nat 4%bv eq_refl) in Q4.
rewrite (EE 8%nat 8%bv eq_refl), R8 in Q8, Q11.
assert (Q10' : getr (ms_regs ms0) 10 = w64 c) by (rewrite Q10, E34; reflexivity).
assert (Q3' : getr (ms_regs ms0) 3 = w64 (as_gp B)) by (rewrite Q3; exact (eq_trans (RK 3 ltac:(cbn; tauto)) Hgp)).
assert (Q4' : getr (ms_regs ms0) 4 = w64 (as_tp B)) by (rewrite Q4; exact (eq_trans (RK 4 ltac:(cbn; tauto)) Htp)).
assert (E52 : ew E2 52 = getr regs2 10) by reflexivity.
assert (VNA : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms0)) (c + 4) 4 1).
{ exact (st_chunk_val SEGS E2 _ _ 1 _ 34 4 4 (SLit 1) c 1 HS eq_refl eq_refl ltac:(cbn; tauto) B34' eq_refl ltac:(cbn; lia) ltac:(cbn; lia)). }
assert (VFN : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms0)) (c + 0) 4 REC_POOL_CONFIG).
{ exact (st_chunk_val SEGS E2 _ _ 1 _ 34 0 4 (SLit REC_POOL_CONFIG) c REC_POOL_CONFIG HS eq_refl eq_refl ltac:(cbn; tauto) B34' eq_refl
    ltac:(unfold REC_POOL_CONFIG; cbn; lia) ltac:(cbn; lia)). }
assert (VA0 : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms0)) (c + 8) 8 p1).
{ assert (Hp1 : 0 <= p1 < 2 ^ 64).
  { destruct (al_blocks _ _ LAWS _ _ _ _ _ p1 (LIVE_XSTRDUP x) HAR2 ltac:(apply (Permutation_in _ (Permutation_sym Xperm)); left; reflexivity))
      as (_ & _ & Hce & _). pose proof asan_consts as (Ca & _). destruct (req_size_pos (LIVE_XSTRDUP x) ltac:(unfold LIVE_XSTRDUP; lia)). lia. }
  apply (st_chunk_val SEGS E2 _ _ 1 _ 34 8 8 (SOff 52 0) c p1 HS eq_refl eq_refl); [cbn; tauto | exact B34' | | cbn; lia | cbn; lia].
  cbn [sv_denot]. rewrite E52, X10, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
pose proof HJ2 as (HAR2' & Hly2 & _ & _ & _ & Hfr2 & Hnev2 & _).
assert (HRO2 : arodata_okP SEGS RLO RHI B (rdW W2 (ms_mem ms0)))
  by exact (spc_aro B MT HY _ _ O ly S W mem md _ _ _ _ _ _ _ HAR (spc_rep_in B ly S _ R O HREP) HJ2 HROD).
assert (HBB2 : blocks_bytes S2 = blocks_bytes Sc + LIVE_XSTRDUP x).
{ rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B lyc Sc), (bsum_perm _ _ Xperm), bsum_cons. cbn [snd]. lia. }
assert (HMLE2 : mo_le MT S S2 (rec_spill_frees R * mo_free MT + XM_XSTRDUP MT x))
  by exact (mle_station MT S Sc S2 _ _ MTL HMLE Xmle).
assert (HEVI : st_nev S2 + EV_ARG_I <= EV_MAX).
{ unfold EV_SUP_POOL_CONFIG, EV_ARG_I, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in *. lia. }
assert (HLIVEI : blocks_bytes S2 + LIVE_ARG_I max <= LIVE_MAX).
{ rewrite HBB2. unfold LIVE_SUP_POOL_CONFIG, LIVE_ARG_I, LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XSTRDUP in *. fold x t in HLIVE. lia. }
assert (HMOKI : mo_ok MT S2 (XM_ARG_I MT max)).
{ apply (mok_station MT S S2 (XM_SUP_POOL_CONFIG MT R name max) _ _ MTL HMOK HMLE2 XMI).
  unfold XM_SUP_POOL_CONFIG. fold x t. lia. }
assert (HFR2' : Z.of_nat (length (frames S2)) <= 8) by (rewrite Xfrs, app_nil_l, Hfrc, app_nil_l; exact HFR8).
assert (HSLOT : (exists i, 0 <= i < REC_CALLS_MAX /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ c = A_REC_SPILL).
{ unfold c, spc_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [L | L]; [left | right; reflexivity].
  exists (Z.of_nat (length (r_calls R))). unfold REC_CALLS_MAX. split; [lia | reflexivity]. }
(* the registers arg_i keeps, at its call *)
assert (HRA3 : getr (ms_regs ms0) 1 = Z_to_bv 64 (BASE + SPC_ARGI))
  by (rewrite Q1; change SPC_ARGI with 22808; reflexivity).
prreg HS (9%bv : bv 5) Q9. prreg HS (20%bv : bv 5) Q20.
assert (Q9' : getr (ms_regs ms0) 9 = w64 c) by (rewrite Q9, (OLD2 34%nat ltac:(lia)), E34; reflexivity).
assert (Q20' : getr (ms_regs ms0) 20 = w64 SB) by (rewrite Q20, (OLD2 32%nat ltac:(lia)), E32; reflexivity).
assert (QK : forall r, In r [3; 4; 22; 23; 24; 25; 26; 27] -> getr (ms_regs ms0) (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)).
{ intros r Hr. cbv [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [lazymatch goal with |- getr _ ?rr = _ => let P := fresh "P" in prreg HS rr P;
       rewrite P, OLD2 by lia; apply EE; reflexivity end|]).
  destruct Hr. }
assert (SA : SIG CS_arg_i = BASE + AF_arg_i).
{ rewrite (SIGP CS_arg_i ltac:(unfold cmd_prog_syms; repeat (first [left; reflexivity | right]))). f_equal. }
rewrite SA. unfold spc_goal.
eapply srr_after_callF.
{ eapply (cl_callS_wideF B LAWS W2 (ms_regs ms0) (ms_mem ms0) _ _ sp0 (spc_FP O) ly S W mem md [] ly2 S2 _ _
    ARG_I_STK _ EV_ARG_I (-64) (getr (ms_regs ms0) 1) []).
  - exact HJ2.
  - unfold spZ. rewrite Q2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - reflexivity.
  - lia.
  - unfold ARG_I_STK, XSTRDUP_STK, ASTACK, ESTACK. lia.
  - unfold ARG_I_STK, XSTRDUP_STK, ASTACK, ESTACK. lia.
  - exact Q3'.
  - exact Q4'.
  - reflexivity.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Q1, unsigned_lit_small by lia. lia.
  - unfold s0Z. rewrite Q8. apply spc_achain_max; [exact Hmax|].
    pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop2 & _). lia.
  - intros HPRE1. unfold cfg_at in *.
    exact (TARG_I fx ly2 S2 W2 (ms_regs ms0) (ms_mem ms0) _ [] c max 1 HPRE1 HFR0 HFR2' HRO2
      (cmd_ro_ok_of_aro ly2 S2 W2 (ms_mem ms0) _ HAR2' HRO2)
      Q10' Q11 Hmax HSLOT (aval_mem_view SEGS (w_H W2) (ms_mem ms0) (c + CALL_OFF_NARGS) 4 1 VNA) ltac:(unfold REC_ARGS_MAX; lia)
      HEVI HLIVEI HMOKI).
  - intros a Ha. cbn in Ha. apply (spc_awr_slot B HB cmd_prog_img _ _ _ _ _ _ _ _ c a Hc).
    destruct Ha as (r & [<- | [<- | []]] & Hr); cbn [fst snd] in Hr; unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE in *; lia.
  - intros ly3 S3 W3 regs3 mem3 md3 _ a Ha Hw _. exfalso.
    destruct Ha as (r & Hr & Hrr). cbn in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hrr;
    unfold CALL_OFF_NARGS, CALL_OFF_ARGS, A_REC_SPILL, A_G_REC, OFF_CALLS in *; lia. }
(* back at 0x8bdfc, at the FP state fx1 arg_i returned: nargs 2, args[1] = p2 holding dec max *)
intros fx1 ly3 S3 W3 regs3 mem3 md3 HW3 Hfx (HJ3 & HJi & HP3 & (Ibb & Imle & Ires)).
destruct Ires as [(Hm6 & _) | (_ & p2 & Ip & Iperm & Ifr & Ina & Iarg & Istr)]; [unfold REC_ARGS_MAX in Hm6; lia|].
pose proof HJi as (HAR3 & _ & _ & _ & _ & Ifrs & _ & _ & IK394 & IKB & IKI & _).
assert (IFPs : forall a, inFP (if 1 <? REC_ARGS_MAX
    then [(c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4); (c + CALL_OFF_ARGS + 8 * 1, c + CALL_OFF_ARGS + 8 * 1 + 8)] else []) a ->
  (c + 4 <= a < c + 8) \/ (c + 16 <= a < c + 24)).
{ intros a (r & Hr & Hrr). cbn in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hrr;
  unfold CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia. }
assert (K43g : forall a, Exists (in_zr a) recb_PG -> ~ (c + 4 <= a < c + 8) -> ~ (c + 16 <= a < c + 24) ->
  rdW W3 mem3 a = rdW W2 (ms_mem ms0) a).
{ intros a HPG Hn Hn'. destruct (spc_prog_unowned B HB a HPG) as [Hown Herr].
  apply IKI; [exact (cmd_prog_img a HPG) | exact Hown | exact Herr|].
  apply fp_spares_closed.
  - apply sink_closed_pos. try (match goal with |- context [if ?b then _ else _] => replace b with true by reflexivity end).
    repeat constructor; cbn [fst]; unfold CALL_OFF_NARGS, CALL_OFF_ARGS, A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia.
  - intros Hf. apply IFPs in Hf. lia. }
assert (K43b : forall p n i, In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n ->
  rdW W3 mem3 (p + i) = rdW W2 (ms_mem ms0) (p + i)).
{ intros p n i Hin Hi.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR2 Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
  apply (IKB p n i); [exact Hin | apply (Permutation_in _ (Permutation_sym Iperm)); right; exact Hin | exact Hi |].
  intros Hf. apply IFPs in Hf.
  destruct (spc_blk_off B cmd_prog_img ly2 S2 W2 mem2 md2 p n (p + i) HAR2 Hin ltac:(lia)) as [_ HnPG].
  apply HnPG. exact (spc_slot_PG c (p + i) Hc ltac:(unfold CALL_SIZE; lia)). }
set (n1 := LIVE_XSTRDUP x) in *.
set (n2 := Z.of_nat (length (dec max)) + 1) in *.
assert (Hin2 : forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly2 S2))
  by (intros bk Hbk; apply (Permutation_in _ (Permutation_sym Xperm)); right; exact Hbk).
assert (Hin3 : forall pn, In pn (ablocks B ly2 S2) -> In pn (ablocks B ly3 S3))
  by (intros bk Hbk; apply (Permutation_in _ (Permutation_sym Iperm)); right; exact Hbk).
assert (Hp1 : In (p1, n1) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Xperm)); left; reflexivity).
assert (Hp2 : In (p2, n2) (ablocks B ly3 S3)) by (apply (Permutation_in _ (Permutation_sym Iperm)); left; reflexivity).
(* the reader after arg_i against the readers the walk met *)
assert (K3G : forall a, Exists (in_zr a) recb_PG -> ~ (c <= a < c + CALL_SIZE) -> rdW W3 mem3 a = rdW Wc memc a).
{ intros a HPG Hn. pose proof (pa_img_range a (cmd_prog_img a HPG)) as Hr.
  rewrite K43g by (first [exact HPG | unfold CALL_SIZE in Hn; lia]). rewrite K32 by (first [lia | exact Hn]).
  rewrite XKPG by exact HPG. apply KS; [lia | exact Hn]. }
assert (K3blk : forall p n i, In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n ->
  rdW W3 mem3 (p + i) = rdW W2 mem2 (p + i)).
{ intros p n i Hin Hi.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR2 Hin) as (_ & H4096 & Hcp & _ & _ & _ & Hn0).
  pose proof asan_consts as (Ca & _).
  destruct (spc_blk_off B cmd_prog_img ly2 S2 W2 mem2 md2 p n (p + i) HAR2 Hin ltac:(lia)) as [_ HnPG].
  assert (Hns : ~ (c <= p + i < c + CALL_SIZE)) by (intros Hs; exact (HnPG (spc_slot_PG c _ Hc Hs))).
  rewrite (K43b p n i Hin Hi). apply K32; [lia | exact Hns]. }
assert (K3c : forall p n i, In (p, n) (ablocks B lyc Sc) -> 0 <= i < req_size n ->
  rdW W3 mem3 (p + i) = rdW Wc memc (p + i)).
{ intros p n i Hin Hi.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HARc Hin) as (_ & H4096 & Hcp & _ & _ & _ & Hn0).
  pose proof asan_consts as (Ca & _).
  destruct (spc_blk_off B cmd_prog_img lyc Sc Wc memc mdc p n (p + i) HARc Hin ltac:(lia)) as [_ HnPG].
  assert (Hns : ~ (c <= p + i < c + CALL_SIZE)) by (intros Hs; exact (HnPG (spc_slot_PG c _ Hc Hs))).
  rewrite (K3blk p n i (Hin2 _ Hin) Hi). rewrite (K21b p n i Hin Hi). apply KS; [lia | exact Hns]. }
assert (HO0s : forall bq, In bq O0 -> In bq (ablocks B lyc Sc)).
{ intros bq Hbq. apply (proj1 (HO0 bq)) in Hbq as [H1 H2]. apply (proj2 (HBL bq)). split; [exact (spc_rep_in B ly S _ R O HREP _ H1) | exact H2]. }
assert (HO0pos : forall bq, In bq O0 -> 0 < snd bq).
{ intros bq Hbq. apply (proj1 (HO0 bq)) in Hbq as [H1 _]. exact (proj1 (spc_rep_own B ly S _ R O HREP bq H1)). }
assert (Hlx : Z.of_nat (length x) + 1 <= LMAX + 1) by (destruct HSTRc as (_ & _ & Hn & _); exact Hn).
pose proof (dec_length max Hmax) as Hld.
assert (Hn1 : n1 = Z.of_nat (length x) + 1) by reflexivity.
assert (Hap : forall p n lo len, In (p, n) (ablocks B ly3 S3) -> 0x10000 <= lo -> lo + len <= 0x606000 -> iv_apart p n lo len).
{ intros p n lo len Hin Hlo Hhi. pose proof (blk_off_imgP B ly3 S3 W3 mem3 md3 p n HAR3 Hin) as Hoff. unfold off_img in Hoff.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR3 Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
  destruct (req_size_pos n ltac:(lia)). unfold iv_apart. lia. }
assert (P12 : p1 <> p2).
{ intros E12. pose proof (proj1 (Forall_forall _ _) Ifr _ Hp1) as Hap12. cbn [fst snd] in Hap12. unfold iv_apart in Hap12.
  unfold n1, n2, LIVE_XSTRDUP in *. lia. }
(* the recorder after arg_i: the call recorded with its two arguments *)
assert (HREP3 : rec_repA B ly3 S3 (rdW W3 mem3) (rec_record R REC_POOL_CONFIG [x; dec max]) (O0 ++ [(p1, n1); (p2, n2)])).
{ apply (spc_rep_final B lyB SBs ly3 S3 rdB (rdW W3 mem3) R O0 REC_POOL_CONFIG x (dec max) p1 n1 p2 n2 Hlen16 HREPB).
  - unfold REC_POOL_CONFIG, REC_FN_COUNT. lia.
  - intros bq Hbq. exact (Hin3 _ (Hin2 _ (HO0s _ Hbq))).
  - exact (Hin3 _ Hp1).
  - exact Hp2.
  - intros a Hr Hnc Hns. rewrite (K3G a ltac:(destruct Hr as [Hr | Hr]; [exact (recb_grec_in a Hr) | exact (recb_spill_in a Hr)]) Hns).
    exact (HKB a Hr Hnc Hns).
  - intros [pb nb] i Hbq Hi. cbn [fst snd] in *. pose proof (HO0pos _ Hbq) as Hnb. cbn [snd] in Hnb.
    destruct (req_size_pos nb ltac:(lia)) as [_ Hrq]. rewrite (K3c pb nb i (HO0s _ Hbq) ltac:(lia)). exact (HKO (pb, nb) i Hbq Hi).
  - intros L k Hk. rewrite K3G; [exact (HNC L k Hk) | apply recb_grec_in | ]; unfold A_G_REC, OFF_NCALLS, REC_SIZE, OFF_CALLS, CALL_SIZE in *; lia.
  - intros k Hk. fold c. rewrite K43g; [ | apply (spc_slot_PG c); [exact Hc | ] | | ]; unfold CALL_OFF_FN, CALL_SIZE in *; try lia.
    exact (aval_mem_view SEGS (w_H W2) (ms_mem ms0) (c + 0) 4 REC_POOL_CONFIG VFN k Hk).
  - intros k Hk. exact (Ina k Hk).
  - intros k Hk. fold c. rewrite K43g; [ | apply (spc_slot_PG c); [exact Hc | ] | | ]; unfold CALL_OFF_ARGS, CALL_SIZE in *; try lia.
    exact (aval_mem_view SEGS (w_H W2) (ms_mem ms0) (c + 8) 8 p1 VA0 k Hk).
  - intros k Hk. exact (Iarg k Hk).
  - destruct Xcopy as [Hb Hnz]. split; [|exact Hnz]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    destruct (req_size_pos n1 ltac:(lia)) as [_ Hrq].
    rewrite (K3blk p1 n1 (Z.of_nat i) Hp1 ltac:(lia)). exact (Hb i ltac:(rewrite length_app; cbn [length]; lia)).
  - exact Istr.
  - lia.
  - unfold LMAX. lia.
  - unfold n1, LIVE_XSTRDUP, LMAX in *. lia.
  - unfold n2, LMAX. lia.
  - lia.
  - lia.
  - exact P12.
  - apply Hap; [exact (Hin3 _ Hp1) | unfold A_G_REC; lia | unfold A_G_REC, REC_SIZE; lia].
  - apply Hap; [exact (Hin3 _ Hp1) | unfold A_REC_SPILL; lia | unfold A_REC_SPILL, SC_SIZE; lia].
  - apply Hap; [exact Hp2 | unfold A_G_REC; lia | unfold A_G_REC, REC_SIZE; lia].
  - apply Hap; [exact Hp2 | unfold A_REC_SPILL; lia | unfold A_REC_SPILL, SC_SIZE; lia].
  - intros Hm. apply in_map_iff in Hm as ([pb kb] & Eb & Hb). cbn [fst] in Eb. subst pb.
    pose proof (proj1 (Forall_forall _ _) Xfr _ (HO0s _ Hb)) as Hapx. cbn [fst snd] in Hapx. unfold iv_apart in Hapx.
    pose proof (HO0pos _ Hb) as Hkb. cbn [snd] in Hkb. unfold n1, LIVE_XSTRDUP in *. lia.
  - intros Hm. apply in_map_iff in Hm as ([pb kb] & Eb & Hb). cbn [fst] in Eb. subst pb.
    pose proof (proj1 (Forall_forall _ _) Ifr _ (Hin2 _ (HO0s _ Hb))) as Hapx. cbn [fst snd] in Hapx. unfold iv_apart in Hapx.
    pose proof (HO0pos _ Hb) as Hkb. cbn [snd] in Hkb. unfold n2 in *. lia. }
(* the blocks after arg_i: the entry's less F, and the two copies *)
assert (HA3 : forall bq, In bq (ablocks B ly3 S3) <-> (In bq (ablocks B ly S) /\ ~ In bq F) \/ bq = (p1, n1) \/ bq = (p2, n2)).
{ intros bq. split.
  - intros H. apply (Permutation_in _ Iperm) in H. destruct H as [<- | H]; [right; right; reflexivity|].
    apply (Permutation_in _ Xperm) in H. destruct H as [<- | H]; [right; left; reflexivity|].
    left. exact (proj1 (HBL _) H).
  - intros [H | [-> | ->]]; [exact (Hin3 _ (Hin2 _ (proj2 (HBL _) H))) | exact (Hin3 _ Hp1) | exact Hp2]. }
assert (Hb1 : ~ (In (p1, n1) (ablocks B ly S) /\ ~ In (p1, n1) F)).
{ intros H. pose proof (proj2 (HBL _) H) as Hc0. pose proof (proj1 (Forall_forall _ _) Xfr _ Hc0) as Hx. cbn [fst snd] in Hx.
  unfold iv_apart, n1, LIVE_XSTRDUP in *. lia. }
assert (Hb2 : ~ (In (p2, n2) (ablocks B ly S) /\ ~ In (p2, n2) F)).
{ intros H. pose proof (Hin2 _ (proj2 (HBL _) H)) as Hc0. pose proof (proj1 (Forall_forall _ _) Ifr _ Hc0) as Hx. cbn [fst snd] in Hx.
  unfold iv_apart, n2 in *. lia. }
assert (HBB3 : blocks_bytes S3 <= blocks_bytes S + n1 + n2).
{ unfold LIVE_ARG_I in Ibb. rewrite HBB2 in Ibb. unfold n1, n2, LIVE_XSTRDUP in *. lia. }
(* the saved registers in the frame, kept by xstrdup, the run and arg_i (their windows lie below the frame) *)
assert (HFRM3 : spc_frame_at (mrestrict (w_H W3) mem3) sp0 regs).
{ apply (spc_frame_kept (w_H Wc) (w_H W3) memc mem3 sp0 regs HFRM).
  intros a Ha.
  assert (E1 : rdW W3 mem3 a = rdW W2 (ms_mem ms0) a).
  { apply IK394; [lia | lia |]. intros Hf. apply IFPs in Hf. unfold A_REC_SPILL, A_G_REC, OFF_CALLS in *. lia. }
  rewrite E1, (K32 a ltac:(lia) ltac:(unfold CALL_SIZE, A_REC_SPILL in *; lia)).
  assert (Ex2 : rdW W2 mem2 a = rdW Wc (ms_mem ms) a) by (apply XK394; [lia | lia | exact (inFP_nil a)]).
  rewrite Ex2. exact (KS a ltac:(lia) ltac:(unfold CALL_SIZE, A_REC_SPILL in *; lia)). }
assert (HMI : spc_midI B MT ly S W regs mem md R O name max O0 F p1 p2 ly3 S3 W3 mem3 md3 regs3).
{ unfold spc_midI. cbv zeta.
  split; [exact HJ3|]. split; [exact HA3|]. split; [exact HFO|]. split; [exact HO0|]. split; [exact Hb1|]. split; [exact Hb2|].
  split; [exact P12|]. split; [exact HBB3|]. split; [exact (mle_station MT S S2 S3 _ _ MTL HMLE2 Imle)|].
  split; [rewrite Ifrs, app_nil_l; exact HFR2'|]. split; [exact HFRM3|]. split; [exact HREP3|].
  split; [exact (eq_trans (HP3 2 ltac:(unfold acallee_saved; lia)) Q2)|].
  split; [exact (eq_trans (HP3 8 ltac:(unfold acallee_saved; lia)) Q8)|].
  split; [exact (eq_trans (HP3 9 ltac:(unfold acallee_saved; lia)) Q9')|].
  split; [exact (eq_trans (HP3 20 ltac:(unfold acallee_saved; lia)) Q20')|].
  intros r Hr. rewrite <- (RK r Hr), <- (QK r Hr). apply HP3. cbv [In] in Hr. unfold acallee_saved. lia. }
rewrite HRA3.
exact (spc_seg_tail (fx := fx1) B MT HY ly S W regs mem md ch max name R O O0 F p1 p2 ly3 S3 W3 mem3 md3 regs3
  HFN (fxrel_frm0 fx fx1 HFR0 Hfx) HROD Hmax HREP HEV HLIVE HMOK HMI).
Qed.

End e.
End f.
End d.
