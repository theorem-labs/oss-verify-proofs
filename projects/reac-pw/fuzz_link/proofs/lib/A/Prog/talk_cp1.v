(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_up.v, with its module paths and module names changed; 311 of its 349 lines of code are new or changed and 2651 lines of the source are left out. *)
(* talk on image A: the piece TK_AT_CP1 of lib/A/Prog/talk_defs.v, the lemma tk_cp1_ok.
   - +0x12c: the call of checked_memcpy(m + 12 + 512 n, r, len), lifted by lib/A/Prog/talk_kit.v tk_intrin with the
     source premises of tk_src_req; after it the request's bytes sit in slot n of the model block;
   - +0x130 .. +0x154: the instrumented check of n_req, the store of n + 1 and the address of req_len[n];
   - +0x158 .. +0x168: the check of that address and the 8-byte store of len; then +0x16c, where TK_CL0 takes over
     with the model block as `owe` leaves it (talk_spec.v md_owe / mo_owe).
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk talk_c talk_defs talk_kit talk_spec talk_ret talk_chunk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis LV : LinkVals.
Hypothesis MEMCPY : aintrin_realizes SEGS B OCpy (pa_sigma LS___asan_memcpy).
Variable c : tkc.
Hypothesis HC : tk_call SK B c.
#[local] Notation W := (tc_W c).
#[local] Notation memc := (tc_memc c).
#[local] Notation regs0 := (tc_regs0 c).
#[local] Notation mbs := (tc_mbs c).
#[local] Notation kbs := (tc_kbs c).
#[local] Notation req := (tc_req c).

Ltac cp_in := repeat (first [left; reflexivity | right]).
Ltac cp_keep RK r K := pose proof (RK r ltac:(cp_in)) as K; cbn [ms_regs restrict] in K.
Ltac cp_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
  end.
Ltac cp_awr_m U :=
  lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end;
  apply awr_ok_x_cons;
  [ intros ?a ?Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U in Ha;
    apply (ck_ajw_m SK B c HC); unfold MD_REQ_LEN, MD_N_REQ, MD_SIZE in Ha |- *; lia
  | apply awr_ok_x_nil ].

(* the address of req_len[n] (+0x13c..+0x154) *)
Lemma cp_den_rl : forall E n, ew E 20 = w64 (tk_m c) -> ew E 49 = w64 n ->
  0 <= tk_m c -> tk_m c + MD_SIZE <= kHighMemEnd - 1 -> 0 <= n <= 15 ->
  sv_denot E (SAlu ALU_ADD (SOff 20 8208) (SAlu ALU_SLL (SOff 49 0) (SLit 3))) =
  w64 (tk_m c + MD_REQ_LEN + 8 * n).
Proof.
  intros E n E20 E49 Hm0 Hmhi Hn.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  rewrite denot_lit_U. unfold w64. f_equal.
  rewrite !U_SAlu. cbn [zalu_raw]. rewrite (ck_U0 E 49 n E49) by lia. rewrite !U_lit by lia.
  rewrite (ck_Uoff E 20 (tk_m c) 8208 E20) by (unfold MD_SIZE in *; lia).
  change (Z.land 3 63) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  unfold zcanon, M64, MD_REQ_LEN, MD_SIZE in *. rewrite !(Z.mod_small _ (2 ^ 64)); lia.
Qed.

Lemma tk_cp1_ok : TK_CL0 SK B c -> TK_AT_CP1 SK B c.
Proof.
intros HCL0 regs mem md HI HR0 HRN Hra R10 R11 R12 R20 R21 R22 R24 HM HB HMAIN Hnr Hbuf.
pose proof (ck_wf SK B c HC) as (HNW & HMW & HML & HKL & HRQ).
destruct (tk_m_facts SK B c HC) as (Hm0 & Hmhi & Hm2 & Hmg & Hmf & Hmra & Hmh & Hmbs).
destruct (tk_r_facts SK B c HC) as (Hr0 & Hrlen & Hramr & Hrhi & Hrf & Hrp & Hrra & Hrh & Hrq & Hrl).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof (tk_sp_rng SK B c HC) as (S0 & S1 & S2 & S3).
pose proof HI as (HJ & _ & _ & Hsp & _).
pose proof HR0 as (R8 & R9 & R23).
pose proof HRN as (N18 & N19).
pose proof HMW as (HNRB & _).
pose proof HMAIN as (HMS & HMD).
unfold NL_SENT_MAX in HNRB. unfold NL_SENT_LEN in Hrlen.
unfold apart in Hrp. unfold apart_frame, tk_sp in Hmf, Hrf.
(* ---- the call of checked_memcpy at +0x12c ---- *)
unfold tk_goal. eapply SRr_bind.
{ refine (tk_intrin SK B LAWS c HC OCpy (pa_sigma LS___asan_memcpy) MEMCPY regs mem md
    (tk_m c + MD_REQ + NL_SENT_LEN * md_n_req mbs) (tk_r c) (tk_len c)
    (Z_to_bv 64 (BASE + TP_C1)) HI R10 R11 R12 _ _ Hra
    (ret_ok_codeptr_v TP_C1 ltac:(unfold TP_C1, AF_talk; lia) ltac:(unfold TP_C1, AF_talk; reflexivity)) _).
  - unfold NL_SENT_LEN in *. lia.
  - left. unfold MD_REQ, NL_SENT_LEN, MD_SIZE in *. lia.
  - destruct (tk_src_req SK B c HC regs mem md HI Hsp Hbuf) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5).
    split; [exact Q0|]. split; [exact Q1|]. split; [exact Q2|].
    split; [unfold MD_REQ, NL_SENT_LEN, MD_SIZE in *; lia|].
    split; [exact Q3|]. split; [exact Q4 | exact Q5]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HI2 & HP2 & Hcp & Hout).
assert (KB : forall (rr : bv 5) z, rr = Z_to_bv 5 z -> acallee_saved z -> getr regs2 rr = getr regs rr)
  by (intros rr z -> Hz; exact (HP2 z Hz)).
assert (P2' : getr regs2 2 = getr regs 2) by (apply (KB 2%bv 2); [apply bv_eq; reflexivity | unfold acallee_saved; lia]).
assert (P3' : getr regs2 3 = getr regs 3) by (apply (KB 3%bv 3); [apply bv_eq; reflexivity | unfold acallee_saved; lia]).
assert (P4' : getr regs2 4 = getr regs 4) by (apply (KB 4%bv 4); [apply bv_eq; reflexivity | unfold acallee_saved; lia]).
assert (P8' : getr regs2 8 = getr regs 8) by (apply (KB 8%bv 8); [apply bv_eq; reflexivity | unfold acallee_saved; lia]).
assert (P9' : getr regs2 9 = getr regs 9) by (apply (KB 9%bv 9); [apply bv_eq; reflexivity | unfold acallee_saved; lia]).
assert (P18' : getr regs2 18 = getr regs 18) by (apply (KB 18%bv 18); [apply bv_eq; reflexivity | unfold acallee_saved; lia]).
assert (P19' : getr regs2 19 = getr regs 19) by (apply (KB 19%bv 19); [apply bv_eq; reflexivity | unfold acallee_saved; lia]).
assert (P20' : getr regs2 20 = getr regs 20) by (apply (KB 20%bv 20); [apply bv_eq; reflexivity | unfold acallee_saved; lia]).
assert (P21' : getr regs2 21 = getr regs 21) by (apply (KB 21%bv 21); [apply bv_eq; reflexivity | unfold acallee_saved; lia]).
assert (P22' : getr regs2 22 = getr regs 22) by (apply (KB 22%bv 22); [apply bv_eq; reflexivity | unfold acallee_saved; lia]).
assert (P23' : getr regs2 23 = getr regs 23) by (apply (KB 23%bv 23); [apply bv_eq; reflexivity | unfold acallee_saved; lia]).
assert (P24' : getr regs2 24 = getr regs 24) by (apply (KB 24%bv 24); [apply bv_eq; reflexivity | unfold acallee_saved; lia]).
pose proof HI2 as (_ & _ & _ & _ & _ & _ & _ & _ & PR2).
(* the request's bytes now sit in slot n of the model block *)
assert (HM2 : amodel_at SEGS (rdW W mem2) (tk_m c) (bput mbs (MD_REQ + NL_SENT_LEN * md_n_req mbs) req)).
{ apply (amodel_put SEGS (rdW W mem) (rdW W mem2) (tk_m c) mbs
    (MD_REQ + NL_SENT_LEN * md_n_req mbs) req HM);
    [ unfold MD_REQ, NL_SENT_LEN; lia | unfold MD_REQ, NL_SENT_LEN, MD_SIZE in *; lia | | | ].
  - intros i Hi Hni. apply (mbyte_of_aview SEGS (w_H W) (w_H W) mem mem2).
    apply Hout; [unfold MD_SIZE in *; lia | unfold MD_REQ, NL_SENT_LEN in *; lia
                | unfold tk_sp, TALK_AK, TALK_AFRAME, ESTACK, MD_SIZE in *; lia ].
  - intros k Hk.
    assert (Hk' : 0 <= Z.of_nat k < tk_len c) by lia.
    replace (tk_m c + (MD_REQ + NL_SENT_LEN * md_n_req mbs) + Z.of_nat k)
      with (tk_m c + MD_REQ + NL_SENT_LEN * md_n_req mbs + Z.of_nat k) by lia.
    rewrite (aview_mbyte_eq SEGS (w_H W) (w_H W) memc mem2 (tk_r c + Z.of_nat k)
      (tk_m c + MD_REQ + NL_SENT_LEN * md_n_req mbs + Z.of_nat k)
      ltac:(rewrite (Hcp (Z.of_nat k) Hk'); exact (Hbuf (Z.of_nat k) Hk'))).
    destruct Hrq as (_ & _ & Hb). exact (Hb k ltac:(lia)).
  - intros i Hi. apply (writable_kept (w_H W) memc mem2 (tk_m c + i) (PR2 (tk_m c + i))).
    exact (ck_mwr c memc mbs Hmbs i Hi). }
assert (HB2 : tk_bufs c mem2 no_attrs).
{ apply (ck_bufs_keep SK B c HC mem mem2 no_attrs HB).
  - intros a Ha Hoff Hwin. apply Hout;
      [ exact Ha | unfold MD_REQ, NL_SENT_LEN, MD_SIZE in *; lia
      | unfold tk_sp, TALK_AK, TALK_AFRAME, ESTACK in *; lia ].
  - intros a Hp. exact (PR2 a Hp). }
(* ---- +0x130: the store of n + 1 ---- *)
assert (R20'' : getr regs2 20 = w64 (tk_m c)) by (rewrite P20'; exact R20).
assert (R22'' : getr regs2 22 = w64 (tk_m c + MD_N_REQ)) by (rewrite P22'; exact R22).
assert (R23'' : getr regs2 23 = w64 SHADOW_OFF) by (rewrite P23'; exact R23).
assert (R24'' : getr regs2 24 = w64 (tk_shx (tk_m c + MD_N_REQ))) by (rewrite P24'; exact R24).
assert (E20 : ew (tk_E c regs2 [w64 (md_n_req mbs)]) 20 = w64 (tk_m c))
  by (rewrite (tk_E_reg c regs2 [w64 (md_n_req mbs)] 20 20%bv) by (lia || reflexivity); exact R20'').
assert (U20 : bv_unsigned (ew (tk_E c regs2 [w64 (md_n_req mbs)]) 20) = tk_m c)
  by (rewrite E20; apply ck_uw; unfold MD_SIZE in *; lia).
assert (E49 : ew (tk_E c regs2 [w64 (md_n_req mbs)]) 49 = w64 (md_n_req mbs))
  by exact (tk_E_xs c regs2 [w64 (md_n_req mbs)] 0%nat ltac:(lia)).
assert (Vnr : val_mem SEGS (rdW W mem2) (tk_m c + MD_N_REQ) 4 (md_n_req mbs)).
{ apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem2).
  - intros k Hk. cbn in Hk. apply Hout;
      [ unfold MD_N_REQ, MD_SIZE in *; lia | unfold MD_REQ, MD_N_REQ, NL_SENT_LEN in *; lia
      | unfold tk_sp, TALK_AK, TALK_AFRAME, ESTACK, MD_N_REQ, MD_SIZE in *; lia ].
  - pose proof (ck_mfield c mem mbs MD_N_REQ 4%nat HM ltac:(unfold MD_N_REQ; lia)
      ltac:(unfold MD_N_REQ, MD_SIZE; cbn; lia)) as HV.
    change (Z.of_nat 4) with 4 in HV. exact HV. }
pose proof (tk_E_env c regs2 [w64 (md_n_req mbs)]) as HEI.
assert (HS : st_ok_pi SEGS VAL (tk_E c regs2 [w64 (md_n_req mbs)]) tk_ss_c1
    (restrict (w_H W) (mkst regs2 (Z_to_bv 64 (BASE + TP_C1)) mem2 (seg_rom SEGS)))).
{ unfold tk_ss_c1. apply (tk_st_ok SK B LV c HC regs2 mem2 md2 [w64 (md_n_req mbs)] TP_C1).
  - exact HI2.
  - exact R23''.
  - exact (tk_ov_c1_ok SK B c HC regs2 [w64 (md_n_req mbs)] R20'' R22'' R24'' R23'').
  - vm_compute; reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold tk_ch, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U20. split; [unfold MD_N_REQ; lia|]. split; [unfold MD_N_REQ, MD_SIZE in *; lia|].
    split.
    { intros o Ho. apply (writable_kept (w_H W) memc mem2 (tk_m c + o) (PR2 (tk_m c + o))).
      apply (ck_mwr c memc mbs Hmbs). unfold MD_SIZE. lia. }
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ (tk_m c) 8336 4 (SOff 49 0) (md_n_req mbs));
      [ apply ck_den0; [exact E49 | lia] | ck_zrng | ck_zrng | exact Vnr ].
  - cbn [pairwise_disjoint all_disjoint]. repeat first [exact I | split].
  - refine (conj _ (conj _ I)); unfold afact_ok; cbn [af_lo af_hi af_al2].
    + rewrite U20, Z.pow_0_r, Z.mod_1_r. unfold MD_SIZE in *. lia.
    + rewrite E49, (ck_uw (md_n_req mbs)) by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia. }
assert (SHOK : sh_ok SEGS tk_Bx tk_SH_c1 (tk_E c regs2 [w64 (md_n_req mbs)]) (rdW W mem2))
  by exact (ck_sh_m SK B c HC regs2 mem2 md2 [w64 (md_n_req mbs)] HI2 R23'' R20'').
pose proof (paj_run_to_x SK B LAWS (tc_G c) (ck_HGX SK B c HC) (tc_XO c) (tc_OUT c)) as RUNTO.
pose proof HI2 as (HJ2 & _).
paj_run_to_tok RUNTO HS HJ2 SHOK tk_span TP_RL; [cp_awr_m U20|].
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms3 end.
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _
  (fun a => tk_m c + MD_N_REQ <= a < tk_m c + MD_N_REQ + 4) HFr
  ltac:(intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
        destruct Hin as [Hq | []]; injection Hq as <- <- <-;
        cbn [base_val] in Hrr; rewrite U20 in Hrr; cbv beta;
        unfold MD_N_REQ in *; clear - Hrr; lia)) as UN3.
pose proof (st_ok_region_nth (segs := SEGS) _ _ _ 0 _ HS eq_refl) as HR3.
assert (V3 : val_mem SEGS (rdW W (ms_mem ms3)) (tk_m c + MD_N_REQ) 4 (md_n_req mbs + 1)).
{ replace (tk_m c + MD_N_REQ) with (tk_m c + 8336) by (unfold MD_N_REQ; lia).
  eapply (field_of_region (segs := SEGS) _ _ _ _ _ _ _ _ _ _ 4%N);
    [ exact HR3 | exact U20 | cp_in | apply ck_denoff; [exact E49 | lia] | ck_zrng | ck_zrng ]. }
assert (HM3 : amodel_at SEGS (rdW W (ms_mem ms3)) (tk_m c)
    (bput (bput mbs (MD_REQ + NL_SENT_LEN * md_n_req mbs) req) MD_N_REQ (lev 4 (md_n_req mbs + 1)))).
{ apply (amodel_store SEGS (rdW W mem2) (rdW W (ms_mem ms3)) (tk_m c)
    (bput mbs (MD_REQ + NL_SENT_LEN * md_n_req mbs) req) MD_N_REQ 4%nat (md_n_req mbs + 1) HM2);
    [ unfold MD_N_REQ; lia | unfold MD_N_REQ, MD_SIZE; cbn; lia | | exact V3 | ].
  - intros i Hi Hni. apply (mbyte_of_aview SEGS (w_H W) (w_H W) mem2 (ms_mem ms3)).
    apply UN3; [unfold MD_SIZE in *; lia | cbv beta; unfold MD_N_REQ in *; lia].
  - intros i Hi. apply (writable_kept (w_H W) mem2 (ms_mem ms3) (tk_m c + i)
      (fun Hp => apresent_grows _ _ _ _ HG Hp)).
    apply (writable_kept (w_H W) memc mem2 (tk_m c + i) (PR2 (tk_m c + i))).
    exact (ck_mwr c memc mbs Hmbs i Hi). }
assert (HB3 : tk_bufs c (ms_mem ms3) no_attrs).
{ apply (ck_bufs_keep SK B c HC mem2 (ms_mem ms3) no_attrs HB2).
  - intros a Ha Hoff Hwin. apply UN3; [exact Ha | cbv beta; unfold MD_N_REQ, MD_SIZE in *; lia].
  - intros a Hp. exact (apresent_grows _ _ _ _ HG (PR2 a Hp)). }
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (MD3 := mdq) end.
assert (HI3 : tk_inv SK B c (ms_regs ms3) (ms_mem ms3) MD3).
{ apply (tk_inv_step SK B c HC regs2 mem2 md2 (ms_regs ms3) (ms_mem ms3) MD3
    (fun a => tk_m c + MD_N_REQ <= a < tk_m c + MD_N_REQ + 4) HI2 HJ2);
    [ unfold MD3; repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
    | unfold MD3; repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity
    | exact UN3
    | intros a Ha; right; apply ck_ewr_m; cbv beta in Ha; unfold MD_N_REQ, MD_SIZE in *; lia
    | intros a Hp; exact (apresent_grows _ _ _ _ HG Hp)
    | | | ].
  - pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 (tk_ext c ++ [w64 (md_n_req mbs)])
      [2%bv] HS (ck_agree c regs2 [w64 (md_n_req mbs)]) ltac:(vm_compute; reflexivity)) as RKa.
    cp_keep RKa (2%bv : bv 5) Ka. exact Ka.
  - pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 (tk_ext c ++ [w64 (md_n_req mbs)])
      [3%bv] HS (ck_agree c regs2 [w64 (md_n_req mbs)]) ltac:(vm_compute; reflexivity)) as RKb.
    cp_keep RKb (3%bv : bv 5) Kb. exact Kb.
  - pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 (tk_ext c ++ [w64 (md_n_req mbs)])
      [4%bv] HS (ck_agree c regs2 [w64 (md_n_req mbs)]) ltac:(vm_compute; reflexivity)) as RKc.
    cp_keep RKc (4%bv : bv 5) Kc. exact Kc. }
pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 (tk_ext c ++ [w64 (md_n_req mbs)])
  [8%bv;9%bv;18%bv;19%bv;20%bv;21%bv;23%bv] HS (ck_agree c regs2 [w64 (md_n_req mbs)])
  ltac:(vm_compute; reflexivity)) as RK.
cp_keep RK (8%bv : bv 5) K8. cp_keep RK (9%bv : bv 5) K9. cp_keep RK (18%bv : bv 5) K18.
cp_keep RK (19%bv : bv 5) K19. cp_keep RK (20%bv : bv 5) K20. cp_keep RK (21%bv : bv 5) K21.
cp_keep RK (23%bv : bv 5) K23.
cp_reg HS (10%bv : bv 5) Q10.
assert (R10' : getr (ms_regs ms3) 10 = w64 (tk_m c + MD_REQ_LEN + 8 * md_n_req mbs))
  by (rewrite Q10; apply (cp_den_rl _ (md_n_req mbs) E20 E49); lia).
assert (R23' : getr (ms_regs ms3) 23 = w64 SHADOW_OFF) by (rewrite K23; exact R23'').
assert (R21' : getr (ms_regs ms3) 21 = w64 (tk_len c)) by (rewrite K21, P21'; exact R21).
clear HF HFr HG UN3 HR3 HS SHOK HEI.
(* ---- +0x158: the 8-byte store of len ---- *)
assert (E10 : ew (tk_E c (ms_regs ms3) []) 10 = w64 (tk_m c + MD_REQ_LEN + 8 * md_n_req mbs))
  by (rewrite (tk_E_reg c (ms_regs ms3) [] 10 10%bv) by (lia || reflexivity); exact R10').
assert (U10 : bv_unsigned (ew (tk_E c (ms_regs ms3) []) 10) = tk_m c + MD_REQ_LEN + 8 * md_n_req mbs)
  by (rewrite E10; apply ck_uw; unfold MD_REQ_LEN, MD_SIZE in *; lia).
assert (E21 : ew (tk_E c (ms_regs ms3) []) 21 = w64 (tk_len c))
  by (rewrite (tk_E_reg c (ms_regs ms3) [] 21 21%bv) by (lia || reflexivity); exact R21').
pose proof (tk_E_env c (ms_regs ms3) []) as HEI.
assert (HS : st_ok_pi SEGS VAL (tk_E c (ms_regs ms3) []) tk_ss_rl
    (restrict (w_H W) (mkst (ms_regs ms3) (Z_to_bv 64 (BASE + TP_RL)) (ms_mem ms3) (seg_rom SEGS)))).
{ unfold tk_ss_rl. apply (tk_st_ok SK B LV c HC (ms_regs ms3) (ms_mem ms3) MD3 [] TP_RL).
  - exact HI3.
  - exact R23'.
  - apply Forall_nil.
  - vm_compute; reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U10. split; [unfold MD_REQ_LEN; lia|]. split; [unfold MD_REQ_LEN, MD_SIZE in *; lia|].
    split; [|apply Forall_nil].
    intros o Ho.
    replace (tk_m c + MD_REQ_LEN + 8 * md_n_req mbs + o)
      with (tk_m c + (MD_REQ_LEN + 8 * md_n_req mbs + o)) by lia.
    apply (writable_kept (w_H W) memc (ms_mem ms3) _
      (fun Hp => proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HI3))))))) _ Hp)).
    apply (ck_mwr c memc mbs Hmbs). unfold MD_REQ_LEN, MD_SIZE. lia.
  - cbn [pairwise_disjoint all_disjoint]. repeat first [exact I | split].
  - refine (conj _ I). unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U10, Z.pow_0_r, Z.mod_1_r. unfold MD_REQ_LEN, MD_SIZE in *. lia. }
assert (SHOK : sh_ok SEGS tk_Bx tk_SH_rl (tk_E c (ms_regs ms3) []) (rdW W (ms_mem ms3))).
{ unfold tk_SH_rl. apply Forall_cons; [|apply Forall_nil].
  apply (ck_shent SK B c HC (ms_regs ms3) (ms_mem ms3) MD3 [] 10%nat 10%bv
    (tk_m c + MD_REQ_LEN + 8 * md_n_req mbs) 8 HI3 ltac:(lia) ltac:(reflexivity) R23' R10');
    [ unfold MD_REQ_LEN; lia | lia | unfold MD_REQ_LEN, MD_SIZE in *; lia
    | unfold amem_range, kLowMemEnd, kHighMemBeg, MD_REQ_LEN, MD_SIZE in *;
      destruct Hm2 as [Hq|Hq]; [left|right]; lia
    | apply (range_addressable_sub _ _ (tk_m c) MD_SIZE);
      [ exact Hmra | unfold MD_REQ_LEN; lia | unfold MD_REQ_LEN, MD_SIZE; lia ] ]. }
pose proof HI3 as (HJ3 & _).
paj_run_to_tok RUNTO HS HJ3 SHOK tk_span TP_CL0; [cp_awr_m U10|].
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms4 end.
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _
  (fun a => tk_m c + MD_REQ_LEN + 8 * md_n_req mbs <= a < tk_m c + MD_REQ_LEN + 8 * md_n_req mbs + 8) HFr
  ltac:(intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
        destruct Hin as [Hq | []]; injection Hq as <- <- <-;
        cbn [base_val] in Hrr; rewrite U10 in Hrr; cbv beta; clear - Hrr; lia)) as UN4.
pose proof (st_ok_region_nth (segs := SEGS) _ _ _ 0 _ HS eq_refl) as HR4.
assert (V4 : val_mem SEGS (rdW W (ms_mem ms4)) (tk_m c + MD_REQ_LEN + 8 * md_n_req mbs) 8 (tk_len c)).
{ replace (tk_m c + MD_REQ_LEN + 8 * md_n_req mbs)
    with (tk_m c + MD_REQ_LEN + 8 * md_n_req mbs + 0) by lia.
  eapply (field_of_region (segs := SEGS) _ _ _ _ _ _ _ _ _ _ 8%N);
    [ exact HR4 | exact U10 | cp_in | apply ck_den0; [exact E21 | lia] | ck_zrng | ck_zrng ]. }
assert (HM4 : amodel_at SEGS (rdW W (ms_mem ms4)) (tk_m c) (md_owe mbs req)).
{ rewrite (md_owe_lt mbs req ltac:(unfold NL_SENT_MAX; lia)).
  rewrite Hrl.
  apply (amodel_store SEGS (rdW W (ms_mem ms3)) (rdW W (ms_mem ms4)) (tk_m c)
    (bput (bput mbs (MD_REQ + NL_SENT_LEN * md_n_req mbs) req) MD_N_REQ (lev 4 (md_n_req mbs + 1)))
    (MD_REQ_LEN + 8 * md_n_req mbs) 8%nat (tk_len c) HM3);
    [ unfold MD_REQ_LEN; lia | unfold MD_REQ_LEN, MD_SIZE; cbn; lia | | | ].
  - intros i Hi Hni. apply (mbyte_of_aview SEGS (w_H W) (w_H W) (ms_mem ms3) (ms_mem ms4)).
    apply UN4; [unfold MD_SIZE in *; lia | cbv beta; unfold MD_REQ_LEN in *; lia].
  - replace (tk_m c + (MD_REQ_LEN + 8 * md_n_req mbs))
      with (tk_m c + MD_REQ_LEN + 8 * md_n_req mbs) by lia. exact V4.
  - intros i Hi. apply (writable_kept (w_H W) (ms_mem ms3) (ms_mem ms4) (tk_m c + i)
      (fun Hp => apresent_grows _ _ _ _ HG Hp)).
    apply (writable_kept (w_H W) memc (ms_mem ms3) (tk_m c + i)
      (fun Hp => proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HI3))))))) _ Hp)).
    exact (ck_mwr c memc mbs Hmbs i Hi). }
assert (HB4 : tk_bufs c (ms_mem ms4) no_attrs).
{ apply (ck_bufs_keep SK B c HC (ms_mem ms3) (ms_mem ms4) no_attrs HB3).
  - intros a Ha Hoff Hwin. apply UN4; [exact Ha | cbv beta; unfold MD_REQ_LEN, MD_SIZE in *; lia].
  - intros a Hp. pose proof HI3 as (_ & _ & _ & _ & _ & _ & _ & _ & PR3).
    exact (apresent_grows _ _ _ _ HG (PR3 a Hp)). }
pmkst HS.
pose proof (regs_kept_of_st_ok_pi _ _ _ (ms_regs ms3) (tk_ext c ++ [])
  [2%bv;3%bv;4%bv;8%bv;9%bv;18%bv;19%bv;20%bv;23%bv] HS (ck_agree c (ms_regs ms3) [])
  ltac:(vm_compute; reflexivity)) as RK4.
cp_keep RK4 (2%bv : bv 5) L2. cp_keep RK4 (3%bv : bv 5) L3. cp_keep RK4 (4%bv : bv 5) L4.
cp_keep RK4 (8%bv : bv 5) L8. cp_keep RK4 (9%bv : bv 5) L9. cp_keep RK4 (18%bv : bv 5) L18.
cp_keep RK4 (19%bv : bv 5) L19. cp_keep RK4 (20%bv : bv 5) L20. cp_keep RK4 (23%bv : bv 5) L23.
destruct (mo_owe mbs req HML HMW ltac:(lia) HMS HMD) as (HOL & HON & HOW).
apply HCL0.
- lazymatch goal with |- tk_inv _ _ _ _ _ ?mdq => set (MD4 := mdq) end.
  apply (tk_inv_step SK B c HC (ms_regs ms3) (ms_mem ms3) MD3 (ms_regs ms4) (ms_mem ms4) MD4
    (fun a => tk_m c + MD_REQ_LEN + 8 * md_n_req mbs <= a
              < tk_m c + MD_REQ_LEN + 8 * md_n_req mbs + 8) HI3 HJ3);
    [ unfold MD4; repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
    | unfold MD4; repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity
    | exact UN4
    | intros a Ha; right; apply ck_ewr_m; cbv beta in Ha; unfold MD_REQ_LEN, MD_SIZE in *; lia
    | intros a Hp; exact (apresent_grows _ _ _ _ HG Hp)
    | exact L2 | exact L3 | exact L4 ].
- split; [rewrite L8, K8, P8'; exact R8|].
  split; [rewrite L9, K9, P9'; exact R9 | rewrite L23; exact R23'].
- split; [rewrite L18, K18, P18'; exact N18 | rewrite L19, K19, P19'; exact N19].
- rewrite L20, K20, P20'; exact R20.
- exists (md_owe mbs req). split; [exact HM4|]. split; [exact HOW | exact HON].
- exact HB4.
- exact HMAIN.
Qed.

End w.

