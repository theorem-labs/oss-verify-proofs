(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/W_LLVMFuzzerTestOneInput_top_x.v, with its module paths and module names changed; 446 of its 683 lines of code are new or changed and 990 lines of the source are left out. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
ReplyCnt W_LLVMFuzzerTestOneInput_drain_defs_x W_LLVMFuzzerTestOneInput_drain_calls TopxEntry
W_img_x W_gesture_end W_gestures_end_top AsmTopX CfRBridgeRulesB TopX_RT_lock.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyB3TrPeakCnl.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_send_line_x TopX_RT4 W_errno_azs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require RTx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_cut W_LLVMFuzzerTestOneInput_cut_x W_LLVMFuzzerTestOneInput_G.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD2l YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcallcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_head_x ReplyLSB ReplyRINVB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcallx YG01cf YG05cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_frame W_frame_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0tcf YG0dcf YG08cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
W_op_add W_LLVMFuzzerTestOneInput_pro W_LLVMFuzzerTestOneInput_pro_x W_LLVMFuzzerTestOneInput_latch_x
W_bx_defs W_LLVMFuzzerTestOneInput_exit_x W_bx_inst W_bx_inst_x YCk0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_sites_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_drain_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_small_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
W_LLVMFuzzerTestOneInput_add W_LLVMFuzzerTestOneInput_add_x W_LLVMFuzzerTestOneInput_write W_LLVMFuzzerTestOneInput_write_x
W_list_push.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
W_LLVMFuzzerTestOneInput_remove W_LLVMFuzzerTestOneInput_remove_x W_LLVMFuzzerTestOneInput_arm_event
W_LLVMFuzzerTestOneInput_event_x TopxImageB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
W_LLVMFuzzerTestOneInput_gone_x W_LLVMFuzzerTestOneInput_gone_base W_LLVMFuzzerTestOneInput_gone_base_x
W_LLVMFuzzerTestOneInput_gone_inst.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0scf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Spec Require PresetRoom.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
ReplyLS3B_inst ReplyB3Base ReplyB3LSCntL ReplyB3LS3 ReplyB3LS3c ReplyB3LS3p ReplyLSBo ReplyLSBArms ReplyLSBoRf ReplyB3LS3o
ReplyB3LS3e ReplyB3LS3Arms ReplyB3LS3w ReplyB3LScap ReplyB3LS3Peak ReplyB3LS3cTopxPost ReplyBLSrm YCfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyKfMeterB ReplyLSBSec ReplyBTopLsi.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Local Notation G := (G_fr_c TfibB).
Local Notation RINV := ReplyRINVB.fr_RINV.
Local Notation MTs nsec KMAX := (ReplyKfMeterB.MT_sec nsec KMAX).
Local Notation LSc := (ReplyLS3B_inst.LSI TfibB ReplyLSBo.OUT_MAX4 ReplyB3LScap.fr_CAP).
Local Notation CAPSs nsec KMAX KC :=
  (fun cx t m ly S => ReplyB3LScap.fr_CAP cx t m ly S /\ ReplyLSBSec.fr_SEC nsec KMAX KC cx t m ly S).
Local Notation LSs nsec KMAX KC := (ReplyLS3B_inst.LSI TfibB ReplyLSBo.OUT_MAX4 (CAPSs nsec KMAX KC)).

Lemma btlsec_split : forall (rc : YM05.RunCeil) (nsec : astate -> Z) (KMAX KC : Z) cx t m ly S,
  LSs nsec KMAX KC cx t m ly S -> LSc cx t m ly S /\ ReplyLSBSec.fr_SEC nsec KMAX KC cx t m ly S.
Proof.
  intros rc nsec KMAX KC cx t m ly S (HP & HO & HE & HC & HS). exact (conj (conj HP (conj HO (conj HE HC))) HS).
Qed.

Lemma btlsec_join : forall (rc : YM05.RunCeil) (nsec : astate -> Z) (KMAX KC : Z) cx t m ly S,
  LSc cx t m ly S -> ReplyLSBSec.fr_SEC nsec KMAX KC cx t m ly S -> LSs nsec KMAX KC cx t m ly S.
Proof.
  intros rc nsec KMAX KC cx t m ly S (HP & HO & HE & HC) HS. exact (conj HP (conj HO (conj HE (conj HC HS)))).
Qed.

Lemma btlsec_parts : forall (rc : YM05.RunCeil) (nsec : astate -> Z) (KMAX KC : Z) cx t m ly S,
  LSs nsec KMAX KC cx t m ly S ->
  ReplyB3LS3c.fr_LS3c TfibB YCfn_cf.CALL_ROOM_B cx t m ly S /\ ReplyB3LS3.fr_LS3 TfibB YCfn_cf.CALL_ROOM_B cx t m ly S /\
  ReplyLSBo.fr_OUT ReplyLSBo.OUT_MAX4 cx t m ly S /\ ReplyB3LS3e.fr_ENT TfibB cx m ly S /\
  ReplyLSBSec.fr_SEC nsec KMAX KC cx t m ly S.
Proof.
  intros rc nsec KMAX KC cx t m ly S H.
  destruct (ReplyLS3B_inst.lsi_parts _ _ _ cx t m ly S H) as (_ & H3c & H3 & HO & HE & _ & HS).
  exact (conj H3c (conj H3 (conj HO (conj HE HS)))).
Qed.

Lemma btlsi_LS_head_nout_sec : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (nsec : astate -> Z) (KMAX KC : Z),
  240 <= KC ->
  forall cx t m ly S, LSs nsec KMAX KC cx t m ly S -> LSs nsec KMAX KC cx t (W_LLVMFuzzerTestOneInput_head.lm_clear_O m) ly S.
Proof.
  intros rc fx nsec KMAX KC HKC cx t m ly S H.
  destruct (btlsec_split rc nsec KMAX KC cx t m ly S H) as [HC HS].
  exact (btlsec_join rc nsec KMAX KC _ _ _ _ _ (ReplyBTopLsi.btlsi_LS_head_nout_cap rc fx cx t m ly S HC)
    (ReplyLSBSec.fr_SEC_head_nout TfibB nsec KMAX KC HKC cx t m ly S HS)).
Qed.

Lemma btlsi_LS_head_skip_sec : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (nsec : astate -> Z) (KMAX KC : Z),
  240 <= KC ->
  forall cx t m ly S, 0 <= t < OPS_MAX -> 0 <= lm_k m < c_n cx -> lm_O m = [] ->
  picks (in_byte cx (lm_k m) mod 10) = true -> in_byte cx (lm_k m) mod 10 <> 1 ->
  pick (lm_hs m) (W_LLVMFuzzerTestOneInput_head.hd_kb cx m) = None -> LSs nsec KMAX KC cx t m ly S -> LSs nsec KMAX KC cx (t + 1) (W_LLVMFuzzerTestOneInput_head.lm_set_k m (W_LLVMFuzzerTestOneInput_head.hd_k' cx m)) ly S.
Proof.
  intros rc fx nsec KMAX KC HKC cx t m ly S Ht Hk HO0 Hpk H1 Hn H.
  destruct (btlsec_split rc nsec KMAX KC cx t m ly S H) as [HC HS].
  exact (btlsec_join rc nsec KMAX KC _ _ _ _ _
    (ReplyBTopLsi.btlsi_LS_head_skip_cap rc fx cx t m ly S Ht Hk HO0 Hpk H1 Hn HC)
    (ReplyLSBSec.fr_SEC_head_skip TfibB nsec KMAX KC HKC cx t m ly S HS)).
Qed.

Lemma btlsi_LS_pro_oa_sec : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (nsec : astate -> Z) (KMAX KC : Z),
  240 <= KC ->
  forall (XM_LIB : Z -> Z), (forall n, ReplyLSBSec.SEC_CALL KC <= XM_LIB n) ->
  forall (RLO RHI : Z) (LIBROOM NP : astate -> Prop)
    (ARX : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop),
  forall cx Hp (S2 : astate) pos,
  lf_base_x TfibB (MTs nsec KMAX) XM_LIB RLO RHI YCfn_cf.fr_live_pre_b LIBROOM NP G ARX cx Hp ->
  ablocks TfibB (c_ly cx) S2 = ablocks TfibB (c_ly cx) (c_S cx) -> frames S2 = [(1, pos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) ->
  mo_le (MTs nsec KMAX) (c_S cx) S2 0 ->
  blocks_bytes S2 + APARTIAL + ATABLE <= LIVE_MAX /\ mo_ok (MTs nsec KMAX) S2 (W_op_add.oa_cost (MTs nsec KMAX)).
Proof.
  intros rc fx nsec KMAX KC HKC XM_LIB HXM RLO RHI LIBROOM NP ARX cx Hp S2 pos HB Hb2 Hf2 Hn2 Hbb2 Hm0.
  split.
  - exact (ReplyLSBArms.LS_pro_oa_B (MT := MTs nsec KMAX) TfibB XM_LIB RLO RHI LIBROOM NP G ARX cx Hp S2 pos HB Hb2 Hf2
      Hn2 Hbb2).
  - exact (ReplyLSBSec.sec_LS_pro_oa TfibB nsec KMAX KC HKC XM_LIB HXM RLO RHI YCfn_cf.fr_live_pre_b LIBROOM NP G ARX
      cx Hp S2 pos HB Hb2 Hf2 Hn2 Hbb2 Hm0).
Qed.

Lemma btlsi_LS_pro_sec : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (nsec : astate -> Z) (KMAX KC : Z),
  240 <= KC ->
  forall (XM_LIB : Z -> Z), (forall n, ReplyLSBSec.SEC_CALL KC <= XM_LIB n) ->
  forall (RLO RHI : Z) (LIBROOM NP : astate -> Prop)
    (ARX : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop),
  forall cx Hp q T' pj c O cap out (S2 : astate) pos ly S,
  lf_base_x TfibB (MTs nsec KMAX) XM_LIB RLO RHI YCfn_cf.fr_live_pre_b LIBROOM NP G ARX cx Hp ->
  (exists c0 mx0, aout_at TfibB fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c0 O mx0 (Z.of_nat (length O)) cap out) ->
  ct_cl c = 3 -> ct_br c = 0 -> ct_dd c = 0 -> ct_ei c = 0 ->
  ablocks TfibB (c_ly cx) S2 = ablocks TfibB (c_ly cx) (c_S cx) -> frames S2 = [(1, pos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) -> mo_le (MTs nsec KMAX) (c_S cx) S2 0 ->
  mo_le (MTs nsec KMAX) S2 S (W_op_add.oa_cost (MTs nsec KMAX)) ->
  (exists T0 rest0, Permutation (ablocks TfibB (c_ly cx) (c_S cx))
       (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest0) /\
     ReplyCnt.xcnt_ok TfibB (c_S cx) (c_ly cx) (input_blks cx) T0 cap out /\
     fr_hblks (c_W cx) (c_mem cx) = (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out /\
     ((T0 = 0 /\ Permutation (ablocks TfibB ly S) ((T', ATABLE) :: (q, APARTIAL) :: ablocks TfibB (c_ly cx) (c_S cx))) \/
      (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks TfibB ly S) ((q, APARTIAL) :: ablocks TfibB (c_ly cx) (c_S cx))))) ->
  LSs nsec KMAX KC cx 0 (W_LLVMFuzzerTestOneInput_pro.pro_m q T' pj c O cap out) ly S.
Proof.
  intros rc fx nsec KMAX KC HKC XM_LIB HXM RLO RHI LIBROOM NP ARX cx Hp q T' pj c O cap out S2 pos ly S HB Hout Hc1 Hc2
    Hc3 Hc4 Hb2 Hf2 Hn2 Hbb2 Hm0 Hmo HX.
  apply btlsec_join.
  - exact (ReplyBTopLsi.btlsi_LS_pro_cap rc fx (MTs nsec KMAX) XM_LIB RLO RHI LIBROOM NP ARX cx Hp q T' pj c O cap out
      S2 pos ly S HB Hout Hc1 Hc2 Hc3 Hc4 Hb2 Hf2 Hn2 Hbb2 Hm0 Hmo HX).
  - exact (ReplyLSBSec.fr_SEC_pro TfibB nsec KMAX KC HKC XM_LIB HXM RLO RHI YCfn_cf.fr_live_pre_b LIBROOM NP G ARX
      cx Hp q T' pj c O cap out S2 pos ly S HB Hm0 Hmo).
Qed.

Lemma btlsi_LS_rf_room_sec : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (nsec : astate -> Z) (KMAX KC : Z),
  240 <= KC ->
  forall cx t m ly S,
  LSs nsec KMAX KC cx t m ly S -> 0 <= t <= OPS_MAX ->
  W_bx_defs.lx_rf_room CfParamsReply.fr_MMAX (blocks_bytes S) (lm_c m) [] (lm_mx m) 0 (lm_cap m)
    (lm_es m).
Proof.
  intros rc fx nsec KMAX KC HKC. exact (ReplyBTopLsi.btlsi_LS_rf_room rc fx (CAPSs nsec KMAX KC)).
Qed.

Lemma btlsi_LS_exit_budget_sec : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (nsec : astate -> Z) (KMAX KC : Z),
  240 <= KC ->
  forall cx t m ly S, LSs nsec KMAX KC cx t m ly S ->
  0 <= t <= OPS_MAX ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m) ->
  mo_ok (MTs nsec KMAX) S (W_bx_defs.lx_exit_cost (MTs nsec KMAX) m).
Proof.
  intros rc fx nsec KMAX KC HKC cx t m ly S H Ht Hk.
  destruct (btlsec_parts rc nsec KMAX KC cx t m ly S H) as (_ & H3 & HO & _ & HS).
  exact (ReplyLSBSec.sec_LS_exit_budget TfibB nsec KMAX KC HKC ReplyLSBo.OUT_MAX4 cx t m ly S H3 HO HS Ht Hk).
Qed.

Lemma btlsi_LS_exit_end_sec {SK : YI16.sink_head} :
  forall (rc : YM05.RunCeil) (fx : YK11.FPState) (nsec : astate -> Z) (KMAX KC : Z),
  240 <= KC -> (forall f s, nsec (set_fs f s) = nsec s) ->
  forall (XN_LIB : Z -> Z), (forall n, ReplyLSBSec.SEC_CALL KC <= XN_LIB n) ->
  forall (fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z))
    (ARX : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop),
  forall cx t m ly3 S3 rest ly' S' (W' : world segs) mem' md' fpos k' C cap out,
  LSs nsec KMAX KC cx t m ly3 S3 ->
  Permutation (ablocks TfibB ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks TfibB ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  frames S' = [(1, fpos)] -> mo_le (MTs nsec KMAX) S3 S' C -> C <= W_bx_defs.lx_exit_cost (MTs nsec KMAX) m ->
  ajournal_gx_x segs TfibB [] ARX G 0 [] YCfn.LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly' (stack_free_state 1 fpos S') [] W' mem' md' k' ->
  cap = gse_cap (W_bx_defs.lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) ->
  0 <= t <= OPS_MAX ->
  fr_hblks W' mem' = (lm_G m, ATABLE) :: aout_blks cap out ->
  List.NoDup (ablocks TfibB ly' S') ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m) ->
  YCfn_cf.fr_live_post_b (c_S cx) (stack_free_state 1 fpos S') k' /\
  YCfn_cf.fr_surv_b TfibB (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem' /\
  mo_le (MTs nsec KMAX) (c_S cx) (stack_free_state 1 fpos S') (XN_LIB (c_n cx)).
Proof.
  intros rc fx nsec KMAX KC HKC HNSF XN_LIB HXN fr_FP ARX cx t m ly3 S3 rest ly' S' W' mem' md' fpos k' C cap out H HP3
    HP' Hfr Hmo HC0 HJ Hcap Ht HFH HND Hk.
  destruct (btlsec_parts rc nsec KMAX KC cx t m ly3 S3 H) as (H3c & H3 & HO & HE & HS).
  assert (X : ReplyB3LS3e.fr_live_post3_e ReplyLSBo.OUT_MAX4 (c_S cx) (stack_free_state 1 fpos S') k' /\
              ReplyB3LS3e.fr_surv_e TfibB (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem')
    by (eapply ReplyB3LS3e.LS_exit_end3e; first [eassumption | apply Z.le_refl]).
  destruct X as [X1 X2].
  split; [exact X1 | split; [exact X2 |]].
  exact (ReplyLSBSec.sec_LS_exit_end TfibB nsec KMAX KC HKC XN_LIB HXN HNSF ReplyLSBo.OUT_MAX4 fr_FP ARX G
    cx t m ly3 S3 rest ly' S' W' mem' md' fpos k' C cap out H3 HO HS HP3 HP' Hfr Hmo HC0 HJ Hcap Ht HFH HND Hk).
Qed.

Lemma btlsi_LS_exit_cnt_sec : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (nsec : astate -> Z) (KMAX KC : Z),
  240 <= KC ->
  forall cx t m ly3 S3 rest (ly' : alayout) (S' : astate) cap out,
  LSs nsec KMAX KC cx t m ly3 S3 ->
  Permutation (ablocks TfibB ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks TfibB ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  (forall p n, In (p, n) (ablocks TfibB ly' S') -> 4096 <= p) ->
  ReplyCnt.xcnt_ok TfibB S' ly' (input_blks cx) (lm_G m) cap out.
Proof.
  intros rc fx nsec KMAX KC HKC. exact (ReplyBTopLsi.btlsi_LS_exit_cnt rc fx (CAPSs nsec KMAX KC)).
Qed.

Lemma btlsi_LS_exit_cap_sec : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (nsec : astate -> Z) (KMAX KC : Z),
  240 <= KC ->
  forall cx t m ly S,
  LSs nsec KMAX KC cx t m ly S -> RINV cx t m -> 0 <= t <= OPS_MAX ->
  gse_cap (W_bx_defs.lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) <= CAPOUT_MAX.
Proof.
  intros rc fx nsec KMAX KC HKC.
  exact (ReplyBTopLsi.btlsi_LS_exit_cap rc fx (CAPSs nsec KMAX KC) (fun cx t m ly S HC => proj1 HC)).
Qed.

Lemma btlsi_LS_drain_pre_sec : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (nsec : astate -> Z) (KMAX KC : Z),
  240 <= KC ->
  forall cx t m ly S si h j,
  LSs nsec KMAX KC cx t m ly S -> RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
  hl_cap (hs_expected h) < 2 ^ 26 /\
  re_nheld (nth j (lm_es m) dr_e0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
  tr_max (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) < CfParamsReply.fr_MMAX /\
  blocks_bytes S +
    tr_peak (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)
    <= LIVE_MAX /\
  mo_ok (MTs nsec KMAX) S (dr_cost (MTs nsec KMAX) (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h).
Proof.
  intros rc fx nsec KMAX KC HKC cx t m ly S si h j H HRI Hat Hpick Hj Hfd Heof Ht HU HXP.
  destruct (btlsec_parts rc nsec KMAX KC cx t m ly S H) as (_ & H3 & _ & _ & HS).
  destruct (ReplyB3LS3Peak.pk_drain_pre TfibB YCfn_cf.CALL_ROOM_B (Z.le_refl _) cx t m ly S si h j H3 HRI Hat Hpick Hj
              Hfd Heof Ht HU HXP) as (C1 & C2 & C3 & C4 & C5).
  exact (conj C1 (conj C2 (conj C3 (conj C4 (conj C5
    (ReplyLSBSec.sec_LS_drain_pre TfibB nsec KMAX KC HKC cx t m ly S si h j H3 HS HRI Hat Hpick Hj Hfd Heof Ht HU)))))).
Qed.

Lemma btlsi_LS_cnl_pre_sec : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (nsec : astate -> Z) (KMAX KC : Z),
  240 <= KC ->
  forall cx t m ly S (ly' : alayout) (S' : astate) si h j h'' e' cap' out',
  LSs nsec KMAX KC cx t m ly S -> RINV cx t m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  mo_le (MTs nsec KMAX) S S' (dr_cost (MTs nsec KMAX) (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                   (nth j (lm_es m) dr_e0) h) ->
  hl_cap (hs_expected h'') = drain_b_c.ds_ecap
    (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  map snd (hl_recs (hs_expected h'')) =
    map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) ->
  hs_held h'' = hs_held h ->
  0 <= t < OPS_MAX -> lm_O m = [] ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_epre (nth j (lm_es m) dr_e0) -> W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_hpre h -> 0 <= lm_cap m ->
  (exists rest,
     Permutation (ablocks TfibB ly S)
       (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks TfibB ly' S') (aentry_blks e' ++ asrc_blks h'' ++ aout_blks cap' out' ++ rest)) ->
  cap' = (if dr_live (lm_c m) h
          then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                   (nth j (lm_es m) dr_e0) h)
          else lm_cap m) ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_epost (nth j (lm_es m) dr_e0) e' h -> W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_hpost h h'' ->
  NoDup (texts (hs_held h'')) /\ hl_n (hs_expected h'') < 2 ^ 26 /\
  hl_n (hs_held h'') + Z.of_nat (count_begin (texts (hs_expected h''))) < 2 ^ 22 /\
  cnl_room CfParamsReply.fr_MMAX (blocks_bytes S') (texts (hs_held h'')) (hl_cap (hs_held h'')) (hl_recs (hs_expected h'')) /\
  mo_ok (MTs nsec KMAX) S' (cnl_cost (MTs nsec KMAX) (hs_expected h'') (hs_held h'')) /\
  W_rep.AREC * capb (hs_held h'') (hs_expected h'') < 2 ^ 32.
Proof.
  intros rc fx nsec KMAX KC HKC cx t m ly S ly' S' si h j h'' e' cap' out' H HRI Hpick Hj Hfd Heof Hmo Hec Hmap Hheld
    Ht HO0 Hep Hhp Hc0 HPm Hcap' Hepo Hhpo.
  destruct (btlsec_parts rc nsec KMAX KC cx t m ly S H) as (_ & H3 & _ & _ & HS).
  destruct (ReplyB3LS3Arms.fr_LS3_cnl_pre_p TfibB YCfn_cf.CALL_ROOM_B (Z.le_refl _) cx t m ly S ly' S' si h j h'' e' cap'
              out' H3 HRI Hpick Hj Hfd Heof Hmo Hec Hmap Hheld Ht HO0 Hep Hhp Hc0 HPm Hcap' Hepo Hhpo)
    as (C1 & C2 & C3 & C4 & C6).
  exact (conj C1 (conj C2 (conj C3 (conj C4 (conj
    (ReplyLSBSec.sec_LS_cnl_pre TfibB nsec KMAX KC HKC cx t m ly S ly' S' si h j h'' e' cap' out' HS HRI Hpick Hj Hfd
       Heof Hmo Hmap Hheld Ht HO0 Hep) C6))))).
Qed.

Lemma btlsi_LS_drain_skip_sec : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (nsec : astate -> Z) (KMAX KC : Z),
  240 <= KC ->
  forall cx t m ly S,
  LSs nsec KMAX KC cx t m ly S -> LSs nsec KMAX KC cx (t + 1) (dr_skip m (dr_k' cx m)) ly S.
Proof.
  intros rc fx nsec KMAX KC HKC cx t m ly S H.
  destruct (btlsec_split rc nsec KMAX KC cx t m ly S H) as [HC HS].
  exact (btlsec_join rc nsec KMAX KC _ _ _ _ _ (ReplyBTopLsi.btlsi_LS_drain_skip_cap rc fx cx t m ly S HC)
    (ReplyLSBSec.fr_SEC_drain_skip TfibB nsec KMAX KC HKC cx t m ly S HS)).
Qed.

Lemma btlsi_LS_drain_step_sec : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (nsec : astate -> Z) (KMAX KC : Z),
  240 <= KC ->
  forall cx t m ly S (S1 : astate) (ly' : alayout) (S' : astate)
    si h j h'' e' c' O' cap' out' (E H : hlist) (ly1 : alayout) (h1 : hsrc) (E' H' : hlist),
  LSs nsec KMAX KC cx t m ly S -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  mo_le (MTs nsec KMAX) S S1
    (dr_cost (MTs nsec KMAX) (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  mo_le (MTs nsec KMAX) S1 S' (cnl_cost (MTs nsec KMAX) E H) ->
  (exists rest,
     Permutation (ablocks TfibB ly S)
       (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks TfibB ly1 S1) (aentry_blks e' ++ asrc_blks h1 ++ aout_blks cap' out' ++ rest)) ->
  hl_recs (hs_pending h1) = [] ->
  E = hs_expected h1 -> H = hs_held h1 ->
  (forall rest, Permutation (ablocks TfibB ly1 S1) (list_blks E ++ list_blks H ++ rest) ->
     Permutation (ablocks TfibB ly' S') (list_blks E' ++ list_blks H' ++ rest)) ->
  h'' = set_exp_held h1 E' H' ->
  dr_at_op cx m -> RINV cx t m -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_epre (nth j (lm_es m) dr_e0) -> W_LLVMFuzzerTestOneInput_drain_defs_x.ls3_kh (nth j (lm_es m) dr_e0) ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_hpre h -> W_LLVMFuzzerTestOneInput_drain_defs_x.ls3_hn h -> 0 <= lm_cap m ->
  cap' = (if dr_live (lm_c m) h
          then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                   (nth j (lm_es m) dr_e0) h)
          else lm_cap m) ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_epost (nth j (lm_es m) dr_e0) e' h -> W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_hpost h h1 ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.ls3_dpost m j h e' h1 -> W_LLVMFuzzerTestOneInput_drain_defs_x.ls3_cpost h1 E' H' ->
  0 <= t < OPS_MAX ->
  LSs nsec KMAX KC cx (t + 1) (dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') ly' S'.
Proof.
  intros rc fx nsec KMAX KC HKC cx t m ly S S1 ly' S' si h j h'' e' c' O' cap' out' E H ly1 h1 E' H' HL Hpick Hj
    M1 M2 HF1 Hp1 EE EH HF2 Eh Hat HRI Hfd Heof Hep Hkh Hhp Hhn Hc0 Hcap' Hepo Hhpo Hdp Hcp Ht.
  destruct (btlsec_parts rc nsec KMAX KC cx t m ly S HL) as (_ & H3 & _ & _ & HS).
  destruct (btlsec_split rc nsec KMAX KC cx t m ly S HL) as [HC _].
  exact (btlsec_join rc nsec KMAX KC _ _ _ _ _
    (ReplyBTopLsi.btlsi_LS_drain_step_cap rc fx (MTs nsec KMAX) cx t m ly S S1 ly' S' si h j h'' e' c' O' cap' out' E H
       ly1 h1 E' H' HC Hpick Hj M1 M2 HF1 Hp1 EE EH HF2 Eh Hat HRI Hfd Heof Hep Hkh Hhp Hhn Hc0 Hcap' Hepo Hhpo Hdp Hcp Ht)
    (ReplyLSBSec.fr_SEC_drain_step TfibB nsec KMAX KC HKC cx t m ly S S1 ly' S' si h j h'' e' c' O' cap' out' E H ly1
       h1 E' H' H3 HS Hpick Hj M1 M2 Hp1 EE EH Eh Hat HRI Hfd Heof Hep Hdp Ht)).
Qed.

Lemma btlsi_LS_close_sec : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (nsec : astate -> Z) (KMAX KC : Z),
  240 <= KC ->
  forall cx t m i ly S, LSs nsec KMAX KC cx t m ly S ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  LSs nsec KMAX KC cx (t + 1) (W_LLVMFuzzerTestOneInput_small.sm_close cx m i) ly S.
Proof.
  intros rc fx nsec KMAX KC HKC cx t m i ly S H Hpk.
  destruct (btlsec_split rc nsec KMAX KC cx t m ly S H) as [HC HS].
  exact (btlsec_join rc nsec KMAX KC _ _ _ _ _ (ReplyBTopLsi.btlsi_LS_close_cap rc fx cx t m i ly S HC Hpk)
    (ReplyLSBSec.fr_SEC_close TfibB nsec KMAX KC HKC cx t m i ly S HS)).
Qed.

Lemma btlsi_LS_eintr_sec : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (nsec : astate -> Z) (KMAX KC : Z),
  240 <= KC ->
  forall cx t m i ly S, LSs nsec KMAX KC cx t m ly S ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  LSs nsec KMAX KC cx (t + 1) (W_LLVMFuzzerTestOneInput_small.sm_eintr cx m i) ly S.
Proof.
  intros rc fx nsec KMAX KC HKC cx t m i ly S H Hpk.
  destruct (btlsec_split rc nsec KMAX KC cx t m ly S H) as [HC HS].
  exact (btlsec_join rc nsec KMAX KC _ _ _ _ _ (ReplyBTopLsi.btlsi_LS_eintr_cap rc fx cx t m i ly S HC Hpk)
    (ReplyLSBSec.fr_SEC_eintr TfibB nsec KMAX KC HKC cx t m i ly S HS)).
Qed.

Lemma btlsi_LS_sendmax_sec : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (nsec : astate -> Z) (KMAX KC : Z),
  240 <= KC ->
  forall cx t m ly S, LSs nsec KMAX KC cx t m ly S ->
  LSs nsec KMAX KC cx (t + 1) (W_LLVMFuzzerTestOneInput_small.sm_sendmax cx m (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0)) ly S.
Proof.
  intros rc fx nsec KMAX KC HKC cx t m ly S H.
  destruct (btlsec_split rc nsec KMAX KC cx t m ly S H) as [HC HS].
  exact (btlsec_join rc nsec KMAX KC _ _ _ _ _ (ReplyBTopLsi.btlsi_LS_sendmax_cap rc fx cx t m ly S HC)
    (ReplyLSBSec.fr_SEC_sendmax TfibB nsec KMAX KC HKC cx t m ly S HS)).
Qed.

Lemma btlsi_LS_default_sec : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (nsec : astate -> Z) (KMAX KC : Z),
  240 <= KC ->
  forall cx t m ly S, LSs nsec KMAX KC cx t m ly S -> LSs nsec KMAX KC cx (t + 1) (W_LLVMFuzzerTestOneInput_small.sm_default cx m (W_LLVMFuzzerTestOneInput_small.sm_dg cx m)) ly S.
Proof.
  intros rc fx nsec KMAX KC HKC cx t m ly S H.
  destruct (btlsec_split rc nsec KMAX KC cx t m ly S H) as [HC HS].
  exact (btlsec_join rc nsec KMAX KC _ _ _ _ _ (ReplyBTopLsi.btlsi_LS_default_cap rc fx cx t m ly S HC)
    (ReplyLSBSec.fr_SEC_default TfibB nsec KMAX KC HKC cx t m ly S HS)).
Qed.

Lemma btlsi_LS_add_room_sec : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (nsec : astate -> Z) (KMAX KC : Z),
  240 <= KC ->
  forall cx t m ly S,
  LSs nsec KMAX KC cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_add.ad_at_op cx m ->
  blocks_bytes S + APARTIAL + ATABLE <= LIVE_MAX /\ mo_ok (MTs nsec KMAX) S (W_op_add.oa_cost (MTs nsec KMAX)).
Proof.
  intros rc fx nsec KMAX KC HKC cx t m ly S H HRI Hat.
  destruct (btlsec_parts rc nsec KMAX KC cx t m ly S H) as (_ & H3 & _ & _ & HS).
  exact (conj (ReplyB3LS3.fr_LS3_add_room TfibB YCfn_cf.CALL_ROOM_B (Z.le_refl _) cx t m ly S H3)
    (ReplyLSBSec.sec_LS_add_room TfibB nsec KMAX KC HKC cx t m ly S HS)).
Qed.

Lemma btlsi_LS_add_open_sec : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (nsec : astate -> Z) (KMAX KC : Z),
  240 <= KC ->
  forall cx t m i q pj ev ly S (ly' : alayout) (S' : astate),
  LSs nsec KMAX KC cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_add.ad_at_op cx m -> W_op_add.oa_first (W_LLVMFuzzerTestOneInput_add.ad_os (lm_hs m)) = Some i ->
  mo_le (MTs nsec KMAX) S S' (W_op_add.oa_cost (MTs nsec KMAX)) -> Permutation (ablocks TfibB ly' S') ((q, APARTIAL) :: ablocks TfibB ly S) ->
  LSs nsec KMAX KC cx (t + 1) (W_LLVMFuzzerTestOneInput_add.ad_open m i q pj ev) ly' S'.
Proof.
  intros rc fx nsec KMAX KC HKC cx t m i q pj ev ly S ly' S' H HRI Hat Hf Hmo HPm.
  destruct (btlsec_split rc nsec KMAX KC cx t m ly S H) as [HC HS].
  exact (btlsec_join rc nsec KMAX KC _ _ _ _ _
    (ReplyBTopLsi.btlsi_LS_add_open_cap rc fx (MTs nsec KMAX) cx t m i q pj ev ly S ly' S' HC HRI Hat Hf Hmo HPm)
    (ReplyLSBSec.fr_SEC_add_open TfibB nsec KMAX KC HKC cx t m i q pj ev ly S ly' S' HS HRI Hf Hmo)).
Qed.

Lemma btlsi_LS_add_none_sec : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (nsec : astate -> Z) (KMAX KC : Z),
  240 <= KC ->
  forall cx t m ly S,
  LSs nsec KMAX KC cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_add.ad_at_op cx m -> W_op_add.oa_first (W_LLVMFuzzerTestOneInput_add.ad_os (lm_hs m)) = None ->
  LSs nsec KMAX KC cx (t + 1) (W_LLVMFuzzerTestOneInput_add.ad_none m) ly S.
Proof.
  intros rc fx nsec KMAX KC HKC cx t m ly S H HRI Hat Hf.
  destruct (btlsec_split rc nsec KMAX KC cx t m ly S H) as [HC HS].
  exact (btlsec_join rc nsec KMAX KC _ _ _ _ _ (ReplyBTopLsi.btlsi_LS_add_none_cap rc fx cx t m ly S HC HRI Hat Hf)
    (ReplyLSBSec.fr_SEC_add_none TfibB nsec KMAX KC HKC cx t m ly S HS)).
Qed.

Lemma btlsi_LS_write_skip_sec : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (nsec : astate -> Z) (KMAX KC : Z),
  240 <= KC ->
  forall cx t m ly S,
  LSs nsec KMAX KC cx t m ly S -> LSs nsec KMAX KC cx (t + 1) (W_LLVMFuzzerTestOneInput_write.wr_skip m (W_LLVMFuzzerTestOneInput_write.wr_k2 cx m)) ly S.
Proof.
  intros rc fx nsec KMAX KC HKC cx t m ly S H.
  destruct (btlsec_split rc nsec KMAX KC cx t m ly S H) as [HC HS].
  exact (btlsec_join rc nsec KMAX KC _ _ _ _ _ (ReplyBTopLsi.btlsi_LS_write_skip_cap rc fx cx t m ly S HC)
    (ReplyLSBSec.fr_SEC_write_skip TfibB nsec KMAX KC HKC cx t m ly S HS)).
Qed.

Lemma btlsi_LS_write_room_sec : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (nsec : astate -> Z) (KMAX KC : Z),
  240 <= KC ->
  forall cx t m si h ly S,
  LSs nsec KMAX KC cx t m ly S -> W_LLVMFuzzerTestOneInput_write.wr_pick cx m si h -> 0 < W_LLVMFuzzerTestOneInput_write.wr_n cx m ->
  (W_contract.lp_grow (hs_pending h) = true -> W_contract.lp_vbytes (hs_pending h) < W_LLVMFuzzerTestOneInput_write.WR_MMAX) /\
  blocks_bytes S + (if W_contract.lp_grow (hs_pending h) then W_contract.lp_vbytes (hs_pending h) else 0) + (W_LLVMFuzzerTestOneInput_write.wr_n cx m + 1) <= LIVE_MAX /\
  mo_ok (MTs nsec KMAX) S (W_contract.lp_cost (MTs nsec KMAX) (hs_pending h) (W_LLVMFuzzerTestOneInput_write.wr_n cx m)).
Proof.
  intros rc fx nsec KMAX KC HKC cx t m si h ly S H Hpk Hn.
  destruct (btlsec_parts rc nsec KMAX KC cx t m ly S H) as (_ & H3 & _ & _ & HS).
  destruct (ReplyB3LS3.fr_LS3_write_room TfibB YCfn_cf.CALL_ROOM_B (Z.le_refl _) cx t m si h ly S H3 Hpk Hn) as (C1 & C2).
  exact (conj C1 (conj C2 (ReplyLSBSec.sec_LS_write_room TfibB nsec KMAX KC HKC cx t m si h ly S HS))).
Qed.

Lemma btlsi_LS_write_push_sec : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (nsec : astate -> Z) (KMAX KC : Z),
  240 <= KC ->
  forall cx t m si h (l' : hlist) d ev ly S ly' S',
  LSs nsec KMAX KC cx t m ly S -> W_LLVMFuzzerTestOneInput_write.wr_pick cx m si h -> 0 < W_LLVMFuzzerTestOneInput_write.wr_n cx m ->
  hl_recs l' = hl_recs (hs_pending h) ++ [(d, W_LLVMFuzzerTestOneInput_write.wr_x cx m)] ->
  hl_cap l' = ListRep.grow_cap (hl_n (hs_pending h)) (hl_cap (hs_pending h)) ->
  (W_contract.lp_grow (hs_pending h) = false -> HarnessRep.hl_v l' = HarnessRep.hl_v (hs_pending h)) ->
  (forall rest, Permutation (ablocks TfibB ly S)
       ((if W_contract.lp_grow (hs_pending h) && negb (hl_cap (hs_pending h) =? 0)
         then [(HarnessRep.hl_v (hs_pending h), W_rep.AREC * hl_cap (hs_pending h))] else []) ++ rest) ->
     Permutation (ablocks TfibB ly' S')
       ((d, Z.of_nat (length (W_LLVMFuzzerTestOneInput_write.wr_x cx m)) + 1) ::
        (if W_contract.lp_grow (hs_pending h) then [(HarnessRep.hl_v l', W_rep.AREC * hl_cap l')] else []) ++ rest)) ->
  mo_le (MTs nsec KMAX) S S' (W_contract.lp_cost (MTs nsec KMAX) (hs_pending h) (W_LLVMFuzzerTestOneInput_write.wr_n cx m)) ->
  0 <= t < OPS_MAX ->
  LSs nsec KMAX KC cx (t + 1) (W_LLVMFuzzerTestOneInput_write.wr_push m (W_LLVMFuzzerTestOneInput_write.wr_k2 cx m) si (W_LLVMFuzzerTestOneInput_write.set_pending h l') ev) ly' S'.
Proof.
  intros rc fx nsec KMAX KC HKC cx t m si h l' d ev ly S ly' S' H Hpk Hn Hr Hc Hv HPm Hmo Ht.
  destruct (btlsec_split rc nsec KMAX KC cx t m ly S H) as [HC HS].
  exact (btlsec_join rc nsec KMAX KC _ _ _ _ _
    (ReplyBTopLsi.btlsi_LS_write_push_cap rc fx (MTs nsec KMAX) cx t m si h l' d ev ly S ly' S' HC Hpk Hn Hr Hc Hv HPm
       Hmo Ht)
    (ReplyLSBSec.fr_SEC_write_push TfibB nsec KMAX KC HKC cx t m si h l' d ev ly S ly' S' HS Hpk Hn Hr Hmo Ht)).
Qed.

Lemma btlsi_LS_rm_rr_pre_sec : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (nsec : astate -> Z) (KMAX KC : Z),
  240 <= KC ->
  forall cx t m ly S si h j0,
  LSs nsec KMAX KC cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  (exists c, val_mem segs (arm (c_W cx) (c_mem cx)) (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX) ->
  (re_eof (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) = 0 ->
     Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\ hl_cap (hs_expected h) < 2 ^ 26 /\
     re_nheld (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26) /\
  tr_max (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) < CfParamsReply.fr_MMAX /\ blocks_bytes S + tr_peak (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) <= LIVE_MAX /\
  mo_ok (MTs nsec KMAX) S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost (MTs nsec KMAX)) m h) /\ lm_cap m < CfParamsReply.fr_MMAX /\
  blocks_bytes S + tr_peak (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) + 4 * Z.max (lm_cap m) (tr_max (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h)) <= LIVE_MAX.
Proof.
  intros rc fx nsec KMAX KC HKC cx t m ly S si h j0 H HRI Hat Ht HU Hpos Hsrc HCAP0.
  destruct (btlsec_parts rc nsec KMAX KC cx t m ly S H) as (_ & _ & _ & _ & HS).
  destruct (ReplyB3LS3Peak.pk_lsi_rm_rr_pre_m TfibB
              (CAPSs nsec KMAX KC)
              cx t m ly S si h j0 H HRI Hat Ht HU Hpos Hsrc HCAP0) as (C1 & C2 & C3 & C5 & C6).
  exact (conj C1 (conj C2 (conj C3 (conj
    (ReplyLSBSec.sec_LS_rm_rr_pre TfibB nsec KMAX KC HKC cx t m ly S si h j0 HS HRI Hat Ht HU) (conj C5 C6))))).
Qed.

Lemma btlsi_LS_rm_cnl_pre_sec : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (nsec : astate -> Z) (KMAX KC : Z),
  240 <= KC ->
  forall cx t m ly0 S0 (S : astate) si h j0 e1 h1 ev LB c2 O2 cap2 (ly : alayout) out2,
  LSs nsec KMAX KC cx t m ly0 S0 -> RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  mo_le (MTs nsec KMAX) S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost (MTs nsec KMAX)) m h) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall rest, Permutation (ablocks TfibB ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks TfibB ly S) (input_blks cx ++ model_blks (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si (Some h1) j0 c2 O2 cap2 out2) ++ rest)) ->
  cnl_room CfParamsReply.fr_MMAX (blocks_bytes S) (texts (hs_held h1)) (hl_cap (hs_held h1)) (hl_recs (hs_expected h1)) /\
  mo_ok (MTs nsec KMAX) S ((W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost (MTs nsec KMAX)) (hs_expected h1) (hs_held h1)).
Proof.
  intros rc fx nsec KMAX KC HKC cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2 ly out2 H HRI Hat Hrr Ht HU Hmo Hpos HF.
  destruct (btlsec_parts rc nsec KMAX KC cx t m ly0 S0 H) as (_ & H3 & _ & _ & HS).
  exact (conj
    (ReplyB3LS3Arms.fr_LS3_rm_cnl_pre_p TfibB YCfn_cf.CALL_ROOM_B (Z.le_refl _) cx t m ly0 S0 ly S si h j0 e1 h1 ev LB c2
       O2 cap2 out2 H3 HRI Hat Hrr Hmo Hpos HF)
    (ReplyLSBSec.sec_LS_rm_cnl_pre TfibB nsec KMAX KC HKC cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2 ly out2 HS HRI
       Hat Hrr Ht HU Hmo)).
Qed.

Lemma btlsi_LS_rm_cshe_pre_sec : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (nsec : astate -> Z) (KMAX KC : Z),
  240 <= KC ->
  forall cx t m ly0 S0 (S : astate) si h j0 e1 h1 ev LB c2 O2 cap2 E' H',
  LSs nsec KMAX KC cx t m ly0 S0 -> RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' ->
  mo_le (MTs nsec KMAX) S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost (MTs nsec KMAX)) m h + (W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost (MTs nsec KMAX)) (hs_expected h1) (hs_held h1)) ->
  mo_ok (MTs nsec KMAX) S ((W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost (MTs nsec KMAX)) H').
Proof.
  intros rc fx nsec KMAX KC HKC cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H HRI Hat Hrr Ht HU Hcnl Hmo.
  destruct (btlsec_parts rc nsec KMAX KC cx t m ly0 S0 H) as (_ & _ & _ & _ & HS).
  exact (ReplyLSBSec.sec_LS_rm_cshe_pre TfibB nsec KMAX KC HKC cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2 E' H' HS HRI
    Hat Hrr Ht HU Hmo).
Qed.

Lemma btlsi_LS_rm_sr_pre_sec : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (nsec : astate -> Z) (KMAX KC : Z),
  240 <= KC ->
  forall cx t m ly0 S0 (S : astate) si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H'' ds cc,
  LSs nsec KMAX KC cx t m ly0 S0 -> RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' -> W_LLVMFuzzerTestOneInput_remove.rm_cshe_ok m (set_exp_held h1 E' H') O2 (W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1) H'' ds cc ->
  mo_le (MTs nsec KMAX) S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost (MTs nsec KMAX)) m h + (W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost (MTs nsec KMAX)) (hs_expected h1) (hs_held h1) + (W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost (MTs nsec KMAX)) H') ->
  mo_ok (MTs nsec KMAX) S (sr_cost (MTs nsec KMAX) (Some (set_held (set_exp_held h1 E' H') H''))).
Proof.
  intros rc fx nsec KMAX KC HKC cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H'' ds cc H HRI Hat Hrr Ht HU Hcnl
    Hcshe Hmo.
  destruct (btlsec_parts rc nsec KMAX KC cx t m ly0 S0 H) as (_ & _ & _ & _ & HS).
  exact (ReplyLSBSec.sec_LS_rm_sr_pre TfibB nsec KMAX KC HKC cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H'' ds
    cc HS HRI Hat Hrr Ht HU Hmo).
Qed.

Lemma btlsi_LS_rm_step_sec : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (nsec : astate -> Z) (KMAX KC : Z),
  240 <= KC ->
  forall cx t m ly0 S0 (ly : alayout) (S : astate)
    si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5,
  LSs nsec KMAX KC cx t m ly0 S0 ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  mo_le (MTs nsec KMAX) S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost (MTs nsec KMAX)) m h + (W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost (MTs nsec KMAX)) (hs_expected h1) (hs_held h1) + (W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost (MTs nsec KMAX)) H' +
                 sr_cost (MTs nsec KMAX) (Some (set_held (set_exp_held h1 E' H') H''))) ->
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 ->
  W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' ->
  W_LLVMFuzzerTestOneInput_remove.rm_cshe_ok m (set_exp_held h1 E' H') O2 (W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1) H'' ds cc ->
  (forall rest, Permutation (ablocks TfibB ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks TfibB ly S)
       (input_blks cx ++ model_blks (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si None j0 (W_LLVMFuzzerTestOneInput_remove.rm_cev c2 ev5) O2 cap2 out2) ++ rest)) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0)) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  0 <= t < OPS_MAX ->
  LSs nsec KMAX KC cx (t + 1) (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si None j0 (W_LLVMFuzzerTestOneInput_remove.rm_cev c2 ev5) O2 cap2 out2) ly S.
Proof.
  intros rc fx nsec KMAX KC HKC cx t m ly0 S0 ly S si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5 HL HU Hmo HRI
    Hat Hrr Hcnl Hcshe HF Hpos Hkeys Hpend Ht.
  destruct (btlsec_split rc nsec KMAX KC cx t m ly0 S0 HL) as [HC HS].
  exact (btlsec_join rc nsec KMAX KC _ _ _ _ _
    (ReplyBTopLsi.btlsi_LS_rm_step_f9_cap rc fx (MTs nsec KMAX) cx t m ly0 S0 ly S si h j0 e1 h1 ev LB c2 O2 cap2 out2
       E' H' H'' ds cc ev5 HC HU Hmo HRI Hat Hrr Hcnl Hcshe HF Hpos Hkeys Hpend Ht)
    (ReplyLSBSec.fr_SEC_rm_step TfibB nsec KMAX KC HKC cx t m ly0 S0 ly S si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H''
       ds cc ev5 HS HU Hmo HRI Hat Hrr Ht)).
Qed.

Lemma btlsi_LS_event_malloc_sec : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (nsec : astate -> Z) (KMAX KC : Z),
  240 <= KC ->
  forall cx t m ly S e,
  LSs nsec KMAX KC cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_arm_event.ev_evt cx m e ->
  re_len e < CfParamsReply.fr_MMAX /\ blocks_bytes S + re_len e <= LIVE_MAX /\ mo_ok (MTs nsec KMAX) S (mo_malloc (MTs nsec KMAX) (re_len e)).
Proof.
  intros rc fx nsec KMAX KC HKC cx t m ly S e H HRI He.
  destruct (btlsec_parts rc nsec KMAX KC cx t m ly S H) as (_ & H3 & _ & _ & HS).
  destruct (ReplyB3LS3Arms.fr_LS3_event_malloc TfibB YCfn_cf.CALL_ROOM_B (Z.le_refl _) cx t m ly S e H3 HRI He)
    as (C1 & C2).
  exact (conj C1 (conj C2 (ReplyLSBSec.sec_LS_event_malloc TfibB nsec KMAX KC HKC cx t m ly S e HS))).
Qed.

Lemma btlsi_LS_event_relay_sec : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (nsec : astate -> Z) (KMAX KC : Z),
  240 <= KC ->
  forall cx t m ly S (S1 : astate) e (ly1 : alayout) q,
  LSs nsec KMAX KC cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_arm_event.ev_evt cx m e ->
  mo_le (MTs nsec KMAX) S S1 (mo_malloc (MTs nsec KMAX) (re_len e)) ->
  lm_O m = [] ->
  ablocks TfibB ly1 S1 = ablocks TfibB ly S ++ [(q, re_len e)] ->
  sl_maxr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e) < CfParamsReply.fr_MMAX /\
  blocks_bytes S1 + sl_alloc (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e) <= LIVE_MAX /\
  mo_ok (MTs nsec KMAX) S1 (sl_cost (MTs nsec KMAX) (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)).
Proof.
  intros rc fx nsec KMAX KC HKC cx t m ly S S1 e ly1 q H HRI He Hmo HO Hm.
  destruct (btlsec_parts rc nsec KMAX KC cx t m ly S H) as (_ & H3 & _ & _ & HS).
  destruct (ReplyB3LS3Arms.fr_LS3_event_relay_r TfibB YCfn_cf.CALL_ROOM_B (Z.le_refl _) cx t m ly S S1 e ly1 q H3 HRI He
              Hmo HO Hm) as (C1 & C2).
  exact (conj C1 (conj C2 (ReplyLSBSec.sec_LS_event_relay TfibB nsec KMAX KC HKC cx t m ly S S1 e ly1 q HS He Hmo HO))).
Qed.

Lemma btlsi_LS_event_free_sec : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (nsec : astate -> Z) (KMAX KC : Z),
  240 <= KC ->
  forall cx t m ly S (S1 S2 : astate) e,
  LSs nsec KMAX KC cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_arm_event.ev_evt cx m e -> lm_O m = [] ->
  mo_le (MTs nsec KMAX) S S1 (mo_malloc (MTs nsec KMAX) (re_len e)) ->
  mo_le (MTs nsec KMAX) S1 S2 (sl_cost (MTs nsec KMAX) (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) ->
  mo_ok (MTs nsec KMAX) S2 (mo_free (MTs nsec KMAX)).
Proof.
  intros rc fx nsec KMAX KC HKC cx t m ly S S1 S2 e H HRI He HO M1 M2.
  destruct (btlsec_parts rc nsec KMAX KC cx t m ly S H) as (_ & _ & _ & _ & HS).
  exact (ReplyLSBSec.sec_LS_event_free TfibB nsec KMAX KC HKC cx t m ly S S1 S2 e HS He HO M1 M2).
Qed.

Lemma btlsi_LS_event_step_sec : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (nsec : astate -> Z) (KMAX KC : Z),
  240 <= KC ->
  forall cx t m ly S (S1 S2 S3 : astate) (ly3 : alayout) e v out' (ly1 ly2 : alayout) q,
  LSs nsec KMAX KC cx t m ly S -> W_LLVMFuzzerTestOneInput_arm_event.ev_evt cx m e ->
  mo_le (MTs nsec KMAX) S S1 (mo_malloc (MTs nsec KMAX) (re_len e)) ->
  mo_le (MTs nsec KMAX) S1 S2 (sl_cost (MTs nsec KMAX) (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) ->
  mo_le (MTs nsec KMAX) S2 S3 (mo_free (MTs nsec KMAX)) ->
  0 <= lm_k m < c_n cx -> lm_O m = [] -> 0 <= lm_cap m ->
  ablocks TfibB ly1 S1 = ablocks TfibB ly S ++ [(q, re_len e)] ->
  (exists rest, Permutation (ablocks TfibB ly1 S1) (aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks TfibB ly2 S2)
       (aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) out' ++ rest)) ->
  (exists l1 l2, ablocks TfibB ly2 S2 = l1 ++ (q, re_len e) :: l2 /\ ablocks TfibB ly3 S3 = l1 ++ l2) ->
  0 <= t < OPS_MAX ->
  LSs nsec KMAX KC cx (t + 1) (W_LLVMFuzzerTestOneInput_arm_event.ev_step cx m e v out') ly3 S3.
Proof.
  intros rc fx nsec KMAX KC HKC cx t m ly S S1 S2 S3 ly3 e v out' ly1 ly2 q H He M1 M2 M3 Hk HO0 Hc0 Hm HRR Hf Ht.
  destruct (btlsec_split rc nsec KMAX KC cx t m ly S H) as [HC HS].
  exact (btlsec_join rc nsec KMAX KC _ _ _ _ _
    (ReplyBTopLsi.btlsi_LS_event_step_cap rc fx (MTs nsec KMAX) cx t m ly S S1 S2 S3 ly3 e v out' ly1 ly2 q HC He M1 M2
       M3 Hk HO0 Hc0 Hm HRR Hf Ht)
    (ReplyLSBSec.fr_SEC_event_step TfibB nsec KMAX KC HKC cx t m ly S S1 S2 S3 ly3 e v out' ly1 ly2 q HS He M1 M2 M3 HO0
       Ht)).
Qed.

Lemma btlsi_GN_LS_rig_x_sec : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (nsec : astate -> Z) (KMAX KC : Z),
  240 <= KC ->
  forall cx t m ly S hs,
  LSs nsec KMAX KC cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_gone_base.gn_pairs m hs ->
  W_LLVMFuzzerTestOneInput_gone_base.gn_op cx t m ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall j h, nth j (lm_hs m) None = Some h ->
     (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
     (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  (exists c, val_mem segs (arm (c_W cx) (c_mem cx)) (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX) ->
  let tr := rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
              (W_LLVMFuzzerTestOneInput_gone_base.gn_id cx m) (lm_es m) hs in
  tr_max tr < CfParamsReply.fr_MMAX /\ blocks_bytes S + tr_peak tr <= LIVE_MAX /\ mo_ok (MTs nsec KMAX) S (tr_cost (MTs nsec KMAX) tr) /\
  lm_cap m < CfParamsReply.fr_MMAX /\
  blocks_bytes S + tr_peak tr + 4 * Z.max (lm_cap m) (tr_max tr) <= LIVE_MAX.
Proof.
  intros rc fx nsec KMAX KC HKC cx t m ly S hs H HRI Hp Hop HU Hpos Hsrc HCAP0.
  destruct (btlsec_parts rc nsec KMAX KC cx t m ly S H) as (H3c & _ & _ & _ & HS).
  pose proof (ReplyB3LS3Peak.pk_lsi_gone_rig_m TfibB
                (CAPSs nsec KMAX KC)
                cx t m ly S hs H HRI Hp Hop HU Hpos Hsrc HCAP0) as X.
  pose proof (ReplyLSBSec.sec_GN_LS_rig_x TfibB nsec KMAX KC HKC cx t m ly S hs H3c HS HRI Hp Hop HU Hsrc) as M.
  cbv zeta in X, M |- *.
  destruct X as (R1 & R2 & R4 & R5).
  exact (conj R1 (conj R2 (conj M (conj R4 R5)))).
Qed.
