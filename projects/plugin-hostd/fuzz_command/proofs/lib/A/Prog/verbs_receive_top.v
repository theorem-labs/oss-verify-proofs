(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: tverbs_receive_spec (lib/A/Prog/verbs_receive_c.v) on the ASan build of
   plugin-hostd/fuzz_command, closed. lib/A/Prog/verbs_receive.v proves it from the 32 segment statements of
   lib/A/Prog/verbs_receive_iface.v; here each segment statement is its segment lemma (verbs_receive_sNN.v), applied
   to the Section hypotheses this file takes, and the interface's record-fact premises are the per-binary lemmas of
   CmdRecCells.v, CmdRecRo.v and CmdRecImg.v over HB and IMG (the statements of lib/A/Prog/CmdRecFacts.v).

   The hypotheses are verbs_receive_c.v's, with their names and types (statement pass 4b: the callee contracts and
   the FP-dependent runtime entries at every FP state), and the walk's record facts under cgif's names (HB, IMG,
   TL, TLF, ML, MTL, MTFL, VOBJS, VHIS, SIGP, PRW). Each segment lemma is applied at every FP state (V01 .. V32). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtString RtNumber RtAlloc04 RtShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib PaLibF.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecBase CmdRecCells CmdRecRo CmdRecImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
chain_words_c descriptors_add_c descriptors_get_c descriptors_panel_get_c is_instance_verb_c lv2_refusals_forget_c
number_c pin_set_words_c pins_clear_c reply_c sup_add_c sup_after_reply_c sup_broadcast_c sup_call_c
sup_chain_c sup_chain_clear_c sup_connect_c sup_host_setting_c sup_instance_info_c sup_instance_verb_c sup_lv2_worker_set_c
sup_pin_accept_c sup_policy_set_c sup_pool_config_c sup_quarantine_clear_c sup_remove_c sup_remove_all_c
sup_reply_code_c sup_reset_c sup_resp_c sup_worker_env_c sup_worker_list_c verb_is_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_c verbs_receive_iface.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require verbs_receive
  verbs_receive_s01 verbs_receive_s02 verbs_receive_s03 verbs_receive_s04 verbs_receive_s05 verbs_receive_s06
  verbs_receive_s07 verbs_receive_s08 verbs_receive_s09 verbs_receive_s10 verbs_receive_s11 verbs_receive_s12
  verbs_receive_s13 verbs_receive_s14 verbs_receive_s15 verbs_receive_s16 verbs_receive_s17 verbs_receive_s18
  verbs_receive_s19 verbs_receive_s20 verbs_receive_s21 verbs_receive_s22 verbs_receive_s23 verbs_receive_s24
  verbs_receive_s25 verbs_receive_s26 verbs_receive_s27 verbs_receive_s28 verbs_receive_s29 verbs_receive_s30
  verbs_receive_s31 verbs_receive_s32.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Variables PC_STRDUP_RA0 PC_STRNDUP_RA0 : Z.
(* the program callees' contracts (verbs_receive_c.v:195-226), at every FP state (statement pass 4) *)
Hypothesis TDESCRIPTORS_ADD : forall fx0 : YK11.FPState, tdescriptors_add_spec (fx := fx0) B MT.
Hypothesis TDESCRIPTORS_GET : forall fx0 : YK11.FPState, tdescriptors_get_spec (fx := fx0) B MT.
Hypothesis TDESCRIPTORS_PANEL_GET : forall fx0 : YK11.FPState, tdescriptors_panel_get_spec (fx := fx0) B MT.
Hypothesis TIS_INSTANCE_VERB : forall fx0 : YK11.FPState, tis_instance_verb_spec (fx := fx0) B MT.
Hypothesis TLV2_REFUSALS_FORGET : forall fx0 : YK11.FPState, tlv2_refusals_forget_spec (fx := fx0) B MT.
Hypothesis TNUMBER : forall fx0 : YK11.FPState, tnumber_spec (fx := fx0) B MT.
Hypothesis TPINS_CLEAR : forall fx0 : YK11.FPState, tpins_clear_spec (fx := fx0) B MT.
Hypothesis TREPLY : forall fx0 : YK11.FPState, treply_spec (fx := fx0) B MT.
Hypothesis TSUP_ADD : forall fx0 : YK11.FPState, tsup_add_spec (fx := fx0) B MT.
Hypothesis TSUP_AFTER_REPLY : forall fx0 : YK11.FPState, tsup_after_reply_spec (fx := fx0) B MT.
Hypothesis TSUP_BROADCAST : forall fx0 : YK11.FPState, tsup_broadcast_spec (fx := fx0) B MT.
Hypothesis TSUP_CALL : forall fx0 : YK11.FPState, tsup_call_spec (fx := fx0) B MT.
Hypothesis TSUP_CHAIN_CLEAR : forall fx0 : YK11.FPState, tsup_chain_clear_spec (fx := fx0) B MT.
Hypothesis TSUP_CONNECT : forall fx0 : YK11.FPState, tsup_connect_spec (fx := fx0) B MT.
Hypothesis TSUP_HOST_SETTING : forall fx0 : YK11.FPState, tsup_host_setting_spec (fx := fx0) B MT.
Hypothesis TSUP_INSTANCE_INFO : forall fx0 : YK11.FPState, tsup_instance_info_spec (fx := fx0) B MT.
Hypothesis TSUP_INSTANCE_VERB : forall fx0 : YK11.FPState, tsup_instance_verb_spec (fx := fx0) B MT.
Hypothesis TSUP_LV2_WORKER_SET : forall fx0 : YK11.FPState, tsup_lv2_worker_set_spec (fx := fx0) B MT.
Hypothesis TSUP_PIN_ACCEPT : forall fx0 : YK11.FPState, tsup_pin_accept_spec (fx := fx0) B MT.
Hypothesis TSUP_POLICY_SET : forall fx0 : YK11.FPState, tsup_policy_set_spec (fx := fx0) B MT.
Hypothesis TSUP_POOL_CONFIG : forall fx0 : YK11.FPState, tsup_pool_config_spec (fx := fx0) B MT.
Hypothesis TSUP_QUARANTINE_CLEAR : forall fx0 : YK11.FPState, tsup_quarantine_clear_spec (fx := fx0) B MT.
Hypothesis TSUP_REMOVE : forall fx0 : YK11.FPState, tsup_remove_spec (fx := fx0) B MT.
Hypothesis TSUP_REMOVE_ALL : forall fx0 : YK11.FPState, tsup_remove_all_spec (fx := fx0) B MT.
Hypothesis TSUP_REPLY_CODE : forall fx0 : YK11.FPState, tsup_reply_code_spec (fx := fx0) B MT.
Hypothesis TSUP_RESET : forall fx0 : YK11.FPState, tsup_reset_spec (fx := fx0) B MT.
Hypothesis TSUP_RESP : forall fx0 : YK11.FPState, tsup_resp_spec (fx := fx0) B MT.
Hypothesis TSUP_WORKER_ENV : forall fx0 : YK11.FPState, tsup_worker_env_spec (fx := fx0) B MT.
Hypothesis TSUP_WORKER_LIST : forall fx0 : YK11.FPState, tsup_worker_list_spec (fx := fx0) B MT.
Hypothesis TVERB_IS : forall fx0 : YK11.FPState, tverb_is_spec (fx := fx0) B MT.
Hypothesis TCHAIN_WORDS : forall fx0 : YK11.FPState, tchain_words_spec (fx := fx0) B MT.
Hypothesis TPIN_SET_WORDS : forall fx0 : YK11.FPState, tpin_set_words_spec (fx := fx0) B MT.
(* the runtime entries (verbs_receive_c.v:228-243), at every FP state *)
Hypothesis SM4 : forall fx0 : YK11.FPState, astack_malloc_realizes (fx := fx0) SEGS B 4.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis SH00 : forall fx0 : YK11.FPState, RtShadow.aset_shadow_realizes (fx := fx0) SEGS B (SIGMA CS___asan_set_shadow_00) 0.
Hypothesis SHF5 : forall fx0 : YK11.FPState, RtShadow.aset_shadow_realizes (fx := fx0) SEGS B (SIGMA CS___asan_set_shadow_f5) 0xf5.
Hypothesis SHF8 : forall fx0 : YK11.FPState, RtShadow.aset_shadow_realizes (fx := fx0) SEGS B (SIGMA CS___asan_set_shadow_f8) 0xf8.
Hypothesis STRLEN : forall fx0 : YK11.FPState,
  RtString.astrlen_realizes (fx := fx0) SEGS B (SIGMA CS___interceptor_trampoline_strlen).
Hypothesis STRCMP : forall fx0 : YK11.FPState,
  RtString.astrcmp_realizes (fx := fx0) SEGS B (SIGMA CS___interceptor_trampoline_strcmp).
Hypothesis STRNCMP : forall fx0 : YK11.FPState,
  RtString.astrncmp_realizes (fx := fx0) SEGS B (SIGMA CS___interceptor_trampoline_strncmp).
Hypothesis STRCSPN : forall fx0 : YK11.FPState,
  RtString.astrcspn_realizes (fx := fx0) SEGS B (SIGMA CS___interceptor_trampoline_strcspn) 0xa7098 0x6045d8.
Hypothesis STRTOK_R : forall fx0 : YK11.FPState,
  RtString.astrtok_r_realizes (fx := fx0) SEGS B (SIGMA CS_strtok_r) 0xa7098 0x6045d8.
Hypothesis AATOI : forall fx0 : YK11.FPState,
  RtNumber.aatoi_realizes (fx := fx0) SEGS B (SIGMA CS___interceptor_trampoline_atoi) 0xae8d5 0xa7098 0x6045d8.
Hypothesis ASTRDUP : forall fx0 : YK11.FPState,
  RtAlloc04.astrdup04_rule (fx := fx0) SEGS B MT (SIGMA CS___interceptor_trampoline_strdup) PC_STRDUP_RA0.
Hypothesis ASTRNDUP : forall fx0 : YK11.FPState,
  RtAlloc04.astrndup04_rule (fx := fx0) SEGS B MT (SIGMA CS___interceptor_trampoline_strndup) PC_STRNDUP_RA0.
Hypothesis AFREE : forall fx0 : YK11.FPState, afree04_rule (fx := fx0) SEGS B MT.
(* the record facts *)
Hypothesis HB : CmdBSyms B.
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis VOBJS : cmd_val_objs (PI := PI).
Hypothesis VHIS : cmd_val_his (PI := PI).
Hypothesis SIGP : cmd_sig_prog (PI := PI).
Hypothesis PRW : prog_rw SEGS B.

Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the interface's record-fact premises, by the per-binary lemmas *)
Let RECC : vr_rec_cells B := cmd_rec_cells SEGS B LAWS HB IMG.
Let ROA : vr_ro_of_aro B := cmd_ro_ok_of_aro SEGS B LAWS HB IMG.
Let ROIN : vr_ro_in_img := cmd_ro_in_img SEGS B LAWS HB IMG.
Let RRO : vr_relro_img := cif_relro_img _ _ IMG.
Let RPG : vr_pg_not_ro := cif_prog_not_ro _ _ IMG.
Let PROGU : vr_prog_unowned B := cmd_prog_unowned SEGS B LAWS HB IMG.
(* a byte of a live block is below the block's request size *)
Lemma vrt_blktail : vr_blktail B.
Proof.
intros ly S W mem md p n x HAR Hin Hx.
apply (cmd_heap_tail_vis SEGS B LAWS HB ly S W mem md p n x HAR Hin).
unfold req_size. destruct (n =? 0) eqn:E; [apply Z.eqb_eq in E; lia | lia].
Qed.
(* the literals' and g_instance_info_verbs' checks, by the record's checkers *)
Lemma vrt_shr_chk : forallb (fun an => cmd_addr_b (fst an) (snd an) && cmd_hull_b (fst an) (snd an)) vr_shr = true.
Proof. vm_compute. reflexivity. Qed.
Lemma vrt_shadow_ok : vr_shadow_ok B.
Proof.
intros ly S W mem md a n HAR Hin.
exact (proj1 (Forall_forall _ _) (cmd_lits_chk SEGS B LAWS HB vr_shr vrt_shr_chk ly S W mem md HAR) (a, n) Hin).
Qed.
Let BLKT : vr_blktail B := vrt_blktail.
Let SHOK : vr_shadow_ok B := vrt_shadow_ok.

(* each segment lemma at every FP state (the assembly runs a segment at the FP state the walk has reached) *)
Let V01 : forall fq, vr_s01_stmt (fx := fq) B MT := fun fq =>
  verbs_receive_s01.vr_s01 (fx := fq) B MT SM4 SMP SHF8 TL TLF ML MTL MTFL ROA RRO RPG RECC PROGU.
Let V02 : forall fq, vr_s02_stmt (fx := fq) B MT := fun fq =>
  verbs_receive_s02.vr_s02 (fx := fq) B MT PC_STRNDUP_RA0 (SH00 fq) (STRLEN fq) (ASTRNDUP fq) TL MTL BLKT ROA RRO RECC PROGU.
Let V03 : forall fq, vr_s03_stmt (fx := fq) B MT := fun fq =>
  verbs_receive_s03.vr_s03 (fx := fq) B MT ROA RRO RECC PROGU.
Let V04 : forall fq, vr_s04_stmt (fx := fq) B MT := fun fq =>
  verbs_receive_s04.vr_s04 (fx := fq) B MT PC_STRDUP_RA0 (STRTOK_R fq) (ASTRDUP fq) TL MTL RRO RECC PROGU SHOK BLKT ROA.
Let V05 : forall fq, vr_s05_stmt (fx := fq) B MT := fun fq =>
  verbs_receive_s05.vr_s05 (fx := fq) B MT TSUP_RESP TREPLY HB MTL SIGP RRO RPG RECC PROGU ROA.
Let V06 : forall fq, vr_s06_stmt (fx := fq) B MT := fun fq =>
  verbs_receive_s06.vr_s06 (fx := fq) B MT TL SHOK BLKT STRCMP STRNCMP STRCSPN ROA RRO RECC PROGU HB SIGP TVERB_IS.
Let V07 : forall fq, vr_s07_stmt (fx := fq) B MT := fun fq =>
  verbs_receive_s07.vr_s07 (fx := fq) B MT TSUP_RESP TSUP_ADD TSUP_REPLY_CODE TDESCRIPTORS_ADD STRCMP STRNCMP AATOI HB TL
    MTL SIGP SHOK BLKT ROA RRO RPG RECC PROGU.
Let V08 : forall fq, vr_s08_stmt (fx := fq) B MT := fun fq =>
  verbs_receive_s08.vr_s08 (fx := fq) B MT TDESCRIPTORS_GET HB MTL SIGP ROA RRO RPG RECC PROGU.
Let V09 : forall fq, vr_s09_stmt (fx := fq) B MT := fun fq =>
  verbs_receive_s09.vr_s09 (fx := fq) B MT TDESCRIPTORS_PANEL_GET HB MTL SIGP ROA RRO RPG RECC PROGU.
Let V10 : forall fq, vr_s10_stmt (fx := fq) B MT := fun fq =>
  verbs_receive_s10.vr_s10 (fx := fq) B MT TSUP_REMOVE TSUP_REMOVE_ALL AATOI HB TL MTL SIGP ROA RRO RPG RECC PROGU BLKT.
Let V11 : forall fq, vr_s11_stmt (fx := fq) B MT := fun fq =>
  verbs_receive_s11.vr_s11 (fx := fq) B MT TSUP_WORKER_LIST HB MTL SIGP ROA RRO RPG RECC PROGU.
Let V12 : forall fq, vr_s12_stmt (fx := fq) B MT := fun fq =>
  verbs_receive_s12.vr_s12 (fx := fq) B MT TSUP_INSTANCE_INFO AATOI HB TL MTL SIGP BLKT ROA RRO RPG RECC PROGU.
Let V13 : forall fq, vr_s13_stmt (fx := fq) B MT := fun fq =>
  verbs_receive_s13.vr_s13 (fx := fq) B MT TSUP_RESET HB MTL SIGP VOBJS ROA RRO RPG RECC PROGU BLKT.
Let V14 : forall fq, vr_s14_stmt (fx := fq) B MT := fun fq =>
  verbs_receive_s14.vr_s14 (fx := fq) B MT TSUP_QUARANTINE_CLEAR HB MTL SIGP ROA RRO RPG RECC PROGU.
Let V15 : forall fq, vr_s15_stmt (fx := fq) B MT := fun fq =>
  verbs_receive_s15.vr_s15 (fx := fq) B MT TSUP_POLICY_SET HB MTL SIGP ROA RRO RPG RECC PROGU.
Let V16 : forall fq, vr_s16_stmt (fx := fq) B MT := fun fq =>
  verbs_receive_s16.vr_s16 (fx := fq) B MT TSUP_LV2_WORKER_SET HB MTL SIGP ROA RRO RPG RECC PROGU.
Let V17 : forall fq, vr_s17_stmt (fx := fq) B MT := fun fq =>
  verbs_receive_s17.vr_s17 (fx := fq) B MT TSUP_POOL_CONFIG AATOI HB TL MTL SIGP BLKT ROA RRO RPG RECC PROGU.
Let V18 : forall fq, vr_s18_stmt (fx := fq) B MT := fun fq =>
  verbs_receive_s18.vr_s18 (fx := fq) B MT TSUP_WORKER_ENV HB MTL SIGP ROA RRO RPG RECC PROGU.
Let V19 : forall fq, vr_s19_stmt (fx := fq) B MT := fun fq =>
  verbs_receive_s19.vr_s19 (fx := fq) B MT TCHAIN_WORDS HB MTL SIGP ROA RRO RPG RECC PROGU.
Let V20 : forall fq, vr_s20_stmt (fx := fq) B MT := fun fq =>
  verbs_receive_s20.vr_s20 (fx := fq) B MT TNUMBER TSUP_CHAIN_CLEAR HB MTL MTFL SIGP RRO RPG RECC PROGU ROA.
Let V21 : forall fq, vr_s21_stmt (fx := fq) B MT := fun fq =>
  verbs_receive_s21.vr_s21 (fx := fq) B MT TPIN_SET_WORDS HB MTL SIGP ROA RRO RPG RECC PROGU.
Let V22 : forall fq, vr_s22_stmt (fx := fq) B MT := fun fq =>
  verbs_receive_s22.vr_s22 (fx := fq) B MT TSUP_PIN_ACCEPT HB MTL SIGP ROA RRO RPG RECC PROGU.
Let V23 : forall fq, vr_s23_stmt (fx := fq) B MT := fun fq =>
  verbs_receive_s23.vr_s23 (fx := fq) B MT TLV2_REFUSALS_FORGET TPINS_CLEAR TSUP_RESP HB MTL SIGP RRO RPG RECC PROGU ROA.
Let V24 : forall fq, vr_s24_stmt (fx := fq) B MT := fun fq =>
  verbs_receive_s24.vr_s24 (fx := fq) B MT TSUP_RESP HB MTL SIGP PRW VHIS RRO RPG RECC PROGU ROA.
Let V25 : forall fq, vr_s25_stmt (fx := fq) B MT := fun fq =>
  verbs_receive_s25.vr_s25 (fx := fq) B MT STRCMP TL SHOK BLKT ROA RRO RECC.
Let V26 : forall fq, vr_s26_stmt (fx := fq) B MT := fun fq =>
  verbs_receive_s26.vr_s26 (fx := fq) B MT TSUP_INSTANCE_VERB HB MTL SIGP SHOK ROA RRO RPG RECC PROGU.
Let V27 : forall fq, vr_s27_stmt (fx := fq) B MT := fun fq =>
  verbs_receive_s27.vr_s27 (fx := fq) B MT TIS_INSTANCE_VERB TSUP_CALL AATOI HB TL MTL SIGP BLKT ROA RRO RPG RECC PROGU.
Let V28 : forall fq, vr_s28_stmt (fx := fq) B MT := fun fq =>
  verbs_receive_s28.vr_s28 (fx := fq) B MT TVERB_IS TSUP_CONNECT TSUP_BROADCAST TSUP_HOST_SETTING HB MTL SIGP BLKT ROA
    RRO RPG RECC PROGU.
Let V29 : forall fq, vr_s29_stmt (fx := fq) B MT := fun fq =>
  verbs_receive_s29.vr_s29 (fx := fq) B MT TSUP_RESP MTL SIGP ROA RRO RECC PROGU.
Let V30 : forall fq, vr_s30_stmt (fx := fq) B MT := fun fq =>
  verbs_receive_s30.vr_s30 (fx := fq) B MT RRO RPG RECC PROGU ROA TREPLY HB MTL SIGP.
Let V31 : forall fq, vr_s31_stmt (fx := fq) B MT := fun fq =>
  verbs_receive_s31.vr_s31 (fx := fq) B MT TSUP_AFTER_REPLY STRNCMP STRCSPN AATOI HB TL MTL VOBJS SIGP RRO RPG ROA RECC
    PROGU SHOK BLKT.
Let V32 : forall fq, vr_s32_stmt (fx := fq) B MT := fun fq =>
  verbs_receive_s32.vr_s32 (fx := fq) B MT (AFREE fq) (SHF5 fq) (SHF8 fq) ASF FFL TL ML MTL MTFL PROGU.

Theorem tverbs_receive : tverbs_receive_spec B MT.
Proof.
exact (verbs_receive.tverbs_receive_spec_of_segs B MT V01 V02 V03 V04 V05 V06 V07 V08 V09 V10 V11 V12 V13 V14 V15 V16
  V17 V18 V19 V20 V21 V22 V23 V24 V25 V26 V27 V28 V29 V30 V31 V32 RECC ROIN fx).
Qed.

End e.
End f.
End d.
