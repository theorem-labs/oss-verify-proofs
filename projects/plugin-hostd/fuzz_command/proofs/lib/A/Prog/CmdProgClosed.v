(* The program side of plugin-hostd/fuzz_command's ASan proof (image A), composed at the pinned image: the contract
   `t<fn>_spec` (lib/A/Prog/<fn>_c.v) of each of the 63 program functions at CmdImg.v's instance PB_cmd (segments
   tfibsegs), the sink head AE2k.tfib_sink_head, the allocator record AD2l.CmdB (AD2l.CmdB_syms) and the trivial meter
   YCbp.ameter_triv (ameter_triv_laws, ameter_triv_fs_laws), at every run ceiling and FP state, from
   - each function's closed theorem `t<fn>_closed` (lib/A/Prog/*Closed.v); check_words_pin_set, which has none, by its
     walk (check_words_pin_set.v, pb_check_words_pin_set) with the record's facts its statement names;
   - the runtime entries' contracts from their closing files: lib/A/Rt/RtClosed.v (shadow fills, side-stack entries,
     the string, number and printf interceptors), lib/A/Rt/Strnlen.v (strnlen), lib/A/Rt/RtLAsanMemcpy.v and
     RtLAsanMemset.v (the intrinsics), lib/A/AE2s.v (bcmp), and the allocator: YCbp.v's rules of the trivial meter over
     AF0w.v's malloc contract (tfib_amalloc_realizes), AF0q.v's free contract (afree_realizes_closed), and for strdup /
     strndup RtD04d.v / RtD04n.v over the entries' walks (RtDStrdupX.v, RtDStrndup.v, RtDMallocBody.v) with AF0w.v's
     asan_malloc contract (cmd_amalloc_inner).
   No hypothesis remains: cmd_ltoi_all is lib/A/Prog/CmdLibX.v:155's HLTOI (CmdTop.v's), and cmd_lib_x_final is
   CmdLibX.v's cmd_lib_x_closed with it. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YM05 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0s YG0d
  YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI16 YC5d YG0q YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m AB1v ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AE2k AD2l AF0w AF0q AE2s CmdShape.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Rt Require StrnlenDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtDefs RtAPI RtString RtNumber RtFormat RtStack
  RtShadow RtAlloc04 RtDDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtClosed Strnlen RtLAsanMemcpy RtLAsanMemset
  RtDStrdupX RtDStrndup RtDMallocBody RtD04d RtD04n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdImg CmdBase CmdObj
  CmdGlob CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecBase CmdRecCells CmdRecImg CmdRecRest
  CmdLibX.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require
LLVMFuzzerTestOneInput_c answer_c answer_code_c arg_i_c arg_line_c chain_words_c check_arity_c check_refusal_c
check_reply_answer_c check_reply_c check_round_trip_c check_words_add_c check_words_c check_words_chain_c
check_words_pin_set_c descriptors_add_c descriptors_get_c descriptors_panel_get_c hand_back_c is_instance_verb_c
joined_c lv2_refusals_forget_c mix_call_c number_c pin_set_words_c pins_clear_c pins_set_c rec_calls_copy_c
rec_calls_equal_c rec_calls_free_c rec_canonical_c rec_clear_c rec_code_declared_c rec_shape_of_c reply_c
send_message_c socket_send_c sup_add_c sup_after_reply_c sup_broadcast_c sup_call_c sup_chain_c sup_chain_clear_c
sup_connect_c sup_host_setting_c sup_instance_info_c sup_instance_verb_c sup_lv2_worker_set_c sup_pin_accept_c
sup_policy_set_c sup_pool_config_c sup_quarantine_clear_c sup_remove_all_c sup_remove_c sup_reply_code_c sup_reset_c
sup_resp_c sup_worker_env_c sup_worker_list_c syntax_reply_matches_c verb_is_c verbs_receive_c xstrdup_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require
AnswerClosed ArgIClosed ArgLineClosed ChainWordsClosed CheckArityClosed CheckRefusalClosed CheckWordsAddClosed
CheckWordsChainClosed CheckWordsClosed CmdA9Closed CmdReplyWalksClosed HandBackClosed IsInstanceVerbClosed LtoiClosed
MixCallClosed NumberClosed PinSetWordsClosed RecBClosed ReplyClosed SupAddClosed SupBroadcastClosed SupCallClosed
SupConnectClosed SupRemoveAllRefitClosed SupRemoveClosed SupRespClosed VerbIsClosed VerbsReceiveClosed
check_words_pin_set.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(** * The facts check_words_pin_set's walk names, at CmdB *)
(* the closed check of its two image literals, "-" (0x21ac0, 2 bytes) and "verdict=" (0x21b60, 9 bytes) *)
Lemma cpc_cw_lits_chk :
  forallb (fun an : Z * Z => cmd_addr_b (fst an) (snd an) && cmd_hull_b (fst an) (snd an))%bool
    [(0x21ac0, 2); (0x21b60, 9)] = true.
Proof. vm_compute. reflexivity. Qed.
(* g_rec lies in one of CmdB's zero-shadow ranges (the walk's GREC_ZS) *)
Lemma cpc_grec_zs :
  Exists (fun z : Z * Z => fst z <= A_G_REC /\ A_G_REC + RecInv.REC_SIZE <= fst z + snd z) (as_zero_shadow AD2l.CmdB).
Proof.
assert (H : existsb (fun z : Z * Z => (fst z <=? A_G_REC) && (A_G_REC + RecInv.REC_SIZE <=? fst z + snd z))%bool
  (as_zero_shadow AD2l.CmdB) = true) by (vm_compute; reflexivity).
apply existsb_exists in H as (z & Hz & Hb). apply Exists_exists. exists z. split; [exact Hz|].
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. split; [exact H1 | exact H2].
Qed.

Section closed. Context {rc : YM05.RunCeil}.
#[local] Existing Instance AE2k.tfib_sink_head | 0.
#[local] Existing Instance CmdImg.PB_cmd | 0.
#[local] Notation SK0 := AE2k.tfib_sink_head.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PB_cmd).
#[local] Notation SIG c := (@pa_sigma _ cmd_listing PB_cmd c).
#[local] Notation B := AD2l.CmdB.
#[local] Notation MT := YCbp.ameter_triv.
(* the record, the meter's laws, and the kit's closers of a walk's record hypotheses, at CmdB *)
#[local] Notation HB := AD2l.CmdB_syms.
#[local] Notation MTL := YCbp.ameter_triv_laws.
#[local] Notation MTFL := YCbp.ameter_triv_fs_laws.
#[local] Notation LAWS := (YG0q.AR_laws_ok SEGS B).
#[local] Notation TL := (CmdRecRest.cmd_palib B HB).
#[local] Notation ML := (CmdRecRest.cmd_model_laws B HB).
#[local] Notation SMP := (CmdRecRest.cmd_stack_malloc_progress B).
#[local] Notation FFL := (CmdRecRest.cmd_frame_flag_law B).
#[local] Notation ASF := (CmdRecRest.cmd_astack_free_law B).
#[local] Notation ENV := (@CmdPaLib.pal_env rc cmd_listing PB_cmd B TL).
#[local] Notation k_tailq := (CmdRecImg.cmd_heap_tail_vis SEGS B LAWS HB).
#[local] Notation k_cw_lits := (fun ly S W mem md a n HAR Hin =>
  proj1 (Forall_forall _ _) (CmdRecCells.cmd_lits_chk SEGS B LAWS HB _ cpc_cw_lits_chk ly S W mem md HAR) (a, n) Hin).

(** * The runtime entries' contracts at the program's form, from their closers *)
(* the allocator: the trivial meter's rules (YCbp.v) over the core's malloc and free contracts (AF0w.v, AF0q.v) *)
Lemma r_malloc4 : forall fx0 : YK11.FPState, @YC5d.amalloc04_rule fx0 rc SK0 SEGS B MT.
Proof.
exact (fun fx0 => @YCbp.amalloc04_rule_triv fx0 rc SK0 SEGS B CmdImg.cmd_segs_low ENV LAWS ML
  (@AF0w.tfib_amalloc_realizes fx0 rc B HB (fun t => eq_refl))).
Qed.
Lemma r_free4 : forall fx0 : YK11.FPState, @YC5d.afree04_rule fx0 rc SK0 SEGS B MT.
Proof.
exact (fun fx0 => @YCbp.afree04_rule_triv fx0 rc SK0 SEGS B CmdImg.cmd_segs_low ENV LAWS ML
  (@AF0q.afree_realizes_closed fx0 rc B HB (fun t => eq_refl))).
Qed.
Lemma r_free_null4 : forall fx0 : YK11.FPState, @YC5d.afree_null04_rule fx0 rc SK0 SEGS B MT.
Proof.
exact (fun fx0 => @YCbp.afree_null04_rule_triv fx0 rc SK0 SEGS B CmdImg.cmd_segs_low ENV LAWS ML
  (@AF0q.afree_realizes_closed fx0 rc B HB (fun t => eq_refl))).
Qed.
(* strdup (0x451dc) and strndup (0x45138): the trivial meter's rules (RtD04d.v, RtD04n.v) over the entries' walks
   (RtDStrdupX.v; RtDStrndup.v with RtDMallocBody.v's malloc body), both over AF0w.v's asan_malloc contract *)
Lemma r_strdup4 : forall fx0 : YK11.FPState,
  @RtAlloc04.astrdup04_rule fx0 rc SK0 SEGS B MT (SIG CS___interceptor_trampoline_strdup) RtAPI.PC_STRDUP_RA0.
Proof.
exact (fun fx0 => @RtD04d.astrdup04_rule_triv fx0 rc SK0 SEGS B CmdImg.cmd_segs_low ENV LAWS ML
  (SIG CS___interceptor_trampoline_strdup) RtAPI.PC_STRDUP_RA0
  (@RtDStrdupX.cmd_strdup fx0 rc B LAWS HB (@AF0w.cmd_amalloc_inner fx0 rc B HB (fun t => eq_refl)))).
Qed.
Lemma r_strndup4 : forall fx0 : YK11.FPState,
  @RtAlloc04.astrndup04_rule fx0 rc SK0 SEGS B MT (SIG CS___interceptor_trampoline_strndup) RtAPI.PC_STRNDUP_RA0.
Proof.
exact (fun fx0 => @RtD04n.astrndup04_rule_triv fx0 rc SK0 SEGS B CmdImg.cmd_segs_low ENV LAWS ML
  (SIG CS___interceptor_trampoline_strndup) RtAPI.PC_STRNDUP_RA0 RtAPI.PC_STRNDUP_MID
  (@RtDStrndup.cmd_strndup fx0 rc B LAWS HB (@RtDMallocBody.cmd_amalloc_body fx0 rc B HB LAWS
    (@AF0w.cmd_amalloc_inner fx0 rc B HB (fun t => eq_refl))))).
Qed.
(* __asan_memcpy (0x57630) and __asan_memset (0x57acc): pc_asan_memcpy / pc_asan_memset (as_code CmdB) compute to the
   program's symbols *)
Lemma r_memcpy : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG CS___asan_memcpy).
Proof. exact (fun fx0 => @RtLAsanMemcpy.cmd_asan_memcpy fx0 rc B LAWS HB). Qed.
Lemma r_memset : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OSet (SIG CS___asan_memset).
Proof. exact (fun fx0 => @RtLAsanMemset.cmd_asan_memset fx0 rc B LAWS HB). Qed.
(* the string, number and printf interceptors (RtClosed.v; strnlen by Strnlen.v, bcmp by AE2s.v) *)
Lemma r_strlen : forall fx0 : YK11.FPState,
  @RtString.astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen).
Proof. exact (fun fx0 => @RtClosed.cmd_strlen_closed fx0 rc B HB). Qed.
Lemma r_strcmp : forall fx0 : YK11.FPState,
  @RtString.astrcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcmp).
Proof. exact (fun fx0 => @RtClosed.cmd_strcmp_closed fx0 rc B HB). Qed.
Lemma r_strncmp : forall fx0 : YK11.FPState,
  @RtString.astrncmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strncmp).
Proof. exact (fun fx0 => @RtClosed.cmd_strncmp_closed fx0 rc B HB). Qed.
Lemma r_strspn : forall fx0 : YK11.FPState,
  @RtString.astrspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strspn) 0xa7098 0x6045d8.
Proof. exact (fun fx0 => @RtClosed.cmd_strspn_closed fx0 rc B HB). Qed.
Lemma r_strcspn : forall fx0 : YK11.FPState,
  @RtString.astrcspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcspn) 0xa7098 0x6045d8.
Proof. exact (fun fx0 => @RtClosed.cmd_strcspn_closed fx0 rc B HB). Qed.
Lemma r_strtok_r : forall fx0 : YK11.FPState,
  @RtString.astrtok_r_realizes fx0 rc SEGS B (SIG CS_strtok_r) 0xa7098 0x6045d8.
Proof. exact (fun fx0 => @RtClosed.cmd_strtok_r_closed fx0 rc B HB). Qed.
Lemma r_strnlen : forall fx0 : YK11.FPState,
  @StrnlenDef.astrnlen_whole_realizesM fx0 rc SEGS B 0x10358 0x10378 (SIG CS___interceptor_trampoline_strnlen).
Proof. exact (fun fx0 => @Strnlen.strnlen_icpt_realizesM fx0 rc B LAWS HB). Qed.
Lemma r_memchr : forall fx0 : YK11.FPState,
  @RtString.amemchr0_nf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_memchr).
Proof. exact (fun fx0 => @RtClosed.cmd_memchr_nf_closed fx0 rc B HB). Qed.
Lemma r_strcat : forall fx0 : YK11.FPState,
  @RtString.astrcat_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcat).
Proof. exact (fun fx0 => @RtClosed.cmd_strcat_closed fx0 rc B HB). Qed.
Lemma r_atoi : forall fx0 : YK11.FPState,
  @RtNumber.aatoi_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_atoi) 0xae8d5 0xa7098 0x6045d8.
Proof. exact (fun fx0 => @RtClosed.cmd_atoi_closed fx0 rc B HB). Qed.
Lemma r_strtol : forall fx0 : YK11.FPState,
  @RtNumber.astrtol_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strtol) 0xa7098 0x6045d8.
Proof. exact (fun fx0 => @RtClosed.cmd_strtol_closed fx0 rc B HB). Qed.
Lemma r_bcmp : forall fx0 : YK11.FPState, @abcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_bcmp).
Proof. exact (fun fx0 => @AE2s.bcmp_icpt_contract fx0 rc B LAWS HB). Qed.
Lemma r_snprintf : forall fx0 : YK11.FPState,
  @RtFormat.asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa7098 0x6045d8.
Proof. exact (fun fx0 => @RtClosed.cmd_snprintf_closed fx0 rc B HB). Qed.
Lemma r_sprintf : forall fx0 : YK11.FPState,
  @RtFormat.asprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_sprintf) 0xa7098 0x6045d8.
Proof. exact (fun fx0 => @RtClosed.cmd_sprintf_closed fx0 rc B HB). Qed.
(* the side-stack entries and the shadow fills (RtClosed.v) *)
Lemma r_sm0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0.
Proof. exact (fun fx0 => @RtClosed.cmd_stack_malloc0_contract_closed fx0 rc B HB). Qed.
Lemma r_sm1 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
Proof. exact (fun fx0 => @RtClosed.cmd_stack_malloc1_contract_closed fx0 rc B HB). Qed.
Lemma r_sm3 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 3.
Proof. exact (fun fx0 => @RtClosed.cmd_stack_malloc3_contract_closed fx0 rc B HB). Qed.
Lemma r_sm4 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 4.
Proof. exact (fun fx0 => @RtClosed.cmd_stack_malloc4_contract_closed fx0 rc B HB). Qed.
Lemma r_sm5 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 5.
Proof. exact (fun fx0 => @RtClosed.cmd_stack_malloc5_contract_closed fx0 rc B HB). Qed.
Lemma r_sm7 : forall fx0 : YK11.FPState,
  @RtStack.astack_malloc_sz_realizes fx0 rc SEGS B (SIG CS___asan_stack_malloc_7) 7.
Proof. exact (fun fx0 => @RtClosed.cmd_stack_malloc7_contract_closed fx0 rc B HB). Qed.
Lemma r_sf5 : forall fx0 : YK11.FPState,
  @RtStack.astack_free_cls_realizes fx0 rc SEGS B (SIG CS___asan_stack_free_5) 5.
Proof. exact (fun fx0 => @RtClosed.cmd_stack_free5_contract_closed fx0 rc B HB). Qed.
Lemma r_sf7 : forall fx0 : YK11.FPState,
  @RtStack.astack_free_realizes fx0 rc SEGS B (SIG CS___asan_stack_free_7) 7.
Proof. exact (fun fx0 => @RtClosed.cmd_stack_free7_contract_closed fx0 rc B HB). Qed.
Lemma r_sh00 : forall fx0 : YK11.FPState,
  @RtShadow.aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_00) 0.
Proof. exact (fun fx0 => @RtClosed.cmd_set_shadow_00_closed fx0 rc B HB). Qed.
Lemma r_shf5 : forall fx0 : YK11.FPState,
  @RtShadow.aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_f5) 0xf5.
Proof. exact (fun fx0 => @RtClosed.cmd_set_shadow_f5_closed fx0 rc B HB). Qed.
Lemma r_shf8 : forall fx0 : YK11.FPState,
  @RtShadow.aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_f8) 0xf8.
Proof. exact (fun fx0 => @RtClosed.cmd_set_shadow_f8_closed fx0 rc B HB). Qed.

(** * The program functions, callees first *)
(* is_instance_verb: tis_instance_verb_closed (IsInstanceVerbClosed.v:37) *)
Lemma cl_is_instance_verb : forall fx0 : YK11.FPState,
  @A.Prog.is_instance_verb_c.tis_instance_verb_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.IsInstanceVerbClosed.tis_instance_verb_closed fx0 rc B MT HB r_strcspn r_strncmp).
Qed.
(* rec_calls_free: trec_calls_free_closed (CmdA9Closed.v:60) *)
Lemma cl_rec_calls_free : forall fx0 : YK11.FPState,
  @A.Prog.rec_calls_free_c.trec_calls_free_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.CmdA9Closed.trec_calls_free_closed fx0 rc B MT HB MTL r_free4).
Qed.
(* xstrdup: txstrdup_closed (CmdA9Closed.v:50) *)
Lemma cl_xstrdup : forall fx0 : YK11.FPState, @A.Prog.xstrdup_c.txstrdup_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.CmdA9Closed.txstrdup_closed fx0 rc B MT HB r_malloc4 r_memcpy r_strlen).
Qed.
(* mix_call: tmix_call_closed (MixCallClosed.v:36) *)
Lemma cl_mix_call : forall fx0 : YK11.FPState, @A.Prog.mix_call_c.tmix_call_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.MixCallClosed.tmix_call_closed fx0 rc B MT HB r_strlen).
Qed.
(* hand_back: thand_back_closed (HandBackClosed.v:38) *)
Lemma cl_hand_back : forall fx0 : YK11.FPState, @A.Prog.hand_back_c.thand_back_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.HandBackClosed.thand_back_closed fx0 rc B MT HB MTL cl_xstrdup r_free4 r_free_null4).
Qed.
(* answer_code: tanswer_code_closed (RecBClosed.v:163) *)
Lemma cl_answer_code : forall fx0 : YK11.FPState, @A.Prog.answer_code_c.tanswer_code_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.RecBClosed.tanswer_code_closed fx0 rc B MT HB MTL MTFL cl_hand_back r_free4 r_sm1
  r_snprintf).
Qed.
(* pins_set: tpins_set_closed (RecBClosed.v:374) *)
Lemma cl_pins_set : forall fx0 : YK11.FPState, @A.Prog.pins_set_c.tpins_set_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.RecBClosed.tpins_set_closed fx0 rc B MT HB MTL cl_rec_calls_free cl_xstrdup cl_mix_call
  cl_answer_code).
Qed.
(* lv2_refusals_forget: tlv2_refusals_forget_closed (RecBClosed.v:310) *)
Lemma cl_lv2_refusals_forget : forall fx0 : YK11.FPState,
  @A.Prog.lv2_refusals_forget_c.tlv2_refusals_forget_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.RecBClosed.tlv2_refusals_forget_closed fx0 rc B MT HB MTL cl_rec_calls_free cl_xstrdup
  cl_mix_call).
Qed.
(* pin_set_words: tpin_set_words_closed (PinSetWordsClosed.v:37) *)
Lemma cl_pin_set_words : forall fx0 : YK11.FPState,
  @A.Prog.pin_set_words_c.tpin_set_words_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.PinSetWordsClosed.tpin_set_words_closed fx0 rc B MT HB MTL cl_pins_set
  cl_lv2_refusals_forget r_strlen r_strncmp).
Qed.
(* number: tnumber_closed (NumberClosed.v:38) *)
Lemma cl_number : forall fx0 : YK11.FPState, @A.Prog.number_c.tnumber_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.NumberClosed.tnumber_closed fx0 rc B MT HB r_sm0 r_strtol).
Qed.
(* arg_i: targ_i_closed (ArgIClosed.v:42) *)
Lemma cl_arg_i : forall fx0 : YK11.FPState, @A.Prog.arg_i_c.targ_i_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.ArgIClosed.targ_i_closed fx0 rc B MT HB MTL MTFL cl_xstrdup r_sm0 r_snprintf).
Qed.
(* rec_shape_of: trec_shape_of_closed (CmdReplyWalksClosed.v:90) *)
Lemma cl_rec_shape_of : forall fx0 : YK11.FPState, @A.Prog.rec_shape_of_c.trec_shape_of_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.CmdReplyWalksClosed.trec_shape_of_closed fx0 rc B MT HB r_strlen r_bcmp).
Qed.
(* answer: tanswer_closed (AnswerClosed.v:44) *)
Lemma cl_answer : forall fx0 : YK11.FPState, @A.Prog.answer_c.tanswer_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.AnswerClosed.tanswer_closed fx0 rc B MT HB MTL MTFL cl_hand_back cl_mix_call r_sm7 r_sf7
  r_sh00 r_shf8 r_snprintf).
Qed.
(* sup_chain: tsup_chain_closed (RecBClosed.v:396) *)
Lemma cl_sup_chain : forall fx0 : YK11.FPState, @A.Prog.sup_chain_c.tsup_chain_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.RecBClosed.tsup_chain_closed fx0 rc B MT HB MTL cl_rec_calls_free cl_arg_i cl_xstrdup
  cl_rec_shape_of cl_answer r_malloc4 r_free4 r_sprintf).
Qed.
(* sup_resp: tsup_resp_closed (SupRespClosed.v:41) *)
Lemma cl_sup_resp : forall fx0 : YK11.FPState, @A.Prog.sup_resp_c.tsup_resp_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.SupRespClosed.tsup_resp_closed fx0 rc B MT HB MTFL cl_xstrdup r_sm1 r_snprintf).
Qed.
(* chain_words: tchain_words_closed (ChainWordsClosed.v:40) *)
Lemma cl_chain_words : forall fx0 : YK11.FPState, @A.Prog.chain_words_c.tchain_words_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.ChainWordsClosed.tchain_words_closed fx0 rc B MT HB MTL MTFL cl_number cl_sup_chain
  cl_sup_resp r_sm3 SMP ASF FFL r_shf5).
Qed.
(* verb_is: tverb_is_closed (VerbIsClosed.v:36) *)
Lemma cl_verb_is : forall fx0 : YK11.FPState, @A.Prog.verb_is_c.tverb_is_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.VerbIsClosed.tverb_is_closed fx0 rc B MT HB r_strcspn r_strncmp).
Qed.
(* socket_send: tsocket_send_closed (RecBClosed.v:140) *)
Lemma cl_socket_send : forall fx0 : YK11.FPState, @A.Prog.socket_send_c.tsocket_send_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.RecBClosed.tsocket_send_closed fx0 rc B MT HB MTL r_malloc4 r_free4 r_free_null4 r_memset
  r_memcpy).
Qed.
(* reply: treply_closed (ReplyClosed.v:38) *)
Lemma cl_reply : forall fx0 : YK11.FPState, @A.Prog.reply_c.treply_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.ReplyClosed.treply_closed fx0 rc B MT HB MTL cl_socket_send r_strlen r_free4).
Qed.
(* descriptors_add: tdescriptors_add_closed (RecBClosed.v:342) *)
Lemma cl_descriptors_add : forall fx0 : YK11.FPState,
  @A.Prog.descriptors_add_c.tdescriptors_add_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.RecBClosed.tdescriptors_add_closed fx0 rc B MT HB MTL cl_rec_calls_free cl_xstrdup
  cl_mix_call).
Qed.
(* descriptors_get: tdescriptors_get_closed (RecBClosed.v:352) *)
Lemma cl_descriptors_get : forall fx0 : YK11.FPState,
  @A.Prog.descriptors_get_c.tdescriptors_get_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.RecBClosed.tdescriptors_get_closed fx0 rc B MT HB MTL cl_rec_calls_free cl_xstrdup
  cl_rec_shape_of cl_answer).
Qed.
(* descriptors_panel_get: tdescriptors_panel_get_closed (RecBClosed.v:331) *)
Lemma cl_descriptors_panel_get : forall fx0 : YK11.FPState,
  @A.Prog.descriptors_panel_get_c.tdescriptors_panel_get_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.RecBClosed.tdescriptors_panel_get_closed fx0 rc B MT HB MTL cl_rec_calls_free cl_xstrdup
  cl_rec_shape_of cl_answer).
Qed.
(* pins_clear: tpins_clear_closed (RecBClosed.v:385) *)
Lemma cl_pins_clear : forall fx0 : YK11.FPState, @A.Prog.pins_clear_c.tpins_clear_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.RecBClosed.tpins_clear_closed fx0 rc B MT HB MTL cl_rec_calls_free cl_xstrdup cl_mix_call
  cl_answer_code).
Qed.
(* sup_add: tsup_add_closed (SupAddClosed.v:43) *)
Lemma cl_sup_add : forall fx0 : YK11.FPState, @A.Prog.sup_add_c.tsup_add_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.SupAddClosed.tsup_add_closed fx0 rc B MT HB MTL MTFL cl_rec_calls_free cl_xstrdup
  cl_arg_i cl_mix_call cl_hand_back cl_answer r_sm1 r_snprintf).
Qed.
(* sup_after_reply: tsup_after_reply_closed (RecBClosed.v:210) *)
Lemma cl_sup_after_reply : forall fx0 : YK11.FPState,
  @A.Prog.sup_after_reply_c.tsup_after_reply_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.RecBClosed.tsup_after_reply_closed fx0 rc B MT HB MTL cl_rec_calls_free cl_arg_i
  cl_xstrdup).
Qed.
(* rec_canonical: trec_canonical_closed (CmdA9Closed.v:75) *)
Lemma cl_rec_canonical : forall fx0 : YK11.FPState,
  @A.Prog.rec_canonical_c.trec_canonical_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.CmdA9Closed.trec_canonical_closed fx0 rc B MT HB r_malloc4).
Qed.
(* arg_line: targ_line_closed (ArgLineClosed.v:38) *)
Lemma cl_arg_line : forall fx0 : YK11.FPState, @A.Prog.arg_line_c.targ_line_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.ArgLineClosed.targ_line_closed fx0 rc B MT HB MTL cl_rec_canonical r_strlen).
Qed.
(* sup_broadcast: tsup_broadcast_closed (SupBroadcastClosed.v:37) *)
Lemma cl_sup_broadcast : forall fx0 : YK11.FPState,
  @A.Prog.sup_broadcast_c.tsup_broadcast_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.SupBroadcastClosed.tsup_broadcast_closed fx0 rc B MT HB MTL cl_rec_calls_free cl_arg_line
  cl_answer).
Qed.
(* sup_call: tsup_call_closed (SupCallClosed.v:38) *)
Lemma cl_sup_call : forall fx0 : YK11.FPState, @A.Prog.sup_call_c.tsup_call_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.SupCallClosed.tsup_call_closed fx0 rc B MT HB MTL cl_rec_calls_free cl_arg_i cl_arg_line
  cl_answer).
Qed.
(* sup_chain_clear: tsup_chain_clear_closed (RecBClosed.v:187) *)
Lemma cl_sup_chain_clear : forall fx0 : YK11.FPState,
  @A.Prog.sup_chain_clear_c.tsup_chain_clear_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.RecBClosed.tsup_chain_clear_closed fx0 rc B MT HB MTL cl_arg_i cl_rec_shape_of cl_answer
  cl_rec_calls_free).
Qed.
(* sup_connect: tsup_connect_closed (SupConnectClosed.v:38) *)
Lemma cl_sup_connect : forall fx0 : YK11.FPState, @A.Prog.sup_connect_c.tsup_connect_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.SupConnectClosed.tsup_connect_closed fx0 rc B MT HB MTL cl_rec_calls_free cl_xstrdup
  cl_arg_line cl_answer).
Qed.
(* sup_host_setting: tsup_host_setting_closed (RecBClosed.v:238) *)
Lemma cl_sup_host_setting : forall fx0 : YK11.FPState,
  @A.Prog.sup_host_setting_c.tsup_host_setting_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.RecBClosed.tsup_host_setting_closed fx0 rc B MT HB MTL cl_rec_calls_free cl_arg_line
  cl_arg_i cl_xstrdup cl_mix_call r_malloc4 r_free4 r_strlen r_strcat).
Qed.
(* sup_instance_info: tsup_instance_info_closed (RecBClosed.v:176) *)
Lemma cl_sup_instance_info : forall fx0 : YK11.FPState,
  @A.Prog.sup_instance_info_c.tsup_instance_info_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.RecBClosed.tsup_instance_info_closed fx0 rc B MT HB MTL cl_rec_calls_free cl_arg_i
  cl_rec_shape_of cl_answer).
Qed.
(* sup_instance_verb: tsup_instance_verb_closed (RecBClosed.v:220) *)
Lemma cl_sup_instance_verb : forall fx0 : YK11.FPState,
  @A.Prog.sup_instance_verb_c.tsup_instance_verb_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.RecBClosed.tsup_instance_verb_closed fx0 rc B MT HB MTL cl_rec_calls_free cl_arg_line
  cl_arg_i cl_rec_shape_of cl_answer r_strspn r_strcspn).
Qed.
(* sup_lv2_worker_set: tsup_lv2_worker_set_closed (RecBClosed.v:267) *)
Lemma cl_sup_lv2_worker_set : forall fx0 : YK11.FPState,
  @A.Prog.sup_lv2_worker_set_c.tsup_lv2_worker_set_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.RecBClosed.tsup_lv2_worker_set_closed fx0 rc B MT HB MTL cl_rec_calls_free cl_xstrdup
  cl_rec_shape_of cl_answer).
Qed.
(* sup_pin_accept: tsup_pin_accept_closed (RecBClosed.v:256) *)
Lemma cl_sup_pin_accept : forall fx0 : YK11.FPState,
  @A.Prog.sup_pin_accept_c.tsup_pin_accept_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.RecBClosed.tsup_pin_accept_closed fx0 rc B MT HB MTL cl_rec_calls_free cl_xstrdup
  cl_rec_shape_of cl_answer).
Qed.
(* sup_policy_set: tsup_policy_set_closed (RecBClosed.v:278) *)
Lemma cl_sup_policy_set : forall fx0 : YK11.FPState,
  @A.Prog.sup_policy_set_c.tsup_policy_set_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.RecBClosed.tsup_policy_set_closed fx0 rc B MT HB MTL cl_rec_calls_free cl_xstrdup
  cl_rec_shape_of cl_answer).
Qed.
(* sup_pool_config: tsup_pool_config_closed (RecBClosed.v:198) *)
Lemma cl_sup_pool_config : forall fx0 : YK11.FPState,
  @A.Prog.sup_pool_config_c.tsup_pool_config_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.RecBClosed.tsup_pool_config_closed fx0 rc B MT HB MTL cl_rec_calls_free cl_xstrdup
  cl_arg_i cl_rec_shape_of cl_answer).
Qed.
(* sup_quarantine_clear: tsup_quarantine_clear_closed (RecBClosed.v:320) *)
Lemma cl_sup_quarantine_clear : forall fx0 : YK11.FPState,
  @A.Prog.sup_quarantine_clear_c.tsup_quarantine_clear_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.RecBClosed.tsup_quarantine_clear_closed fx0 rc B MT HB MTL cl_rec_calls_free cl_xstrdup
  cl_rec_shape_of cl_answer).
Qed.
(* sup_remove: tsup_remove_closed (SupRemoveClosed.v:37) *)
Lemma cl_sup_remove : forall fx0 : YK11.FPState, @A.Prog.sup_remove_c.tsup_remove_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.SupRemoveClosed.tsup_remove_closed fx0 rc B MT HB MTL cl_rec_calls_free cl_arg_i
  cl_answer).
Qed.
(* sup_remove_all: tsup_remove_all_closed (SupRemoveAllRefitClosed.v:39) *)
Lemma cl_sup_remove_all : forall fx0 : YK11.FPState,
  @A.Prog.sup_remove_all_c.tsup_remove_all_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.SupRemoveAllRefitClosed.tsup_remove_all_closed fx0 rc B MT HB MTL cl_rec_calls_free
  cl_answer).
Qed.
(* sup_reply_code: tsup_reply_code_closed (CmdReplyWalksClosed.v:69) *)
Lemma cl_sup_reply_code : forall fx0 : YK11.FPState,
  @A.Prog.sup_reply_code_c.tsup_reply_code_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.CmdReplyWalksClosed.tsup_reply_code_closed fx0 rc B MT HB r_strncmp r_atoi).
Qed.
(* sup_reset: tsup_reset_closed (RecBClosed.v:363) *)
Lemma cl_sup_reset : forall fx0 : YK11.FPState, @A.Prog.sup_reset_c.tsup_reset_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.RecBClosed.tsup_reset_closed fx0 rc B MT HB MTL cl_rec_calls_free cl_xstrdup
  cl_rec_shape_of cl_answer).
Qed.
(* sup_worker_env: tsup_worker_env_closed (RecBClosed.v:289) *)
Lemma cl_sup_worker_env : forall fx0 : YK11.FPState,
  @A.Prog.sup_worker_env_c.tsup_worker_env_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.RecBClosed.tsup_worker_env_closed fx0 rc B MT HB MTL cl_rec_calls_free cl_xstrdup
  cl_rec_shape_of cl_answer).
Qed.
(* sup_worker_list: tsup_worker_list_closed (RecBClosed.v:300) *)
Lemma cl_sup_worker_list : forall fx0 : YK11.FPState,
  @A.Prog.sup_worker_list_c.tsup_worker_list_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.RecBClosed.tsup_worker_list_closed fx0 rc B MT HB MTL cl_rec_calls_free cl_rec_shape_of
  cl_answer).
Qed.
(* verbs_receive: tverbs_receive_closed (VerbsReceiveClosed.v:49) *)
Lemma cl_verbs_receive : forall fx0 : YK11.FPState,
  @A.Prog.verbs_receive_c.tverbs_receive_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.VerbsReceiveClosed.tverbs_receive_closed fx0 rc B MT RtAPI.PC_STRDUP_RA0
  RtAPI.PC_STRNDUP_RA0 HB MTL MTFL cl_descriptors_add cl_descriptors_get cl_descriptors_panel_get cl_is_instance_verb
  cl_lv2_refusals_forget cl_number cl_pins_clear cl_reply cl_sup_add cl_sup_after_reply cl_sup_broadcast cl_sup_call
  cl_sup_chain_clear cl_sup_connect cl_sup_host_setting cl_sup_instance_info cl_sup_instance_verb
  cl_sup_lv2_worker_set cl_sup_pin_accept cl_sup_policy_set cl_sup_pool_config cl_sup_quarantine_clear cl_sup_remove
  cl_sup_remove_all cl_sup_reply_code cl_sup_reset cl_sup_resp cl_sup_worker_env cl_sup_worker_list cl_verb_is
  cl_chain_words cl_pin_set_words r_sm4 r_sh00 r_shf5 r_shf8 r_strlen r_strcmp r_strncmp r_strcspn r_strtok_r r_atoi
  r_strdup4 r_strndup4 r_free4).
Qed.
(* rec_calls_equal: trec_calls_equal_closed (CmdA9Closed.v:68) *)
Lemma cl_rec_calls_equal : forall fx0 : YK11.FPState,
  @A.Prog.rec_calls_equal_c.trec_calls_equal_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.CmdA9Closed.trec_calls_equal_closed fx0 rc B MT HB r_strcmp).
Qed.
(* rec_calls_copy: trec_calls_copy_closed (CmdA9Closed.v:92) *)
Lemma cl_rec_calls_copy : forall fx0 : YK11.FPState,
  @A.Prog.rec_calls_copy_c.trec_calls_copy_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.CmdA9Closed.trec_calls_copy_closed fx0 rc B MT HB MTL cl_xstrdup).
Qed.
(* rec_clear: trec_clear_closed (RecBClosed.v:152) *)
Lemma cl_rec_clear : forall fx0 : YK11.FPState, @A.Prog.rec_clear_c.trec_clear_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.RecBClosed.trec_clear_closed fx0 rc B MT HB MTL cl_rec_calls_free r_free4 r_free_null4
  r_memset).
Qed.
(* rec_code_declared: trec_code_declared_closed (CmdReplyWalksClosed.v:46) *)
Lemma cl_rec_code_declared : forall fx0 : YK11.FPState,
  @A.Prog.rec_code_declared_c.trec_code_declared_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.CmdReplyWalksClosed.trec_code_declared_closed fx0 rc B MT HB).
Qed.
(* check_words_pin_set: pb_check_words_pin_set (check_words_pin_set.v:628) *)
Lemma cl_check_words_pin_set : forall fx0 : YK11.FPState,
  @A.Prog.check_words_pin_set_c.tcwps_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.check_words_pin_set.pb_check_words_pin_set fx0 rc SK0 PB_cmd B MT LAWS TL (r_strcmp fx0)
  (r_strncmp fx0) cpc_grec_zs k_tailq k_cw_lits).
Qed.
(* check_words_chain: tcheck_words_chain_closed (CheckWordsChainClosed.v:35) *)
Lemma cl_check_words_chain : forall fx0 : YK11.FPState,
  @A.Prog.check_words_chain_c.tcheck_words_chain_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.CheckWordsChainClosed.tcheck_words_chain_closed fx0 rc B MT HB r_sm4 r_sh00 r_shf5 r_shf8
  r_atoi r_snprintf r_strcmp).
Qed.
(* check_words_add: tcheck_words_add_closed (CheckWordsAddClosed.v:34) *)
Lemma cl_check_words_add : forall fx0 : YK11.FPState,
  @A.Prog.check_words_add_c.tcheck_words_add_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.CheckWordsAddClosed.tcheck_words_add_closed fx0 rc B MT HB r_strcmp r_strncmp).
Qed.
(* joined: tjoined_closed (CmdA9Closed.v:82) *)
Lemma cl_joined : forall fx0 : YK11.FPState, @A.Prog.joined_c.tjoined_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.CmdA9Closed.tjoined_closed fx0 rc B MT HB r_malloc4 r_memcpy r_strlen).
Qed.
(* syntax_reply_matches: tsyntax_reply_matches_closed (CmdReplyWalksClosed.v:80) *)
Lemma cl_syntax_reply_matches : forall fx0 : YK11.FPState,
  @A.Prog.syntax_reply_matches_c.tsyntax_reply_matches_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.CmdReplyWalksClosed.tsyntax_reply_matches_closed fx0 rc B MT HB r_strcspn r_bcmp).
Qed.
(* check_reply_answer: tcheck_reply_answer_closed (CmdReplyWalksClosed.v:53) *)
Lemma cl_check_reply_answer : forall fx0 : YK11.FPState,
  @A.Prog.check_reply_answer_c.tcheck_reply_answer_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.CmdReplyWalksClosed.tcheck_reply_answer_closed fx0 rc B MT HB cl_sup_reply_code r_strcmp
  r_strcspn r_strncmp).
Qed.
(* send_message: tsend_message_closed (CmdReplyWalksClosed.v:99) *)
Lemma cl_send_message : forall fx0 : YK11.FPState, @A.Prog.send_message_c.tsend_message_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.CmdReplyWalksClosed.tsend_message_closed fx0 rc B MT HB MTL MTFL cl_rec_clear
  cl_verbs_receive r_sm1 r_malloc4 r_free4 r_memcpy).
Qed.
(* check_round_trip: tcheck_round_trip_closed (CmdA9Closed.v:100) *)
Lemma cl_check_round_trip : forall fx0 : YK11.FPState,
  @A.Prog.check_round_trip_c.tcheck_round_trip_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.CmdA9Closed.tcheck_round_trip_closed fx0 rc B MT HB MTL MTFL cl_send_message cl_joined
  cl_rec_calls_copy cl_rec_calls_equal cl_rec_calls_free RtAPI.PC_STRDUP_RA0 r_free4 r_strdup4 r_strcmp r_sm5 r_sf5
  r_sh00 r_shf8).
Qed.
(* check_refusal: tcheck_refusal_closed (CheckRefusalClosed.v:38) *)
Lemma cl_check_refusal : forall fx0 : YK11.FPState,
  @A.Prog.check_refusal_c.tcheck_refusal_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.CheckRefusalClosed.tcheck_refusal_closed fx0 rc B MT HB cl_sup_reply_code).
Qed.
(* check_words: tcheck_words_closed (CheckWordsClosed.v:43) *)
Lemma cl_check_words : forall fx0 : YK11.FPState, @A.Prog.check_words_c.tcheck_words_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.CheckWordsClosed.tcheck_words_closed fx0 rc B MT HB MTL MTFL cl_joined cl_check_words_add
  cl_check_words_chain cl_check_words_pin_set r_free4 r_sm0 r_strspn r_strcspn r_strcmp r_atoi r_snprintf).
Qed.
(* check_arity: tcheck_arity_closed (CheckArityClosed.v:36) *)
Lemma cl_check_arity : forall fx0 : YK11.FPState, @A.Prog.check_arity_c.tcheck_arity_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.CheckArityClosed.tcheck_arity_closed fx0 rc B MT HB r_strcmp r_strcspn r_strncmp r_bcmp).
Qed.
(* check_reply: tcheck_reply_closed (CmdReplyWalksClosed.v:116) *)
Lemma cl_check_reply : forall fx0 : YK11.FPState, @A.Prog.check_reply_c.tcheck_reply_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.CmdReplyWalksClosed.tcheck_reply_closed fx0 rc B MT HB cl_check_reply_answer
  cl_sup_reply_code cl_rec_code_declared cl_rec_shape_of cl_syntax_reply_matches r_sm1 r_memchr r_strlen r_snprintf
  r_strcmp).
Qed.

(** * The entry, and CmdLibX.v's interface with it *)
(* LLVMFuzzerTestOneInput: tLLVMFuzzerTestOneInput_closed (LtoiClosed.v:44); this is CmdLibX.v:155's HLTOI *)
Theorem cmd_ltoi_all : forall fx0 : YK11.FPState,
  @A.Prog.LLVMFuzzerTestOneInput_c.tLLVMFuzzerTestOneInput_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @A.Prog.LtoiClosed.tLLVMFuzzerTestOneInput_closed fx0 rc B MT HB MTL MTFL cl_rec_clear
  cl_send_message cl_check_reply cl_check_arity cl_check_words cl_check_refusal cl_check_round_trip r_malloc4 r_free4
  r_memcpy r_memset r_strnlen r_strspn r_strcspn).
Qed.
Theorem cmd_lib_x_final : forall j : nat,
  @tfib_lib_contract_x_all rc CmdShape.cmd_shape B MT CmdLibX.XL0 CmdLibX.XL0 CMD_RLO CMD_RHI GI_cmdA j.
Proof. exact (fun j => @CmdLibX.cmd_lib_x_closed rc cmd_ltoi_all j). Qed.
End closed.
