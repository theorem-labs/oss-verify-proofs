(* The 23 recorder-group-B ASan walks of plugin-hostd/fuzz_command (fuzz_command.asan), closed at the pinned image
   (lib/A/Prog/CmdImg.v's instance PB_cmd, whose segments are tfibsegs, and the sink head AE2k.tfib_sink_head):
   `t<fn>_closed` proves the same `t<fn>_spec B MT` as the walk's `t<fn>_holds`, from HB, MTL (answer_code also MTLF)
   and the statement's own callee and runtime contracts, each at every FP state.
   - the kit's closers give every other walk hypothesis: LAWS is the core's AR_laws_ok, IMG is CmdRecImg's
     cmd_img_facts_tfib, PRW is CmdRecRest's cmd_prw_tfib, TL is cmd_palib, TLF is cmd_palibf, VOBJS is
     cmd_val_objs_PB, SIGP is cmd_sig_prog_PB, answer_code's AFREE_LAW is cmd_astack_free_law, and the record's
     image facts are CmdRecRest's, CmdRecRo's and CmdRecCells' lemmas at IMG;
   - the walks' named forms that differ from the kit lemma's are the adapters crb_* below: cmd_prog_writable (an
     AR state and recb_PG's (start, length) ranges, where PROG_WRITABLE has cmd_PG's (lo, hi) ranges),
     cmd_heap_tail_vis ([p, p + n) where the kit's has [p, p + req_size n)), ZSH_lit_<hex> / HULL_lit_<hex>
     (cmd_addressable_chk / cmd_hull_vis_chk with one closed check each). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YM05 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI16 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0d_tail.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m AF0l AB1v AB13.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtString RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdImg CmdBase CmdRo CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdObj RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require
answer_c answer_code_c arg_i_c arg_line_c descriptors_add_c descriptors_get_c descriptors_panel_get_c hand_back_c
lv2_refusals_forget_c mix_call_c pins_clear_c pins_set_c rec_calls_free_c rec_clear_c rec_shape_of_c socket_send_c
sup_after_reply_c sup_chain_c sup_chain_clear_c sup_host_setting_c sup_instance_info_c sup_instance_verb_c
sup_lv2_worker_set_c sup_pin_accept_c sup_policy_set_c sup_pool_config_c sup_quarantine_clear_c sup_reset_c
sup_worker_env_c sup_worker_list_c xstrdup_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require
socket_send rec_clear answer_code sup_instance_info sup_chain_clear sup_pool_config sup_after_reply
sup_instance_verb sup_host_setting sup_pin_accept sup_lv2_worker_set sup_policy_set sup_worker_env sup_worker_list
lv2_refusals_forget sup_quarantine_clear descriptors_panel_get descriptors_add descriptors_get sup_reset pins_set
pins_clear sup_chain_s8.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(** * Adapters: the walks' forms of the kit's facts *)
(* recb_PG's (start, length) ranges lie in cmd_PG's (lo, hi) ranges *)
Lemma crb_pg_in : forall a, Exists (in_zr a) RecBLemmas.recb_PG -> inFP cmd_PG a.
Proof.
intros a Ha. apply Exists_exists in Ha as (r & Hr & Ha). unfold RecBLemmas.recb_PG in Hr. unfold in_zr in Ha.
destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Ha; unfold RecInv.REC_SIZE, RecInv.SC_SIZE in Ha.
- exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; lia].
- exists (A_REC_SPILL, A_REC_SPILL + 56). split; [right; left; reflexivity | cbn [fst snd]; lia].
- exists (A_G_QUITTING, A_G_QUITTING + 4). split; [right; right; left; reflexivity | cbn [fst snd]; lia].
Qed.
(* the closed checks of the literals the walks hand to a callee (ZSH_lit_<hex>, HULL_lit_<hex>) *)
Lemma crb_addr_21d00 : cmd_addr_b 0x21d00 8 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma crb_hull_21d00 : cmd_hull_b 0x21d00 8 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma crb_addr_21d60 : cmd_addr_b 0x21d60 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma crb_hull_21d60 : cmd_hull_b 0x21d60 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma crb_addr_21ee0 : cmd_addr_b 0x21ee0 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma crb_hull_21ee0 : cmd_hull_b 0x21ee0 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma crb_addr_21f00 : cmd_addr_b 0x21f00 3 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma crb_hull_21f00 : cmd_hull_b 0x21f00 3 = true.
Proof. vm_compute. reflexivity. Qed.

(* Every adapter is closed over `segs B LAWS HB`, cmd_prog_writable's over `segs B LAWS HB PRW`, as the kit's
   lemmas are. *)
Section adapt. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis HB : CmdBSyms B.
(* cmd_heap_tail_vis (a named walk hypothesis): a requested byte of a live block, by the kit's cmd_heap_tail_vis *)
Lemma crb_heap_tail_vis : forall ly S (W : world segs) mem md p n e, AR segs B ly S W mem md ->
In (p, n) (ablocks B ly S) -> p <= e < p + n -> atail_vis segs W mem e.
Proof using LAWS HB.
intros ly S W mem md p n e HAR Hin He. pose proof (crf_req_size_ge n) as Hq.
exact (CmdRecImg.cmd_heap_tail_vis segs B LAWS HB ly S W mem md p n e HAR Hin ltac:(lia)).
Qed.
(* ZSH_lit_<hex> / HULL_lit_<hex>: a literal range whose closed check holds, at every AR state *)
Lemma crb_zsh : forall a n, cmd_addr_b a n = true -> forall ly S (W : world segs) mem md, AR segs B ly S W mem md ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n.
Proof using LAWS HB.
intros a n H ly S W mem md HAR. exact (cmd_addressable_chk segs B LAWS HB ly S W mem md a n HAR H).
Qed.
Lemma crb_hull : forall a n, cmd_hull_b a n = true -> forall ly S (W : world segs) mem md, AR segs B ly S W mem md ->
shadow_hull_vis (aview segs (w_H W) mem) a n.
Proof using LAWS HB.
intros a n H ly S W mem md HAR. exact (cmd_hull_vis_chk segs B LAWS HB ly S W mem md a n HAR H).
Qed.
Hypothesis PRW : prog_rw segs B.
(* cmd_prog_writable: a byte of the program's statics is writable (PROG_WRITABLE) *)
Lemma crb_prog_writable : forall ly S (W : world segs) mem md a, AR segs B ly S W mem md ->
Exists (in_zr a) RecBLemmas.recb_PG -> writable_at segs (mrestrict (w_H W) mem) a.
Proof using LAWS HB PRW.
intros ly S W mem md a _ Ha. exact (PROG_WRITABLE segs B LAWS HB PRW (mrestrict (w_H W) mem) a (crb_pg_in a Ha)).
Qed.
End adapt.

(** * The corollaries, at the pinned image *)
Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance AE2k.tfib_sink_head | 0.
#[local] Existing Instance CmdImg.PB_cmd | 0.
#[local] Notation SK0 := AE2k.tfib_sink_head.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PB_cmd).
#[local] Notation SIG c := (@pa_sigma _ cmd_listing PB_cmd c).
Variable B : asyms.
Variable MT : YC5d.ameter_ops.
(* the allocator record and the meter's laws; answer_code's side-stack frame
   also needs the meter's frame laws (MTLF) *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : YC5d.ameter_laws MT.
Hypothesis MTLF : YC5d.ameter_fs_laws MT.
(* the kit's closers at the pinned image: the record's laws (LAWS), image facts (IMG) and read-write window (PRW),
   and each walk hypothesis they give *)
#[local] Notation LAWS := (YG0q.AR_laws_ok SEGS B).
#[local] Notation IMG := (CmdRecImg.cmd_img_facts_tfib B HB).
#[local] Notation k_tl := (CmdRecRest.cmd_palib B HB).
#[local] Notation k_vobjs := CmdRecRest.cmd_val_objs_PB.
#[local] Notation k_sig := CmdRecRest.cmd_sig_prog_PB.
#[local] Notation k_pimg := (CmdRecRest.cmd_prog_img SEGS B LAWS HB IMG).
#[local] Notation k_pwr := (crb_prog_writable SEGS B LAWS HB (CmdRecRest.cmd_prw_tfib B HB)).
#[local] Notation k_apart := (CmdRecRest.cmd_ro_prog_apart SEGS B LAWS HB IMG).
#[local] Notation k_rook := (CmdRecRo.cmd_ro_ok_of_aro SEGS B LAWS HB IMG).
#[local] Notation k_rob := (CmdRecRo.ROB SEGS B LAWS HB IMG).
#[local] Notation k_relro := (CmdRecRo.RELRO_IMG SEGS B LAWS HB IMG).
#[local] Notation k_roin := (CmdRecRo.CMD_RO_IN SEGS B LAWS HB IMG).
#[local] Notation k_tail := (crb_heap_tail_vis SEGS B LAWS HB).
#[local] Notation k_cells := (CmdRecCells.cmd_rec_cells SEGS B LAWS HB IMG).
#[local] Notation k_atk := (CmdRecRest.cmd_atail_kept SEGS B LAWS HB IMG).

Theorem tsocket_send_closed
  (AMALLOC4 : forall fx0 : YK11.FPState, @YC5d.amalloc04_rule fx0 rc SK0 SEGS B MT)
  (AFREE4 : forall fx0 : YK11.FPState, @YC5d.afree04_rule fx0 rc SK0 SEGS B MT)
  (AFREE_NULL4 : forall fx0 : YK11.FPState, @YC5d.afree_null04_rule fx0 rc SK0 SEGS B MT)
  (AMEMSET : forall fx0 : YK11.FPState, @YG0d.aintrin_realizes fx0 rc SEGS B YG0d.OSet (SIG CmdSyms.CS___asan_memset))
  (AMEMCPY : forall fx0 : YK11.FPState, @YG0d.aintrin_realizes fx0 rc SEGS B YG0d.OCpy (SIG CmdSyms.CS___asan_memcpy)) :
  socket_send_c.tsocket_send_spec B MT.
Proof.
exact (socket_send.tsocket_send_holds B MT AMALLOC4 AFREE4 AFREE_NULL4 AMEMSET AMEMCPY k_vobjs HB k_tl MTL k_pimg
  k_pwr).
Qed.

Theorem trec_clear_closed
  (TRCF : forall fx0 : YK11.FPState, @rec_calls_free_c.trec_calls_free_spec fx0 rc SK0 PB_cmd B MT)
  (AFREE4 : forall fx0 : YK11.FPState, @YC5d.afree04_rule fx0 rc SK0 SEGS B MT)
  (AFREE_NULL4 : forall fx0 : YK11.FPState, @YC5d.afree_null04_rule fx0 rc SK0 SEGS B MT)
  (AMEMSET : forall fx0 : YK11.FPState, @YG0d.aintrin_realizes fx0 rc SEGS B YG0d.OSet (SIG CmdSyms.CS___asan_memset)) :
  rec_clear_c.trec_clear_spec B MT.
Proof.
exact (rec_clear.trec_clear_holds B MT HB k_tl MTL TRCF AFREE4 AFREE_NULL4 AMEMSET k_vobjs k_pimg k_pwr k_apart
  k_sig).
Qed.

Theorem tanswer_code_closed
  (THAND_BACK : forall fx0 : YK11.FPState, @hand_back_c.thand_back_spec fx0 rc SK0 PB_cmd B MT)
  (AFREE4 : forall fx0 : YK11.FPState, @YC5d.afree04_rule fx0 rc SK0 SEGS B MT)
  (ASTACK1 : forall fx0 : YK11.FPState, @YG0d.astack_malloc_realizes fx0 rc SEGS B 1)
  (ASNPRINTF : forall fx0 : YK11.FPState,
     @RtFormat.asnprintf_realizes fx0 rc SEGS B (SIG CmdSyms.CS___interceptor_trampoline_snprintf) 0xa7098 0x6045d8) :
  answer_code_c.tanswer_code_spec B MT.
Proof.
exact (answer_code.tanswer_code_holds B MT THAND_BACK AFREE4 ASTACK1 (CmdRecRest.cmd_astack_free_law B) ASNPRINTF
  k_vobjs HB k_tl (CmdRecRest.cmd_palibf B HB) MTL MTLF k_sig k_rob k_apart k_rook k_pimg
  (crb_zsh SEGS B LAWS HB 0x21d00 8 crb_addr_21d00) (crb_hull SEGS B LAWS HB 0x21d00 8 crb_hull_21d00) k_cells IMG).
Qed.

Theorem tsup_instance_info_closed
  (TRCF : forall fx0 : YK11.FPState, @rec_calls_free_c.trec_calls_free_spec fx0 rc SK0 PB_cmd B MT)
  (TARG_I : forall fx0 : YK11.FPState, @arg_i_c.targ_i_spec fx0 rc SK0 PB_cmd B MT)
  (TREC_SHAPE_OF : forall fx0 : YK11.FPState, @rec_shape_of_c.trec_shape_of_spec fx0 rc SK0 PB_cmd B MT)
  (TANSWER : forall fx0 : YK11.FPState, @answer_c.tanswer_spec fx0 rc SK0 PB_cmd B MT) :
  sup_instance_info_c.tsup_instance_info_spec B MT.
Proof.
exact (sup_instance_info.tsup_instance_info_holds B MT TRCF TARG_I TREC_SHAPE_OF TANSWER k_vobjs k_tl HB MTL k_sig
  k_pimg k_pwr k_rob k_relro k_apart k_rook k_roin).
Qed.

Theorem tsup_chain_clear_closed
  (TARG_I : forall fx0 : YK11.FPState, @arg_i_c.targ_i_spec fx0 rc SK0 PB_cmd B MT)
  (TREC_SHAPE_OF : forall fx0 : YK11.FPState, @rec_shape_of_c.trec_shape_of_spec fx0 rc SK0 PB_cmd B MT)
  (TANSWER : forall fx0 : YK11.FPState, @answer_c.tanswer_spec fx0 rc SK0 PB_cmd B MT)
  (TRCF : forall fx0 : YK11.FPState, @rec_calls_free_c.trec_calls_free_spec fx0 rc SK0 PB_cmd B MT) :
  sup_chain_clear_c.tsup_chain_clear_spec B MT.
Proof.
exact (sup_chain_clear.tsup_chain_clear_holds B MT LAWS k_tl HB MTL k_vobjs k_pimg k_pwr k_sig TARG_I TREC_SHAPE_OF
  TANSWER k_rook k_rob k_relro k_apart k_roin TRCF).
Qed.

Theorem tsup_pool_config_closed
  (TRCF : forall fx0 : YK11.FPState, @rec_calls_free_c.trec_calls_free_spec fx0 rc SK0 PB_cmd B MT)
  (TXSTRDUP : forall fx0 : YK11.FPState, @xstrdup_c.txstrdup_spec fx0 rc SK0 PB_cmd B MT)
  (TARG_I : forall fx0 : YK11.FPState, @arg_i_c.targ_i_spec fx0 rc SK0 PB_cmd B MT)
  (TREC_SHAPE_OF : forall fx0 : YK11.FPState, @rec_shape_of_c.trec_shape_of_spec fx0 rc SK0 PB_cmd B MT)
  (TANSWER : forall fx0 : YK11.FPState, @answer_c.tanswer_spec fx0 rc SK0 PB_cmd B MT) :
  sup_pool_config_c.tsup_pool_config_spec B MT.
Proof.
exact (sup_pool_config.tsup_pool_config_holds B MT TRCF TXSTRDUP TARG_I TREC_SHAPE_OF TANSWER k_vobjs k_tl HB MTL
  k_sig k_pimg k_pwr k_rook k_rob k_relro k_apart k_roin k_tail).
Qed.

Theorem tsup_after_reply_closed
  (TRCF : forall fx0 : YK11.FPState, @rec_calls_free_c.trec_calls_free_spec fx0 rc SK0 PB_cmd B MT)
  (TARG_I : forall fx0 : YK11.FPState, @arg_i_c.targ_i_spec fx0 rc SK0 PB_cmd B MT)
  (TXSTRDUP : forall fx0 : YK11.FPState, @xstrdup_c.txstrdup_spec fx0 rc SK0 PB_cmd B MT) :
  sup_after_reply_c.tsup_after_reply_spec B MT.
Proof.
exact (sup_after_reply.tsup_after_reply_holds B MT TRCF TARG_I TXSTRDUP k_vobjs HB k_tl MTL k_sig k_pimg k_pwr
  k_apart k_rook k_rob k_relro k_tail).
Qed.

Theorem tsup_instance_verb_closed
  (TRCF : forall fx0 : YK11.FPState, @rec_calls_free_c.trec_calls_free_spec fx0 rc SK0 PB_cmd B MT)
  (TARG_LINE : forall fx0 : YK11.FPState, @arg_line_c.targ_line_spec fx0 rc SK0 PB_cmd B MT)
  (TARG_I : forall fx0 : YK11.FPState, @arg_i_c.targ_i_spec fx0 rc SK0 PB_cmd B MT)
  (TREC_SHAPE_OF : forall fx0 : YK11.FPState, @rec_shape_of_c.trec_shape_of_spec fx0 rc SK0 PB_cmd B MT)
  (TANSWER : forall fx0 : YK11.FPState, @answer_c.tanswer_spec fx0 rc SK0 PB_cmd B MT)
  (ASTRSPN : forall fx0 : YK11.FPState,
     @RtString.astrspn_realizes fx0 rc SEGS B (SIG CmdSyms.CS___interceptor_trampoline_strspn) 0xa7098 0x6045d8)
  (ASTRCSPN : forall fx0 : YK11.FPState,
     @RtString.astrcspn_realizes fx0 rc SEGS B (SIG CmdSyms.CS___interceptor_trampoline_strcspn) 0xa7098 0x6045d8) :
  sup_instance_verb_c.tsup_instance_verb_spec B MT.
Proof.
exact (sup_instance_verb.tsup_instance_verb_holds B MT TRCF TARG_LINE TARG_I TREC_SHAPE_OF TANSWER ASTRSPN ASTRCSPN
  k_vobjs k_tl HB MTL k_sig k_pimg k_pwr k_rook k_rob k_relro k_tail k_cells
  (CmdRecImg.cmd_rom_view_on SEGS B LAWS HB IMG CMD_RLO CMD_RHI) (crb_zsh SEGS B LAWS HB 0x21d60 3 crb_addr_21d60)
  (crb_hull SEGS B LAWS HB 0x21d60 3 crb_hull_21d60) k_apart).
Qed.

Theorem tsup_host_setting_closed
  (TRCF : forall fx0 : YK11.FPState, @rec_calls_free_c.trec_calls_free_spec fx0 rc SK0 PB_cmd B MT)
  (TARG_LINE : forall fx0 : YK11.FPState, @arg_line_c.targ_line_spec fx0 rc SK0 PB_cmd B MT)
  (TARG_I : forall fx0 : YK11.FPState, @arg_i_c.targ_i_spec fx0 rc SK0 PB_cmd B MT)
  (TXSTRDUP : forall fx0 : YK11.FPState, @xstrdup_c.txstrdup_spec fx0 rc SK0 PB_cmd B MT)
  (TMIX_CALL : forall fx0 : YK11.FPState, @mix_call_c.tmix_call_spec fx0 rc SK0 PB_cmd B MT)
  (AMALLOC4 : forall fx0 : YK11.FPState, @YC5d.amalloc04_rule fx0 rc SK0 SEGS B MT)
  (AFREE4 : forall fx0 : YK11.FPState, @YC5d.afree04_rule fx0 rc SK0 SEGS B MT)
  (ASTRLEN : forall fx0 : YK11.FPState,
     @RtString.astrlen_realizes fx0 rc SEGS B (SIG CmdSyms.CS___interceptor_trampoline_strlen))
  (ASTRCAT : forall fx0 : YK11.FPState,
     @RtString.astrcat_realizes fx0 rc SEGS B (SIG CmdSyms.CS___interceptor_trampoline_strcat)) :
  sup_host_setting_c.tsup_host_setting_spec B MT.
Proof.
exact (sup_host_setting.tsup_host_setting_holds B MT TRCF TARG_LINE TARG_I TXSTRDUP TMIX_CALL AMALLOC4 AFREE4 ASTRLEN
  ASTRCAT k_vobjs HB k_tl MTL k_sig k_pimg k_pwr k_rook k_rob k_relro k_apart k_atk k_tail IMG).
Qed.

Theorem tsup_pin_accept_closed
  (TRCF : forall fx0 : YK11.FPState, @rec_calls_free_c.trec_calls_free_spec fx0 rc SK0 PB_cmd B MT)
  (TXSTRDUP : forall fx0 : YK11.FPState, @xstrdup_c.txstrdup_spec fx0 rc SK0 PB_cmd B MT)
  (TREC_SHAPE_OF : forall fx0 : YK11.FPState, @rec_shape_of_c.trec_shape_of_spec fx0 rc SK0 PB_cmd B MT)
  (TANSWER : forall fx0 : YK11.FPState, @answer_c.tanswer_spec fx0 rc SK0 PB_cmd B MT) :
  sup_pin_accept_c.tsup_pin_accept_spec B MT.
Proof.
exact (sup_pin_accept.tsup_pin_accept_holds B MT TRCF TXSTRDUP TREC_SHAPE_OF TANSWER k_vobjs k_tl HB MTL k_sig k_pimg
  k_pwr k_apart k_rob k_relro k_rook k_tail k_roin).
Qed.

Theorem tsup_lv2_worker_set_closed
  (TRCF : forall fx0 : YK11.FPState, @rec_calls_free_c.trec_calls_free_spec fx0 rc SK0 PB_cmd B MT)
  (TXSTRDUP : forall fx0 : YK11.FPState, @xstrdup_c.txstrdup_spec fx0 rc SK0 PB_cmd B MT)
  (TREC_SHAPE_OF : forall fx0 : YK11.FPState, @rec_shape_of_c.trec_shape_of_spec fx0 rc SK0 PB_cmd B MT)
  (TANSWER : forall fx0 : YK11.FPState, @answer_c.tanswer_spec fx0 rc SK0 PB_cmd B MT) :
  sup_lv2_worker_set_c.tsup_lv2_worker_set_spec B MT.
Proof.
exact (sup_lv2_worker_set.tsup_lv2_worker_set_holds B MT TRCF TXSTRDUP TREC_SHAPE_OF TANSWER k_vobjs HB k_tl k_pimg
  k_pwr MTL k_sig k_rook k_rob k_relro k_apart k_roin k_tail).
Qed.

Theorem tsup_policy_set_closed
  (TRCF : forall fx0 : YK11.FPState, @rec_calls_free_c.trec_calls_free_spec fx0 rc SK0 PB_cmd B MT)
  (TXSTRDUP : forall fx0 : YK11.FPState, @xstrdup_c.txstrdup_spec fx0 rc SK0 PB_cmd B MT)
  (TREC_SHAPE_OF : forall fx0 : YK11.FPState, @rec_shape_of_c.trec_shape_of_spec fx0 rc SK0 PB_cmd B MT)
  (TANSWER : forall fx0 : YK11.FPState, @answer_c.tanswer_spec fx0 rc SK0 PB_cmd B MT) :
  sup_policy_set_c.tsup_policy_set_spec B MT.
Proof.
exact (sup_policy_set.tsup_policy_set_holds B MT TRCF TXSTRDUP TREC_SHAPE_OF TANSWER k_vobjs HB k_tl k_pimg k_pwr MTL
  k_sig k_rook k_rob k_relro k_apart k_roin k_tail).
Qed.

Theorem tsup_worker_env_closed
  (TRCF : forall fx0 : YK11.FPState, @rec_calls_free_c.trec_calls_free_spec fx0 rc SK0 PB_cmd B MT)
  (TXSTRDUP : forall fx0 : YK11.FPState, @xstrdup_c.txstrdup_spec fx0 rc SK0 PB_cmd B MT)
  (TREC_SHAPE_OF : forall fx0 : YK11.FPState, @rec_shape_of_c.trec_shape_of_spec fx0 rc SK0 PB_cmd B MT)
  (TANSWER : forall fx0 : YK11.FPState, @answer_c.tanswer_spec fx0 rc SK0 PB_cmd B MT) :
  sup_worker_env_c.tsup_worker_env_spec B MT.
Proof.
exact (sup_worker_env.tsup_worker_env_holds TRCF TXSTRDUP TREC_SHAPE_OF TANSWER k_vobjs k_tl HB MTL k_sig k_pimg k_pwr
  k_apart k_rook k_tail k_roin).
Qed.

Theorem tsup_worker_list_closed
  (TRCF : forall fx0 : YK11.FPState, @rec_calls_free_c.trec_calls_free_spec fx0 rc SK0 PB_cmd B MT)
  (TREC_SHAPE_OF : forall fx0 : YK11.FPState, @rec_shape_of_c.trec_shape_of_spec fx0 rc SK0 PB_cmd B MT)
  (TANSWER : forall fx0 : YK11.FPState, @answer_c.tanswer_spec fx0 rc SK0 PB_cmd B MT) :
  sup_worker_list_c.tsup_worker_list_spec B MT.
Proof.
exact (sup_worker_list.tsup_worker_list_holds B MT TRCF TREC_SHAPE_OF TANSWER k_vobjs k_tl HB MTL k_sig k_pimg k_pwr
  k_rob k_relro k_apart k_rook k_roin).
Qed.

Theorem tlv2_refusals_forget_closed
  (TRCF : forall fx0 : YK11.FPState, @rec_calls_free_c.trec_calls_free_spec fx0 rc SK0 PB_cmd B MT)
  (TXSTRDUP : forall fx0 : YK11.FPState, @xstrdup_c.txstrdup_spec fx0 rc SK0 PB_cmd B MT)
  (TMIX_CALL : forall fx0 : YK11.FPState, @mix_call_c.tmix_call_spec fx0 rc SK0 PB_cmd B MT) :
  lv2_refusals_forget_c.tlv2_refusals_forget_spec B MT.
Proof.
exact (lv2_refusals_forget.tlv2_refusals_forget_holds B MT TRCF TXSTRDUP TMIX_CALL k_vobjs HB k_tl MTL k_sig k_pimg
  k_pwr k_rook k_rob k_relro k_apart k_tail k_roin).
Qed.

Theorem tsup_quarantine_clear_closed
  (TRCF : forall fx0 : YK11.FPState, @rec_calls_free_c.trec_calls_free_spec fx0 rc SK0 PB_cmd B MT)
  (TXSTRDUP : forall fx0 : YK11.FPState, @xstrdup_c.txstrdup_spec fx0 rc SK0 PB_cmd B MT)
  (TREC_SHAPE_OF : forall fx0 : YK11.FPState, @rec_shape_of_c.trec_shape_of_spec fx0 rc SK0 PB_cmd B MT)
  (TANSWER : forall fx0 : YK11.FPState, @answer_c.tanswer_spec fx0 rc SK0 PB_cmd B MT) :
  sup_quarantine_clear_c.tsup_quarantine_clear_spec B MT.
Proof.
exact (sup_quarantine_clear.tsup_quarantine_clear_holds B MT TRCF TXSTRDUP TREC_SHAPE_OF TANSWER k_vobjs k_tl HB MTL
  k_sig k_pimg k_pwr k_rob k_rook k_apart k_roin k_tail IMG).
Qed.

Theorem tdescriptors_panel_get_closed
  (TRCF : forall fx0 : YK11.FPState, @rec_calls_free_c.trec_calls_free_spec fx0 rc SK0 PB_cmd B MT)
  (TXSTRDUP : forall fx0 : YK11.FPState, @xstrdup_c.txstrdup_spec fx0 rc SK0 PB_cmd B MT)
  (TREC_SHAPE_OF : forall fx0 : YK11.FPState, @rec_shape_of_c.trec_shape_of_spec fx0 rc SK0 PB_cmd B MT)
  (TANSWER : forall fx0 : YK11.FPState, @answer_c.tanswer_spec fx0 rc SK0 PB_cmd B MT) :
  descriptors_panel_get_c.tdescriptors_panel_get_spec B MT.
Proof.
exact (descriptors_panel_get.tdescriptors_panel_get_holds B MT TRCF TXSTRDUP TREC_SHAPE_OF TANSWER k_vobjs k_tl HB
  k_sig MTL k_pimg k_pwr k_apart k_rook k_tail k_roin).
Qed.

Theorem tdescriptors_add_closed
  (TRCF : forall fx0 : YK11.FPState, @rec_calls_free_c.trec_calls_free_spec fx0 rc SK0 PB_cmd B MT)
  (TXSTRDUP : forall fx0 : YK11.FPState, @xstrdup_c.txstrdup_spec fx0 rc SK0 PB_cmd B MT)
  (TMIX_CALL : forall fx0 : YK11.FPState, @mix_call_c.tmix_call_spec fx0 rc SK0 PB_cmd B MT) :
  descriptors_add_c.tdescriptors_add_spec B MT.
Proof.
exact (descriptors_add.tdescriptors_add_holds B MT TRCF TXSTRDUP TMIX_CALL k_vobjs k_tl HB MTL k_sig k_pimg k_pwr
  k_rook k_rob k_relro k_apart k_tail).
Qed.

Theorem tdescriptors_get_closed
  (TRCF : forall fx0 : YK11.FPState, @rec_calls_free_c.trec_calls_free_spec fx0 rc SK0 PB_cmd B MT)
  (TXSTRDUP : forall fx0 : YK11.FPState, @xstrdup_c.txstrdup_spec fx0 rc SK0 PB_cmd B MT)
  (TREC_SHAPE_OF : forall fx0 : YK11.FPState, @rec_shape_of_c.trec_shape_of_spec fx0 rc SK0 PB_cmd B MT)
  (TANSWER : forall fx0 : YK11.FPState, @answer_c.tanswer_spec fx0 rc SK0 PB_cmd B MT) :
  descriptors_get_c.tdescriptors_get_spec B MT.
Proof.
exact (descriptors_get.tdescriptors_get_holds B MT TRCF TXSTRDUP TREC_SHAPE_OF TANSWER k_vobjs HB k_tl MTL k_sig
  k_pimg k_pwr k_rook k_rob k_relro k_apart k_roin k_tail).
Qed.

Theorem tsup_reset_closed
  (TRCF : forall fx0 : YK11.FPState, @rec_calls_free_c.trec_calls_free_spec fx0 rc SK0 PB_cmd B MT)
  (TXSTRDUP : forall fx0 : YK11.FPState, @xstrdup_c.txstrdup_spec fx0 rc SK0 PB_cmd B MT)
  (TREC_SHAPE_OF : forall fx0 : YK11.FPState, @rec_shape_of_c.trec_shape_of_spec fx0 rc SK0 PB_cmd B MT)
  (TANSWER : forall fx0 : YK11.FPState, @answer_c.tanswer_spec fx0 rc SK0 PB_cmd B MT) :
  sup_reset_c.tsup_reset_spec B MT.
Proof.
exact (sup_reset.tsup_reset_holds B MT TRCF TXSTRDUP TREC_SHAPE_OF TANSWER k_vobjs k_roin k_tl HB MTL k_sig k_pimg
  k_pwr k_rob k_rook k_atk k_apart IMG).
Qed.

Theorem tpins_set_closed
  (TRCF : forall fx0 : YK11.FPState, @rec_calls_free_c.trec_calls_free_spec fx0 rc SK0 PB_cmd B MT)
  (TXSTRDUP : forall fx0 : YK11.FPState, @xstrdup_c.txstrdup_spec fx0 rc SK0 PB_cmd B MT)
  (TMIX_CALL : forall fx0 : YK11.FPState, @mix_call_c.tmix_call_spec fx0 rc SK0 PB_cmd B MT)
  (TANSWER_CODE : forall fx0 : YK11.FPState, @answer_code_c.tanswer_code_spec fx0 rc SK0 PB_cmd B MT) :
  pins_set_c.tpins_set_spec B MT.
Proof.
exact (pins_set.tpins_set_holds B MT TRCF TXSTRDUP TMIX_CALL TANSWER_CODE k_vobjs MTL HB k_tl k_sig k_pimg k_pwr
  k_rob k_relro k_rook k_apart k_tail k_roin).
Qed.

Theorem tpins_clear_closed
  (TRCF : forall fx0 : YK11.FPState, @rec_calls_free_c.trec_calls_free_spec fx0 rc SK0 PB_cmd B MT)
  (TXSTRDUP : forall fx0 : YK11.FPState, @xstrdup_c.txstrdup_spec fx0 rc SK0 PB_cmd B MT)
  (TMIX_CALL : forall fx0 : YK11.FPState, @mix_call_c.tmix_call_spec fx0 rc SK0 PB_cmd B MT)
  (TANSWER_CODE : forall fx0 : YK11.FPState, @answer_code_c.tanswer_code_spec fx0 rc SK0 PB_cmd B MT) :
  pins_clear_c.tpins_clear_spec B MT.
Proof.
exact (pins_clear.tpins_clear_holds B MT TRCF TXSTRDUP TMIX_CALL TANSWER_CODE k_vobjs k_tl HB MTL k_sig k_pimg k_pwr
  k_rob k_relro k_apart k_rook k_tail).
Qed.

Theorem tsup_chain_closed
  (TRCF : forall fx0 : YK11.FPState, @rec_calls_free_c.trec_calls_free_spec fx0 rc SK0 PB_cmd B MT)
  (TARG_I : forall fx0 : YK11.FPState, @arg_i_c.targ_i_spec fx0 rc SK0 PB_cmd B MT)
  (TXSTRDUP : forall fx0 : YK11.FPState, @xstrdup_c.txstrdup_spec fx0 rc SK0 PB_cmd B MT)
  (TREC_SHAPE_OF : forall fx0 : YK11.FPState, @rec_shape_of_c.trec_shape_of_spec fx0 rc SK0 PB_cmd B MT)
  (TANSWER : forall fx0 : YK11.FPState, @answer_c.tanswer_spec fx0 rc SK0 PB_cmd B MT)
  (AMALLOC4 : forall fx0 : YK11.FPState, @YC5d.amalloc04_rule fx0 rc SK0 SEGS B MT)
  (AFREE4 : forall fx0 : YK11.FPState, @YC5d.afree04_rule fx0 rc SK0 SEGS B MT)
  (ASPRINTF : forall fx0 : YK11.FPState,
     @RtFormat.asprintf_realizes fx0 rc SEGS B (SIG CmdSyms.CS___interceptor_trampoline_sprintf) 0xa7098 0x6045d8) :
  sup_chain_c.tsup_chain_spec B MT.
Proof.
exact (sup_chain_s8.tsup_chain_holds B MT k_tl HB MTL k_vobjs k_sig k_pimg k_pwr k_relro k_rob k_apart k_rook k_roin
  k_cells k_tail (crb_zsh SEGS B LAWS HB 0x21ee0 4 crb_addr_21ee0) (crb_zsh SEGS B LAWS HB 0x21f00 3 crb_addr_21f00)
  (crb_hull SEGS B LAWS HB 0x21ee0 4 crb_hull_21ee0) (crb_hull SEGS B LAWS HB 0x21f00 3 crb_hull_21f00) IMG TRCF TARG_I
  TXSTRDUP TREC_SHAPE_OF TANSWER AMALLOC4 AFREE4 ASPRINTF).
Qed.

End closed.
