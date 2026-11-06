From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL00 YL01 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import KindB RecInv RecInvU VerbsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_c verbs_receive_since.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_rel verbs_receive_st verbs_receive_step.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_call.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_br verbs_receive_br2 verbs_receive_br3.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_tail0 verbs_receive_tail.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_fin_t verbs_receive_pre verbs_receive_br_link.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_br_dget verbs_receive_br_pget verbs_receive_br_qclear verbs_receive_br_pinacc verbs_receive_br_policy verbs_receive_br_lv2 verbs_receive_br_env verbs_receive_br_iinfo verbs_receive_br_pool verbs_receive_br_inst verbs_receive_br_remove verbs_receive_br_ledger verbs_receive_br_conn verbs_receive_br_reset verbs_receive_br_wlist verbs_receive_br_pinclr verbs_receive_br_broad verbs_receive_br_quit verbs_receive_br_chain verbs_receive_br_chclear verbs_receive_br_pinset.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import strndup_c strdup_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import strlen_c strtok_r_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import reply_c sup_resp_c sup_after_reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import strcspn_c strncmp_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import sup_broadcast_c sup_host_setting_c chain_words_c sup_connect_c descriptors_get_c sup_worker_env_c sup_instance_info_c sup_call_c sup_instance_verb_c sup_lv2_worker_set_c descriptors_panel_get_c sup_pin_accept_c pins_clear_c lv2_refusals_forget_c sup_policy_set_c sup_pool_config_c sup_quarantine_clear_c sup_remove_c sup_remove_all_c sup_reset_c sup_worker_list_c sup_chain_clear_c pin_set_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require VerbsMem rec_shape_of_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require verbs_receive_disp.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require verbs_receive_tok.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require atoi_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require strcmp_c verb_is_c is_instance_verb_c number_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import sup_add_c descriptors_add_c verbs_receive_br_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require sup_reply_code_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Section P0.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.

Lemma vr_post_contract : forall (fx : YK11.FPState) L A regs mem md b R O msg fd data n q0 D can lb cb ps c',
  vr_post B API (CF.verbs_receive_st.VS fx L A regs mem md b R O msg fd data n q0 D can lb cb ps) c' ->
  exists (fx' : YK11.FPState) L' A' regs' mem' md' O' b',
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\
    CF.RecKindB.fp_kept fx fx' /\
    CF.RecKindB.call_post_rec B (aa_MR API) VR_K L A regs mem md vr_writes (fun a => In a (map fst O))
      L' A' regs' mem' md' /\
    ro_agree (ms_segs B) mem' /\
    (let '(R', x, quit) := vr_run R D in
       g_rec_rep (ms_segs B) L' A' mem' R' O' /\
       le_at B mem' G_QUIT (Mem.le4 (Z_to_bv 64 (if quit then 1 else q0)))) /\
    In (data, Z.max n 1) (blocks L' A') /\ le_at B mem' data D /\
    ~ In (data, Z.max n 1) O' /\
    (forall pn, In pn (blocks L A) -> ~ In pn O -> In pn (blocks L' A')) /\
    (forall pn, In pn (blocks L A) -> ~ In pn O -> ~ In pn O') /\
    (st_init_done A = true -> st_init_done A' = true) /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    le_at B mem' msg (Mem.le4 (Z_to_bv 64 fd)) /\
    le_at B mem' (msg + 8) (Mem.le8 (Z_to_bv 64 data)) /\
    le_at B mem' (msg + 16) (Mem.le8 (Z_to_bv 64 n)) /\
    (forall pn, In pn (blocks L' A') -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn O') /\
    blocks_kept B L A mem mem' (owned_by O) /\
    (exists can', vr_tables B mem' can') /\
    Mem.bytes_at (ms_segs B) mem' rec_shape_of_c.G_SHAPES rec_shape_of_c.g_shapes_bytes /\
    res_ok_slots A' b' /\ sb_cap b' = sb_cap b.
Proof.
  intros fx L A regs mem md b R O msg fd data n q0 D can lb cb ps c' H. exact H.
Qed.

End P0.

Section V.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.

Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO : errno_addr B = 0x3441c.
Hypothesis GUARD : ms_guard B = 0x54730.
Hypothesis GOTG : ms_got_guard B = 0x22d40.
Hypothesis FREE_PC : ms_free B = 0x18ad0.
Hypothesis GLOBS : forall a, in_globals FrameAPI.frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis GLOBO : forall L A mem md a, aa_MR API L A mem md -> in_globals FrameAPI.frame_G a -> ~ owned B L A a.
Hypothesis RELRO : forall L A mem md a, aa_MR API L A mem md -> in_globals FrameAPI.frame_RELRO a ->
  in_img B a /\ ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTXO : ctx_owned B API.
Hypothesis BSLACK : block_slack_present B API.
Hypothesis BWR : blocks_writable B API.
Hypothesis TP : ms_tp B = 0x344c0.
Hypothesis EU : errno_unowned B API.

Hypothesis SNDUP : forall f : YK11.FPState, @strndup_contract f rc B API.
Hypothesis SDUP : forall f : YK11.FPState, @strdup_contract f rc B API.
Hypothesis SRESP : forall f : YK11.FPState, @sup_resp_contract f rc B API.
Hypothesis RP : forall f : YK11.FPState, @reply_contract f rc B API.
Hypothesis SAR : forall f : YK11.FPState, @sup_after_reply_contract f rc B API.
Hypothesis FREE : forall f : YK11.FPState, @free_contract f rc B API.
Hypothesis DB : forall f : YK11.FPState, @sup_broadcast_contract f rc B API.
Hypothesis DH : forall f : YK11.FPState, @sup_host_setting_contract f rc B API.
Hypothesis CW : forall f : YK11.FPState, @chain_words_contract f rc B API.
Hypothesis DCONN : forall f : YK11.FPState, @sup_connect_contract f rc B API.
Hypothesis DDG : forall f : YK11.FPState, @descriptors_get_contract f rc B API.
Hypothesis DENV : forall f : YK11.FPState, @sup_worker_env_contract f rc B API.
Hypothesis DII : forall f : YK11.FPState, @sup_instance_info_contract f rc B API.
Hypothesis DCALL : forall f : YK11.FPState, @sup_call_contract f rc B API.
Hypothesis DIV : forall f : YK11.FPState, @sup_instance_verb_contract f rc B API.
Hypothesis DLV2 : forall f : YK11.FPState, @sup_lv2_worker_set_contract f rc B API.
Hypothesis DPG : forall f : YK11.FPState, @descriptors_panel_get_contract f rc B API.
Hypothesis DPA : forall f : YK11.FPState, @sup_pin_accept_contract f rc B API.
Hypothesis DPC : forall f : YK11.FPState, @pins_clear_contract f rc B API.
Hypothesis DLRF : forall f : YK11.FPState, @lv2_refusals_forget_contract f rc B API.
Hypothesis DPOL : forall f : YK11.FPState, @sup_policy_set_contract f rc B API.
Hypothesis DPOOL : forall f : YK11.FPState, @sup_pool_config_contract f rc B API.
Hypothesis DQC : forall f : YK11.FPState, @sup_quarantine_clear_contract f rc B API.
Hypothesis DREM : forall f : YK11.FPState, @sup_remove_contract f rc B API.
Hypothesis DRALL : forall f : YK11.FPState, @sup_remove_all_contract f rc B API.
Hypothesis DRST : forall f : YK11.FPState, @sup_reset_contract f rc B API.
Hypothesis DWL : forall f : YK11.FPState, @sup_worker_list_contract f rc B API.
Hypothesis DCC : forall f : YK11.FPState, @sup_chain_clear_contract f rc B API.
Hypothesis PSW : forall f : YK11.FPState, @pin_set_words_contract f rc B API.
Hypothesis SA : forall f : YK11.FPState, @sup_add_contract f rc B API.
Hypothesis DA : forall f : YK11.FPState, @descriptors_add_contract f rc B API.

Hypothesis SLEN : strlen_contract.
Hypothesis STOK : strtok_r_contract.
Hypothesis SCMP : strcmp_c.strcmp_contract.
Hypothesis CSPN : strcspn_contract.
Hypothesis NCMP : strncmp_contract.
Hypothesis VIS : verb_is_c.verb_is_contract.
Hypothesis IIV : is_instance_verb_c.is_instance_verb_contract.
Hypothesis ATOI : atoi_c.atoi_contract.
Hypothesis NUM : number_c.number_contract.
Hypothesis RC : sup_reply_code_c.sup_reply_code_contract.

Let HF : vframe B API := Build_vframe B API SEGS ERRNO GUARD GOTG FREE_PC GLOBS GLOBO RELRO AX CTXO BSLACK BWR.

Section W.
Variable S : vstart.
Hypothesis HS : vok B API S.

Local Notation D := (s_D S).

Definition rt_ok (r : vroute) : Prop :=
  forall (f : YK11.FPState) rg mem2 md1 L1 A1 jk,
    route (toks D) = r -> toks D <> [] ->
    @vr_state f _ B API S rg (route_pc r) mem2 md1 L1 A1 (s_R S) (s_O S) 2 (s_q0 S) None jk
      (mkCfg (@mkst f rg (Z_to_bv 64 (route_pc r)) mem2 (seg_rom rsegs)) md1) ->
    getr rg 19 = verbs_receive_disp.ntokw (toks D) ->
    getr rg 20 = hd (Z_to_bv 64 0) (s_ps S) -> getr rg 21 = verbs_receive_disp.ntokw (toks D) ->
    verbs_receive_disp.route_regs r (length (toks D)) (getr rg 8) (getr rg 10) (getr rg 11) (getr rg 22) ->
    SR rsegs (mkCfg (@mkst f rg (Z_to_bv 64 (route_pc r)) mem2 (seg_rom rsegs)) md1) (vr_post B API S).

Lemma nc30 : forall rg r, route (toks D) = r -> nc_route r = true ->
  join_k B API S 0x178ac 10 rg (s_R S) 2 (s_q0 S) (vr_post B API S).
Proof.
  intros rg r RT NR. apply (vr_tail_nc_17830 B API HF S HS RP FREE CSPN NCMP rg 2); [rewrite RT; exact NR | lia].
Qed.

Lemma nc6c8 : forall rg r, route (toks D) = r -> nc_route r = true ->
  join_k B API S 0x176c4 10 rg (s_R S) 2 (s_q0 S) (vr_post B API S).
Proof.
  intros rg r RT NR. apply (vr_tail_nc_176c8 B API HF S HS RP FREE rg 2); [rewrite RT; exact NR | lia].
Qed.

Lemma j70 : forall rg, getr rg 21 = verbs_receive_disp.ntokw (toks D) -> toks D <> [] ->
  join_k B API S 0x17a90 10 rg (s_R S) 2 (s_q0 S) (vr_post B API S).
Proof.
  intros rg N21 NE. exact (vr_tail_17970 B API HF S HS RP SAR FREE CSPN NCMP ATOI rg 2 N21 NE ltac:(lia)).
Qed.

Lemma rej_a : forall (f : YK11.FPState) rg P, join_k B API S 0x17a90 10 rg (s_R S) 2 (s_q0 S) P ->
  rej_k B API S f 0x17a88 rg (s_R S) 2 (s_q0 S) P.
Proof.
  intros f rg P JN rg1 mem md L A O k jk c HR.
  exact (@rej_join f rc B API HF S HS SRESP rg (s_R S) 2 (s_q0 S) 0x17a88 0x17a90 rg1 mem md L A O k jk c P
           (or_introl (conj eq_refl eq_refl)) HR ltac:(lia) JN).
Qed.

Lemma rej_b : forall (f : YK11.FPState) rg P, join_k B API S 0x178ac 10 rg (s_R S) 2 (s_q0 S) P ->
  rej_k B API S f 0x178a4 rg (s_R S) 2 (s_q0 S) P.
Proof.
  intros f rg P JN rg1 mem md L A O k jk c HR.
  exact (@rej_join f rc B API HF S HS SRESP rg (s_R S) 2 (s_q0 S) 0x178a4 0x178ac rg1 mem md L A O k jk c P
           (or_intror (conj eq_refl eq_refl)) HR ltac:(lia) JN).
Qed.

Lemma rt_dget : rt_ok RDget.
Proof.
  intros f rg mem2 md1 L1 A1 jk RT NE HST F19 F20 F21 RR.
  exact (vr_br_dget B API HF S HS DDG f rg mem2 md1 L1 A1 (s_R S) (s_O S) 2 (s_q0 S) jk _ _ HST RT F21
           ltac:(lia) (nc30 rg RDget RT eq_refl) (rej_a f rg _ (j70 rg F21 NE))).
Qed.

Lemma rt_pget : rt_ok RPget.
Proof.
  intros f rg mem2 md1 L1 A1 jk RT NE HST F19 F20 F21 RR.
  exact (vr_br_pget B API HF S HS DPG f rg mem2 md1 L1 A1 (s_R S) (s_O S) 2 (s_q0 S) jk _ _ HST RT F21
           ltac:(lia) (nc30 rg RPget RT eq_refl) (rej_a f rg _ (j70 rg F21 NE))).
Qed.

Lemma rt_qclear : rt_ok RQclear.
Proof.
  intros f rg mem2 md1 L1 A1 jk RT NE HST F19 F20 F21 RR.
  exact (vr_br_qclear B API HF S HS DQC f rg mem2 md1 L1 A1 (s_R S) (s_O S) 2 (s_q0 S) jk _ _ HST RT F21
           ltac:(lia) (nc30 rg RQclear RT eq_refl) (rej_a f rg _ (j70 rg F21 NE))).
Qed.

Lemma rt_pinacc : rt_ok RPinacc.
Proof.
  intros f rg mem2 md1 L1 A1 jk RT NE HST F19 F20 F21 RR.
  exact (vr_br_pinacc B API HF S HS DPA f rg mem2 md1 L1 A1 (s_R S) (s_O S) 2 (s_q0 S) jk _ _ HST RT F21
           ltac:(lia) (nc30 rg RPinacc RT eq_refl) (rej_a f rg _ (j70 rg F21 NE))).
Qed.

Lemma rt_policy : rt_ok RPolicy.
Proof.
  intros f rg mem2 md1 L1 A1 jk RT NE HST F19 F20 F21 RR.
  exact (vr_br_policy B API HF S HS DPOL f rg mem2 md1 L1 A1 (s_R S) (s_O S) 2 (s_q0 S) jk _ _ HST RT F21
           ltac:(lia) (nc30 rg RPolicy RT eq_refl) (rej_a f rg _ (j70 rg F21 NE))).
Qed.

Lemma rt_lv2 : rt_ok RLv2.
Proof.
  intros f rg mem2 md1 L1 A1 jk RT NE HST F19 F20 F21 RR.
  exact (vr_br_lv2 B API HF S HS DLV2 f rg mem2 md1 L1 A1 (s_R S) (s_O S) 2 (s_q0 S) jk _ _ HST RT F21
           ltac:(lia) (nc30 rg RLv2 RT eq_refl) (rej_a f rg _ (j70 rg F21 NE))).
Qed.

Lemma rt_env : rt_ok REnv.
Proof.
  intros f rg mem2 md1 L1 A1 jk RT NE HST F19 F20 F21 RR.
  exact (vr_br_env B API HF S HS DENV f rg mem2 md1 L1 A1 (s_R S) (s_O S) 2 (s_q0 S) jk _ _ HST RT F21
           ltac:(lia) (nc30 rg REnv RT eq_refl) (rej_a f rg _ (j70 rg F21 NE))).
Qed.

Lemma rt_iinfo : rt_ok RIinfo.
Proof.
  intros f rg mem2 md1 L1 A1 jk RT NE HST F19 F20 F21 RR.
  exact (vr_br_iinfo B API HF S HS ATOI DII f rg mem2 md1 L1 A1 (s_R S) (s_O S) 2 (s_q0 S) jk _ _ HST RT F21
           ltac:(lia) (nc30 rg RIinfo RT eq_refl) (rej_a f rg _ (j70 rg F21 NE))).
Qed.

Lemma rt_pool : rt_ok RPool.
Proof.
  intros f rg mem2 md1 L1 A1 jk RT NE HST F19 F20 F21 RR.
  exact (vr_br_pool B API HF S HS ATOI DPOOL f rg mem2 md1 L1 A1 (s_R S) (s_O S) 2 (s_q0 S) jk _ _ HST RT F21
           ltac:(lia) (nc30 rg RPool RT eq_refl) (rej_a f rg _ (j70 rg F21 NE))).
Qed.

Lemma rt_remove : rt_ok RRemove.
Proof.
  intros f rg mem2 md1 L1 A1 jk RT NE HST F19 F20 F21 RR.
  exact (vr_br_remove B API HF S HS ATOI DREM DRALL f rg mem2 md1 L1 A1 (s_R S) (s_O S) 2 (s_q0 S) jk _ _ HST RT F21
           ltac:(lia) (nc30 rg RRemove RT eq_refl) (rej_a f rg _ (j70 rg F21 NE))).
Qed.

Lemma rt_inst : rt_ok RInst.
Proof.
  intros f rg mem2 md1 L1 A1 jk RT NE HST F19 F20 F21 RR.
  destruct (inst_toks (toks D) RT) as (v & a & rest & TK).
  assert (L2 : (2 <= length (toks D))%nat) by (rewrite TK; cbn [length]; lia).
  exact (vr_br_inst B API HF S HS ATOI DCALL f rg mem2 md1 L1 A1 (s_R S) (s_O S) 2 (s_q0 S) jk _ _ HST RT F21
           ltac:(lia) (vr_tail_17830 B API HF S HS RP SAR FREE CSPN NCMP ATOI rg 2 L2 ltac:(lia))).
Qed.

Lemma rt_conn : rt_ok RConn.
Proof.
  intros f rg mem2 md1 L1 A1 jk RT NE HST F19 F20 F21 RR.
  destruct (conn_toks (toks D) RT) as (v & a & b & TK).
  assert (L2 : (2 <= length (toks D))%nat) by (rewrite TK; cbn [length]; lia).
  assert (H20 : getr rg 20 = nth 0 (s_ps S) (Z_to_bv 64 0)) by (rewrite F20; destruct (s_ps S); reflexivity).
  exact (vr_br_conn B API HF S HS DCONN f rg mem2 md1 L1 A1 (s_R S) (s_O S) 2 (s_q0 S) jk _ _ HST RT F21
           ltac:(lia) H20 (vr_tail_17830 B API HF S HS RP SAR FREE CSPN NCMP ATOI rg 2 L2 ltac:(lia))).
Qed.

Lemma rt_ledger : forall led, rt_ok (RLedger led).
Proof.
  intros led f rg mem2 md1 L1 A1 jk RT NE HST F19 F20 F21 RR.
  destruct RR as [H10 H11].
  exact (vr_br_ledger B API HF S HS DIV f rg mem2 md1 L1 A1 (s_R S) (s_O S) 2 (s_q0 S) jk _ _ led HST RT F21
           ltac:(lia) H10 H11 (j70 rg F21 NE)).
Qed.

Lemma rt_chain : rt_ok RChain.
Proof.
  intros f rg mem2 md1 L1 A1 jk RT NE HST F19 F20 F21 RR.
  exact (vr_br_chain B API HF S HS CW f rg mem2 md1 L1 A1 (s_R S) (s_O S) 2 (s_q0 S) jk _ _ HST RT F19 ltac:(lia)
           (ok_decl B API S HS) (vr_tail_17970_ge B API HF S HS RP SAR FREE CSPN NCMP ATOI rg 2 F21 NE ltac:(lia))).
Qed.

Lemma rt_broad : rt_ok RBroad.
Proof.
  intros f rg mem2 md1 L1 A1 jk RT NE HST F19 F20 F21 RR.
  exact (vr_br_broad B API HF S HS DB DH f rg mem2 md1 L1 A1 (s_R S) (s_O S) 2 (s_q0 S) jk _ _ HST RT NE F21
           ltac:(lia) F19 (vr_tail_17974 B API HF S HS RP SAR FREE CSPN NCMP ATOI rg 2 F21 NE ltac:(lia))).
Qed.

Lemma rt_pinclr : rt_ok RPinclr.
Proof.
  intros f rg mem2 md1 L1 A1 jk RT NE HST F19 F20 F21 RR.
  exact (vr_br_pinclr B API HF S HS SRESP DPC DLRF f rg mem2 md1 L1 A1 (s_R S) (s_O S) 2 (s_q0 S) jk _ _ HST RT
           F21 ltac:(lia) (j70 rg F21 NE) (rej_a f rg _ (j70 rg F21 NE))).
Qed.

Lemma rt_quit : rt_ok RQuit.
Proof.
  intros f rg mem2 md1 L1 A1 jk RT NE HST F19 F20 F21 RR.
  exact (vr_br_quit B API HF S HS SRESP f rg mem2 md1 L1 A1 (s_R S) (s_O S) 2 (s_q0 S) jk _ _ HST RT F21 ltac:(lia)
           (nc6c8 rg RQuit RT eq_refl) (rej_b f rg _ (nc30 rg RQuit RT eq_refl))).
Qed.

Lemma rt_reset : rt_ok RReset.
Proof.
  intros f rg mem2 md1 L1 A1 jk RT NE HST F19 F20 F21 RR.
  exact (vr_br_reset B API HF S HS DRST f rg mem2 md1 L1 A1 (s_R S) (s_O S) 2 (s_q0 S) jk _ _ HST RT F21 ltac:(lia)
           RR (j70 rg F21 NE) (rej_b f rg _ (nc30 rg RReset RT eq_refl))).
Qed.

Lemma rt_wlist : rt_ok RWlist.
Proof.
  intros f rg mem2 md1 L1 A1 jk RT NE HST F19 F20 F21 RR.
  exact (vr_br_wlist B API HF S HS DWL f rg mem2 md1 L1 A1 (s_R S) (s_O S) 2 (s_q0 S) jk _ _ HST RT F21 ltac:(lia)
           (nc6c8 rg RWlist RT eq_refl) (rej_b f rg _ (nc30 rg RWlist RT eq_refl))).
Qed.

Lemma rt_chclear : rt_ok RChclear.
Proof.
  intros f rg mem2 md1 L1 A1 jk RT NE HST F19 F20 F21 RR.
  exact (vr_br_chclear B API HF S HS NUM DCC TP EU f rg mem2 md1 L1 A1 (s_R S) (s_O S) 2 (s_q0 S) jk _ _ HST RT
           F21 ltac:(lia) (j70 rg F21 NE) (rej_a f rg _ (j70 rg F21 NE))).
Qed.

Lemma rt_pinset : rt_ok RPinset.
Proof.
  intros f rg mem2 md1 L1 A1 jk RT NE HST F19 F20 F21 RR.
  exact (vr_br_pinset B API HF S HS SRESP PSW f rg mem2 md1 L1 A1 (s_R S) (s_O S) 2 (s_q0 S) jk _ _ HST RT F21
           ltac:(lia) F19 (ok_decl B API S HS) (j70 rg F21 NE)).
Qed.

Lemma rt_add : rt_ok RAdd.
Proof.
  intros f rg mem2 md1 L1 A1 jk RT NE HST F19 F20 F21 RR.
  assert (NC : nc_route (route (toks D)) = true) by (rewrite RT; reflexivity).
  destruct (route_nc (toks D) NC) as (v & rest & TK & TC).
  exact (vr_br_add B API HF S HS DA RC ATOI SA SCMP NCMP f rg mem2 md1 L1 A1 (s_R S) (s_O S) 2 (s_q0 S) jk _ _ HST RT
           F21 ltac:(lia) F19 RR
           ltac:(apply join_k_of_ge; exact (vr_tail_17834_n B API HF S HS RP FREE CSPN NCMP rg 2 v rest TK TC ltac:(lia)))
           (rej_a f rg _ (j70 rg F21 NE)) (rej_b f rg _ (nc30 rg RAdd RT eq_refl))).
Qed.

Lemma vr_dispatch_cases : rt_ok RAdd ->
  forall (f : YK11.FPState) rg mem1 md1 L1 A1 jk c,
  @vr_state f _ B API S rg
    (match toks D with [] => CF.verbs_receive_tok.VR_EMPTY | _ => verbs_receive_disp.DISPATCH end)
    mem1 md1 L1 A1 (s_R S) (s_O S) 2 (s_q0 S) None jk c ->
  getr rg 18 = Z_to_bv 64 (s_msg S) ->
  (toks D <> [] -> getr rg 19 = verbs_receive_disp.ntokw (toks D) /\
                   getr rg 21 = verbs_receive_disp.ntokw (toks D)) ->
  SR rsegs c (vr_post B API S).
Proof.
  intros HADD f rg mem1 md1 L1 A1 jk c HST E18 E1921.
  destruct (toks D) as [|v rest] eqn:TK0 in HST.
  - apply (vr_br_empty B API HF S HS SRESP f rg mem1 md1 L1 A1 (s_R S) (s_O S) 2 (s_q0 S) jk c _ HST TK0 E18
             ltac:(lia)).
    intros rg0 _. apply (vr_tail_176c8 B API HF S HS RP SAR FREE CSPN NCMP ATOI rg0 2); [rewrite TK0; cbn; lia | lia].
  - assert (NE : toks D <> []) by (rewrite TK0; discriminate).
    destruct (E1921 NE) as [E19 E21].
    apply (@vr_route f rc B API HF S HS SCMP CSPN NCMP VIS IIV rg mem1 md1 L1 A1 (s_R S) (s_O S) 2 (s_q0 S) jk c _
             HST NE E18 E19 E21).
    intros rg' mem2 HST' F18 F19 F20 F21 RR.
    revert HST' RR. destruct (route (toks D)) eqn:RT; intros HST' RR.
    + exact (HADD f rg' mem2 md1 L1 A1 jk RT NE HST' F19 F20 F21 RR).
    + exact (rt_dget f rg' mem2 md1 L1 A1 jk RT NE HST' F19 F20 F21 RR).
    + exact (rt_pget f rg' mem2 md1 L1 A1 jk RT NE HST' F19 F20 F21 RR).
    + exact (rt_remove f rg' mem2 md1 L1 A1 jk RT NE HST' F19 F20 F21 RR).
    + exact (rt_wlist f rg' mem2 md1 L1 A1 jk RT NE HST' F19 F20 F21 RR).
    + exact (rt_iinfo f rg' mem2 md1 L1 A1 jk RT NE HST' F19 F20 F21 RR).
    + exact (rt_reset f rg' mem2 md1 L1 A1 jk RT NE HST' F19 F20 F21 RR).
    + exact (rt_qclear f rg' mem2 md1 L1 A1 jk RT NE HST' F19 F20 F21 RR).
    + exact (rt_policy f rg' mem2 md1 L1 A1 jk RT NE HST' F19 F20 F21 RR).
    + exact (rt_lv2 f rg' mem2 md1 L1 A1 jk RT NE HST' F19 F20 F21 RR).
    + exact (rt_pool f rg' mem2 md1 L1 A1 jk RT NE HST' F19 F20 F21 RR).
    + exact (rt_env f rg' mem2 md1 L1 A1 jk RT NE HST' F19 F20 F21 RR).
    + exact (rt_chain f rg' mem2 md1 L1 A1 jk RT NE HST' F19 F20 F21 RR).
    + exact (rt_chclear f rg' mem2 md1 L1 A1 jk RT NE HST' F19 F20 F21 RR).
    + exact (rt_pinset f rg' mem2 md1 L1 A1 jk RT NE HST' F19 F20 F21 RR).
    + exact (rt_pinacc f rg' mem2 md1 L1 A1 jk RT NE HST' F19 F20 F21 RR).
    + exact (rt_pinclr f rg' mem2 md1 L1 A1 jk RT NE HST' F19 F20 F21 RR).
    + exact (rt_quit f rg' mem2 md1 L1 A1 jk RT NE HST' F19 F20 F21 RR).
    + exact (rt_ledger led f rg' mem2 md1 L1 A1 jk RT NE HST' F19 F20 F21 RR).
    + exact (rt_inst f rg' mem2 md1 L1 A1 jk RT NE HST' F19 F20 F21 RR).
    + exact (rt_conn f rg' mem2 md1 L1 A1 jk RT NE HST' F19 F20 F21 RR).
    + exact (rt_broad f rg' mem2 md1 L1 A1 jk RT NE HST' F19 F20 F21 RR).
Qed.

End W.

Lemma vr_holds_of : (forall S, vok B API S -> rt_ok S RAdd) -> verbs_receive_contract B API.
Proof.
  intros HADD. unfold verbs_receive_contract.
  intros L A regs mem md b R O msg fd data n q0 D can PRE RO FZ A0 M8 M4K M63 SPM EIMG EAP HFD HMD HMN MOUT MNW
    DB0 DNO HD ND N8 REC CALLS ANS REP NREP DECL HQ HQW QOUT TAB SHP RES ROOM.
  assert (ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling) by (rewrite ERRNO; pose proof alloc_ceiling_val; lia).
  apply (@vr_prefix fx rc B API SEGS ERRNO_LOW GUARD GOTG GLOBS GLOBO AX CTXO BSLACK BWR (SNDUP fx) (SDUP fx) SLEN STOK
           L A regs mem md b msg data n D _ (proj1 PRE) RO A0 M8 M4K M63 HMD HMN MOUT DB0 HD ND N8 RES ROOM).
  intros c' MID.
  destruct (@vr_start fx rc B API HF L A regs mem md b R O msg fd data n q0 D can c' PRE RO FZ A0 M8 M4K M63 SPM EIMG
              HFD HMD HMN MOUT MNW DB0 DNO HD ND N8 REC CALLS ANS REP NREP DECL HQ HQW QOUT TAB SHP RES ROOM MID)
    as (lb & cb & ps & rg & mem1 & md1 & L1 & A1 & jk & HS & HST & E18 & E1921).
  pose proof (vr_dispatch_cases _ HS (HADD _ HS) fx rg mem1 md1 L1 A1 jk c' HST E18 E1921)
    as HD1.
  rewrite <- SEGS in HD1.
  eapply SR_mono; [exact HD1|].
  intros c'' HP. exact (vr_post_contract B API fx L A regs mem md b R O msg fd data n q0 D can lb cb ps c'' HP).
Qed.

Theorem verbs_receive_holds : verbs_receive_contract B API.
Proof. apply vr_holds_of. intros S HS. exact (rt_add S HS). Qed.

End V.
