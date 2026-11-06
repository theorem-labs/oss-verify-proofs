From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract Img0 FrameAPI SlotPack KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import Ledger GIInit LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require
  fuzz_malloc_c fuzz_free_c fuzz_realloc_c fuzz_strdup_c fuzz_alloc_live_c fuzz_alloc_peak_c fuzz_alloc_peak_reset_c fuzz_alloc_count_c fuzz_alloc_fail_c strlen_c strcmp_c bcmp_c memcpy_c memset_c memchr_c memcmp_c memcpy_same_c strtod_c snprintf_c snprintf_stk_c put_utf8_c hex4_c literal_c pj_parse_c pj_free_c pj_string_c pj_set_c pj_get_c pj_get_str_c grow_c parse_string_c parse_value_c parse_items_c put_c indent_c put_string_c write_value_c pj_write_c tx_put_c tx_line_c tx_string_c tx_value_c ex_hex4_c ex_string_c ex_word_c ex_value_c same_c check_reject_clean_c check_bounded_alloc_c check_as_written_c check_no_overread_c check_reject_clean_starved_c round_trip_text_c PjWriteNeed check_round_trip_c PjWriteHyp
  fuzz_alloc_most_c read_members_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require
  PjWriteAdapt ReaderLink RttEntry RttStgCmp RttStgEnd RttStgFf RttStgNl RttStgOom RttStgSame RttStgTx1 RttStgTxv bcmp bcmp_ro check_as_written check_bounded_alloc check_no_overread check_no_overread_a check_no_overread_b check_no_overread_end check_reject_clean check_reject_clean_starved ex_hex4 ex_string ex_value ex_word fuzz_alloc_count fuzz_alloc_fail fuzz_alloc_live fuzz_alloc_peak fuzz_alloc_peak_reset fuzz_free fuzz_malloc fuzz_realloc fuzz_strdup grow hex4 indent literal memchr memchr_ro memcmp memcmp_ro memcpy memcpy_ro memcpy_same memcpy_same_ro memset memset_ro parse_string pj_free pj_get pj_get_str pj_parse pj_set pj_string pj_write put put_string put_utf8 round_trip_text same snprintf snprintf_ro strcmp strlen strlen_ro strtod strtod_ro tx_line tx_put tx_string tx_value write_value check_round_trip ReaderRes EntrySR EntrySRHolds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require
  fuzz_alloc_ran_out_c fuzz_alloc_ran_out_reset_c parse_noting_c fuzz_alloc_ran_out fuzz_alloc_ran_out_reset parse_noting
  fuzz_alloc_most read_members.
Local Open Scope Z_scope.

Section LinkPlain.
Context {rc : RunCeil} {fx : FPState}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SYMS : slot_syms B.
Hypothesis GLOB : slot_globals B.
Hypothesis FA : forall fx' : FPState, @frame_allocator rc fx' B API.
Lemma lp_segs : ms_segs B = rsegs.
Proof. exact (proj1 SYMS). Qed.

(* The allocator entries of slot_syms (LLVMFuzzerTestOneInput_c): in the .symtab of the #102 plain twin
   fuzz_preset.plain (sha256 c8f4d6b8e567b0b1...), malloc FUNC WEAK 0x178d8 (= default_malloc), free FUNC GLOBAL
   0x17798, realloc FUNC GLOBAL 0x19144. *)
Lemma lp_malloc_at : ms_malloc B = 0x178d8.
Proof. destruct SYMS as (_ & H & _). exact H. Qed.

Lemma lp_free_at : ms_free B = 0x17798.
Proof. destruct SYMS as (_ & _ & H & _). exact H. Qed.

Lemma lp_realloc_at : ms_realloc B = Some 0x19144.
Proof. destruct SYMS as (_ & _ & _ & H & _). exact H. Qed.

Lemma lp_errno : errno_addr B + 4 <= alloc_ceiling.
Proof.
  destruct SYMS as (_ & _ & _ & _ & _ & _ & Htp & Heo). unfold errno_addr. rewrite Htp, Heo.
  pose proof (@alloc_ceiling_value rc) as H. lia.
Qed.

Lemma lp_ax : AllocExtra B (aa_MR API).
Proof. destruct (FA fx) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma lp_ctx : ctx_owned B API.
Proof. destruct (FA fx) as (_ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma lp_slack : block_slack_present B API.
Proof. destruct (FA fx) as (_ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma lp_errno_unowned : errno_unowned B API.
Proof. destruct (FA fx) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma lp_frame_own : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Proof. destruct (FA fx) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma lp_frame_G : forall a, in_globals frame_G a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Proof. intros a Ha. unfold frame_G in Ha. exact (GLOB a Ha). Qed.

Lemma lp_globals : globals_free B API omx_G.
Proof. exact (@fuzz_malloc.omx_globals_free fx rc B API lp_segs lp_ax lp_frame_own lp_frame_G). Qed.

Lemma lp_malloc_r : forall fx' : FPState, @malloc_contract_r fx' rc B API pack_form.
Proof. intros fx'. destruct (FA fx') as (H & _). exact H. Qed.

Lemma lp_free_r : forall fx' : FPState, @free_contract_r fx' rc B API pack_form.
Proof. intros fx'. destruct (FA fx') as (_ & H & _). exact H. Qed.

Lemma lp_realloc_r : forall fx' : FPState, @realloc_contract_r fx' rc B API pack_form 0x19144.
Proof. intros fx'. destruct (FA fx') as (_ & _ & _ & H & _). exact (proj1 (H _ lp_realloc_at)). Qed.

Lemma lp_realloc_null_r : forall fx' : FPState, @realloc_null_contract_r fx' rc B API pack_form 0x19144.
Proof. intros fx'. destruct (FA fx') as (_ & _ & _ & H & _). exact (proj2 (H _ lp_realloc_at)). Qed.

Lemma lp_strlen : strlen_c.strlen_contract.
Proof. exact strlen.strlen_holds. Qed.
Lemma lp_strcmp : strcmp_c.strcmp_contract.
Proof. exact strcmp.strcmp_holds. Qed.
Lemma lp_bcmp : bcmp_c.bcmp_contract.
Proof. exact bcmp.bcmp_holds. Qed.
Lemma lp_memcpy : memcpy_c.memcpy_contract.
Proof. exact memcpy.memcpy_holds. Qed.
Lemma lp_memset : memset_c.memset_contract.
Proof. exact memset.memset_holds. Qed.
Lemma lp_memchr : memchr_c.memchr_contract.
Proof. exact memchr.memchr_holds. Qed.
Lemma lp_memcmp : memcmp_c.memcmp_contract.
Proof. exact memcmp.memcmp_holds. Qed.
Lemma lp_memcpy_same : memcpy_same_c.memcpy_same_contract.
Proof. exact memcpy_same.memcpy_same_holds. Qed.
Lemma lp_strtod : strtod_c.strtod_contract.
Proof. exact strtod.strtod_holds. Qed.
Lemma lp_snprintf : snprintf_c.snprintf_contract.
Proof. exact snprintf.snprintf_holds. Qed.
Lemma lp_snprintf_stk : snprintf_stk_c.snprintf_stk_contract.
Proof. exact snprintf.snprintf_stk_holds. Qed.
Lemma lp_put_utf8 : put_utf8_c.put_utf8_contract.
Proof. exact put_utf8.put_utf8_holds. Qed.
Lemma lp_hex4 : hex4_c.hex4_contract.
Proof. exact hex4.hex4_holds. Qed.
Lemma lp_literal : literal_c.literal_contract.
Proof. exact (literal.literal_holds lp_strlen lp_bcmp). Qed.

Lemma lp_alloc_live : fuzz_alloc_live_c.fuzz_alloc_live_contract.
Proof. exact fuzz_alloc_live.fuzz_alloc_live_holds. Qed.
Lemma lp_alloc_peak : fuzz_alloc_peak_c.fuzz_alloc_peak_contract.
Proof. exact fuzz_alloc_peak.fuzz_alloc_peak_holds. Qed.
Lemma lp_alloc_peak_reset : fuzz_alloc_peak_reset_c.fuzz_alloc_peak_reset_contract.
Proof. exact fuzz_alloc_peak_reset.fuzz_alloc_peak_reset_holds. Qed.
Lemma lp_alloc_count : fuzz_alloc_count_c.fuzz_alloc_count_contract.
Proof. exact fuzz_alloc_count.fuzz_alloc_count_holds. Qed.
Lemma lp_alloc_fail : fuzz_alloc_fail_c.fuzz_alloc_fail_contract.
Proof. exact fuzz_alloc_fail.fuzz_alloc_fail_holds. Qed.

Lemma lp_fuzz_malloc : forall fx' : FPState, @fuzz_malloc_c.fuzz_malloc_contract fx' rc B API pack_form.
Proof.
  intros fx'. exact (fuzz_malloc.fuzz_malloc_holds B API pack_form lp_segs lp_malloc_at lp_errno lp_globals (lp_malloc_r fx')).
Qed.

Lemma lp_fuzz_free : forall fx' : FPState, @fuzz_free_c.fuzz_free_contract fx' rc B API pack_form.
Proof.
  intros fx'. exact (fuzz_free.fuzz_free_holds B API pack_form lp_segs lp_free_at lp_frame_G lp_ax lp_frame_own (lp_free_r fx')).
Qed.

Lemma lp_fuzz_realloc : forall fx' : FPState, @fuzz_realloc_c.fuzz_realloc_contract fx' rc B API pack_form.
Proof.
  intros fx'. exact (fuzz_realloc.fuzz_realloc_holds B API lp_segs lp_errno lp_globals pack_form (lp_realloc_r fx') (lp_fuzz_malloc fx')).
Qed.

Lemma lp_fuzz_strdup : forall fx' : FPState, @fuzz_strdup_c.fuzz_strdup_contract fx' rc B API pack_form.
Proof.
  intros fx'. exact (fuzz_strdup.fuzz_strdup_holds B API pack_form lp_segs lp_errno lp_strlen lp_memcpy (lp_fuzz_malloc fx')).
Qed.

Lemma lp_reader : forall fx' : FPState,
  @pj_parse_c.pj_parse_contract fx' rc B API pack_form /\ @pj_free_c.pj_free_contract fx' rc B API pack_form /\
  @pj_string_c.pj_string_contract fx' rc B API pack_form /\ @pj_set_c.pj_set_contract fx' rc B API pack_form /\
  pj_get_c.pj_get_contract /\ pj_get_str_c.pj_get_str_contract /\
  @grow_c.grow_contract fx' rc B API pack_form /\ @parse_string_c.parse_string_contract fx' rc B API pack_form /\
  (forall d, (d <= MAXD)%nat ->
     @parse_value_c.parse_value_contract fx' rc B API pack_form d /\ @parse_items_c.parse_items_contract fx' rc B API pack_form d).
Proof.
  exact (ReaderLink.reader_link B API pack_form lp_ax lp_ctx lp_errno_unowned lp_fuzz_malloc lp_fuzz_free lp_fuzz_realloc
    lp_fuzz_strdup lp_memset lp_memcpy lp_strtod lp_strcmp lp_literal lp_put_utf8 lp_hex4).
Qed.

Lemma lp_pj_parse : forall fx' : FPState, @pj_parse_c.pj_parse_contract fx' rc B API pack_form.
Proof. intros fx'. exact (proj1 (lp_reader fx')). Qed.
Lemma lp_pj_free : forall fx' : FPState, @pj_free_c.pj_free_contract fx' rc B API pack_form.
Proof. intros fx'. exact (proj1 (proj2 (lp_reader fx'))). Qed.
Lemma lp_pj_string : forall fx' : FPState, @pj_string_c.pj_string_contract fx' rc B API pack_form.
Proof. intros fx'. destruct (lp_reader fx') as (_ & _ & H & _). exact H. Qed.
Lemma lp_pj_set : forall fx' : FPState, @pj_set_c.pj_set_contract fx' rc B API pack_form.
Proof. intros fx'. destruct (lp_reader fx') as (_ & _ & _ & H & _). exact H. Qed.
Lemma lp_pj_get : pj_get_c.pj_get_contract.
Proof. exact (pj_get.pj_get_holds lp_strcmp). Qed.
Lemma lp_pj_get_str : pj_get_str_c.pj_get_str_contract.
Proof. exact (pj_get_str.pj_get_str_holds lp_pj_get). Qed.
Lemma lp_grow : forall fx' : FPState, @grow_c.grow_contract fx' rc B API pack_form.
Proof. intros fx'. destruct (lp_reader fx') as (_ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma lp_parse_string : forall fx' : FPState, @parse_string_c.parse_string_contract fx' rc B API pack_form.
Proof. intros fx'. destruct (lp_reader fx') as (_ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma lp_put : forall fx' : FPState, @put_c.put_contract fx' rc B API pack_form.
Proof. intros fx'. exact (put.put_holds B API pack_form (lp_fuzz_realloc fx') lp_memcpy). Qed.

Lemma lp_indent : forall fx' : FPState, @indent_c.indent_contract fx' rc B API pack_form.
Proof. intros fx'. exact (indent.indent_holds B API pack_form lp_segs lp_ax lp_ctx (lp_put fx')). Qed.

Lemma lp_put_string : forall fx' : FPState, @put_string_c.put_string_contract fx' rc B API pack_form.
Proof. intros fx'. exact (put_string.put_string_holds B API pack_form lp_ax lp_ctx lp_put lp_snprintf lp_strlen). Qed.

Lemma lp_write_value : forall fx' : FPState, @write_value_c.write_value_contract fx' rc B API pack_form.
Proof.
  intros fx'. exact (write_value.write_value_holds B API pack_form lp_ax lp_ctx lp_put lp_indent lp_put_string lp_strlen lp_slack).
Qed.

Lemma lp_pj_write : forall fx' : FPState, @pj_write_c.pj_write_contract fx' rc B API pack_form.
Proof.
  intros fx'. exact (pj_write.pj_write_holds B API pack_form lp_segs lp_ax lp_ctx (lp_write_value fx') lp_put lp_fuzz_free).
Qed.

Lemma lp_tx_put : forall fx' : FPState, @tx_put_c.tx_put_contract fx' rc B API pack_form.
Proof.
  intros fx'. exact (tx_put.tx_put_holds B API pack_form lp_segs lp_errno (lp_realloc_r fx') (lp_realloc_null_r fx') lp_memcpy).
Qed.

Lemma lp_tx_line : forall fx' : FPState, @tx_line_c.tx_line_contract fx' rc B API pack_form.
Proof. intros fx'. exact (tx_line.tx_line_holds B API lp_segs lp_errno lp_ax lp_ctx pack_form (lp_tx_put fx')). Qed.

Lemma lp_tx_string : forall fx' : FPState, @tx_string_c.tx_string_contract fx' rc B API pack_form.
Proof. intros fx'. exact (tx_string.tx_string_holds B API lp_segs lp_errno lp_ax lp_ctx lp_globals pack_form (lp_tx_put fx')). Qed.

Lemma lp_tx_value : forall fx' : FPState, @tx_value_c.tx_value_contract fx' rc B API pack_form.
Proof.
  intros fx'. exact (tx_value.tx_value_holds B API lp_segs lp_errno lp_ax lp_ctx lp_globals lp_slack pack_form
    (lp_tx_put fx') (lp_tx_line fx') (lp_tx_string fx') lp_strlen).
Qed.

Lemma lp_ex_hex4 : ex_hex4_c.ex_hex4_contract.
Proof. exact ex_hex4.ex_hex4_holds. Qed.
Lemma lp_ex_string : ex_string_c.ex_string_contract.
Proof. exact (ex_string.ex_string_holds lp_ex_hex4). Qed.
Lemma lp_ex_word : ex_word_c.ex_word_contract.
Proof. exact (ex_word.ex_word_holds lp_strlen lp_bcmp). Qed.
Lemma lp_ex_value : ex_value_c.ex_value_contract.
Proof. exact (ex_value.ex_value_holds lp_ex_string lp_ex_word lp_strcmp lp_bcmp lp_memcpy lp_strtod). Qed.
Lemma lp_same : same_c.same_contract.
Proof. exact (same.same_holds lp_strcmp lp_bcmp). Qed.
Lemma lp_check_reject_clean : check_reject_clean_c.check_reject_clean_contract.
Proof. exact (check_reject_clean.check_reject_clean_holds lp_alloc_live lp_bcmp). Qed.
Lemma lp_check_bounded_alloc : check_bounded_alloc_c.check_bounded_alloc_contract.
Proof. exact check_bounded_alloc.check_bounded_alloc_holds. Qed.

Lemma lp_alloc_ran_out_reset : fuzz_alloc_ran_out_reset_c.fuzz_alloc_ran_out_reset_contract.
Proof. exact fuzz_alloc_ran_out_reset.fuzz_alloc_ran_out_reset_holds. Qed.
Lemma lp_alloc_ran_out : fuzz_alloc_ran_out_c.fuzz_alloc_ran_out_contract.
Proof. exact fuzz_alloc_ran_out.fuzz_alloc_ran_out_holds. Qed.
Lemma lp_alloc_most : fuzz_alloc_most_c.fuzz_alloc_most_contract.
Proof. exact fuzz_alloc_most.fuzz_alloc_most_holds. Qed.

Lemma lp_check_as_written : forall fx' : FPState, @check_as_written_c.check_as_written_contract fx' rc B API pack_form.
Proof.
  exact (check_as_written.check_as_written_holds B API pack_form lp_malloc_at lp_free_at lp_ax lp_errno_unowned
    lp_malloc_r lp_free_r lp_ex_value lp_globals lp_alloc_ran_out).
Qed.

Lemma lp_parse_noting : forall fx' : FPState, @parse_noting_c.parse_noting_contract fx' rc B API pack_form.
Proof.
  intros fx'. exact (parse_noting.parse_noting_holds B API pack_form lp_globals lp_alloc_live lp_alloc_ran_out_reset
    (lp_pj_parse fx') lp_alloc_ran_out).
Qed.

Lemma lp_check_no_overread : forall fx' : FPState, @check_no_overread_c.check_no_overread_contract fx' rc B API pack_form.
Proof.
  eapply (check_no_overread.check_no_overread_holds B API pack_form).
  all: first [ exact lp_malloc_at | exact lp_free_at | exact lp_ax | exact lp_ctx | exact lp_globals | exact lp_malloc_r
             | exact lp_free_r | exact lp_memcpy | exact lp_memset | exact lp_parse_noting | exact lp_pj_free
             | exact lp_same ].
Qed.

Lemma lp_not_owned_hi : forall L A mem md a, aa_MR API L A mem md -> alloc_ceiling <= a -> ~ owned B L A a.
Proof. intros L A mem md a M Ha O. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M O). lia. Qed.

Lemma lp_pj_write_need : forall KW : Z, (forall t, (PjTree.depth t <= 32)%nat -> pj_write_c.PJW_K t <= KW) ->
  forall fx' : FPState, @PjWriteNeed.pj_write_need fx' rc B API pack_form KW.
Proof.
  intros KW HK fx'. unfold PjWriteNeed.pj_write_need.
  intros L A regs mem md b v pretty t D Lam peak cnt fail SEG GG GD PRE INIT RO FRM R10 R11 HPR LG OFF PN PW DIN DEP
    D32 WL RFOK RM.
  pose proof (HK t D32) as Kt.
  pose proof lp_errno as HE. pose proof (@alloc_ceiling_value rc) as HCV.
  unfold call_pre_t, call_pre_k in PRE.
  destruct PRE as ((HM & HWF & HB & Hra & Hal & Hceil & Hsp & HWs & Htp & HWe & Haux) & HTS).
  assert (PRE' : call_pre_t B API (pj_write_c.PJW_K t) L A regs mem md).
  { unfold call_pre_t, call_pre_k.
    refine (conj (conj HM (conj HWF (conj HB (conj Hra (conj Hal (conj _ (conj Hsp (conj _ (conj Htp (conj HWe Haux))))))))))
      HTS); [lia | intros a Ha; apply HWs; lia]. }
  assert (OFF' : put_c.off_errno B (spZ regs - pj_write_c.PJW_K t) (pj_write_c.PJW_K t)) by (unfold put_c.off_errno in *; lia).
  pose proof (lp_pj_write fx' L A regs mem md b v pretty t D Lam peak cnt fail SEG GG GD PRE' INIT RO FRM R10 R11 HPR LG
    OFF' PN PW DIN DEP WL RFOK RM) as SRC.
  eapply SR_mono; [exact SRC|].
  intros c' RET. unfold pj_write_c.pj_write_ret in RET |- *. cbv zeta in RET |- *.
  destruct RET as (fx2 & L' & A' & regs' & mem' & md' & Lam' & peak' & b' & E1 & E2 & E3 & E4 & HM' & E6 & E7 & E8 & E9 &
    E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & FR & WW & RES).
  exists fx2, L', A', regs', mem', md', Lam', peak', b'.
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact HM'|].
  split; [exact E6|]. split; [exact E7|]. split; [exact E8|]. split; [exact E9|]. split; [exact E10|].
  split; [exact E11|]. split; [exact E12|]. split; [exact E13|]. split; [exact E14|]. split; [exact E15|].
  split; [exact E16|]. split; [exact E17|]. split; [exact E18|].
  split.
  { intros a H1 H2 H3 H4 H5 H6. apply FR; try assumption. lia. }
  split; [|exact RES].
  intros a Ha Hw.
  destruct (Z_lt_le_dec a (spZ regs - pj_write_c.PJW_K t)) as [Hlo|Hhi].
  - destruct Ha as [Ha|Ha]; [|exact (WW a (or_intror Ha) Hw)].
    assert (Hc : alloc_ceiling <= a) by lia.
    refine (proj1 (proj2 (FR a _ _ _ _ _ _)) Hw).
    + left; lia.
    + exact (lp_not_owned_hi L A mem md a HM Hc).
    + exact (lp_not_owned_hi L' A' mem' md' a HM' Hc).
    + lia.
    + intros He. hnf in He. lia.
    + intros Hs. hnf in Hs. unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hs. lia.
  - apply WW; [|exact Hw]. destruct Ha as [Ha|Ha]; [left; lia | right; exact Ha].
Qed.

Definition LP_KW : Z := 12240.

Lemma lp_pjw_kw : forall t, (PjTree.depth t <= 32)%nat -> pj_write_c.PJW_K t <= LP_KW.
Proof.
  intros t Hd. unfold pj_write_c.PJW_K, write_value_c.WV_K, LP_KW.
  assert (H0 : 0 <= Z.of_nat (PjTree.depth t) <= 32) by lia.
  assert (C : 0 <= write_value_c.WV_FR /\
              pj_write_c.PJW_FR + Z.max (write_value_c.WV_FR * 33 + write_value_c.WV_KMAX) (Z.max put_c.PUT_K ALLOC_STACK)
                <= 12240 /\ 0 <= pj_write_c.PJW_FR /\ 0 <= write_value_c.WV_KMAX) by (vm_compute; repeat split; discriminate).
  destruct C as (C1 & C2 & C3 & C4).
  assert (M : write_value_c.WV_FR * (Z.of_nat (PjTree.depth t) + 1) <= write_value_c.WV_FR * 33) by nia.
  lia.
Qed.

Lemma lp_check_reject_clean_starved_kw : forall KW : Z,
  (forall t, (PjTree.depth t <= 32)%nat -> pj_write_c.PJW_K t <= KW) ->
  forall fx' : FPState, @check_reject_clean_starved_c.check_reject_clean_starved_contract fx' rc B API pack_form KW.
Proof.
  intros KW HK fx'.
  exact (check_reject_clean_starved.check_reject_clean_starved_holds B API KW pack_form lp_ax lp_globals
    lp_alloc_live lp_alloc_count lp_alloc_fail lp_check_reject_clean lp_pj_parse (lp_pj_write_need KW HK) lp_fuzz_free).
Qed.

Lemma lp_check_reject_clean_starved : forall fx' : FPState,
  @check_reject_clean_starved_c.check_reject_clean_starved_contract fx' rc B API pack_form LP_KW.
Proof. exact (lp_check_reject_clean_starved_kw LP_KW lp_pjw_kw). Qed.

Lemma lp_round_trip_text : forall fx' : FPState, @round_trip_text_c.round_trip_text_contract fx' rc B API pack_form.
Proof.
  intros fx'.
  eapply (round_trip_text.round_trip_text_holds_w B API pack_form).
  all: first [ exact lp_segs | exact FA | exact lp_free_at | exact lp_free_r | exact lp_pj_write | exact lp_tx_put
             | exact lp_tx_value | exact lp_strcmp | exact lp_strlen | exact lp_same | exact lp_memcpy
             | exact lp_parse_noting | exact lp_alloc_ran_out | exact lp_fuzz_free | exact lp_pj_free ].
Qed.

Lemma lp_pj_write_hyp : forall fx' : FPState, @PjWriteHyp.pj_write_hyp fx' rc B API pack_form pj_write_c.PJW_K.
Proof. intros fx'. exact (PjWriteAdapt.pj_write_adapt B API pack_form lp_ax lp_pj_write). Qed.

Lemma lp_check_round_trip : forall fx' : FPState, @check_round_trip_c.check_round_trip_contract fx' rc B API pack_form.
Proof.
  eapply (check_round_trip.check_round_trip_holds B API pack_form).
  all: first [ exact lp_ax | exact lp_globals | exact lp_round_trip_text | exact lp_pj_string | exact lp_pj_set
             | exact lp_pj_write_hyp | exact lp_parse_noting | exact lp_fuzz_free | exact lp_pj_free | exact lp_strlen
             | exact lp_strcmp | exact lp_same | exact lp_memset | exact lp_alloc_ran_out
             | exact round_trip_text.rtt_pjw_k ].
Qed.

Lemma lp_read_members : read_members_c.read_members_contract.
Proof. exact (read_members.read_members_holds lp_pj_get lp_pj_get_str). Qed.

Context {SH : sink_head} {SK : sink_syms}.

Lemma lp_kw0 : 0 <= LP_KW /\ 112 + check_reject_clean_starved_c.CRCS_K LP_KW <= SLOT_K.
Proof. vm_compute. repeat split; discriminate. Qed.

Lemma lp_kw1 : 0 <= LP_KW <= ReaderRes.PJ_PARSE_K.
Proof. vm_compute. repeat split; discriminate. Qed.

Lemma lp_entry_sr : forall ra empty stk, @EntrySR.entry_sr_contract fx rc B API SH SK pack_form ra empty stk.
Proof.
  intros ra empty stk.
  eapply EntrySRHolds.entry_sr_holds.
  all: first [ exact lp_segs | exact FA | exact lp_kw0 | exact lp_kw1 | exact lp_check_no_overread | exact lp_parse_noting
             | exact lp_check_as_written | exact lp_check_reject_clean_starved | exact lp_check_round_trip
             | exact lp_pj_free | exact lp_alloc_live | exact lp_alloc_count | exact lp_alloc_peak
             | exact lp_alloc_peak_reset | exact lp_check_bounded_alloc | exact lp_check_reject_clean
             | exact lp_read_members | exact lp_alloc_ran_out | exact lp_alloc_ran_out_reset | exact lp_alloc_most ].
Qed.

End LinkPlain.
