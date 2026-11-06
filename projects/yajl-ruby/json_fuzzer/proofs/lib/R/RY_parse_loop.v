(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel SFW1_lemmas InitMem Arr FP NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMallocTree RMalloc_iface RYajlRep RYajl_iface RY_lib RY_rz RY_kit2 RY_parse_kit RY_parse_kitJ RY_parse_kitD RY_parse_kitV RY_parse_gv RY_parse_sep RY_parse_agv RY_parse_mgv RY_parse_map RY_parse_map2 RY_parse_val RY_parse_val2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc Prelim YajlBase YajlBuf YajlLex YajlDecode YajlParser YajlLeaf YajlFactsBuf YajlFactsLex YajlFactsDecode YajlFactsParse YajlFactsLoop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope yprog_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section S.
Variable HK : RawAlloc.PState -> list block -> (word -> option byte) -> Model -> Prop.
Hypothesis HKS : HK_silent_stmt HK.
Hypothesis HKP : HK_perm_stmt HK.
Hypothesis HKF : HK_frame_stmt HK.
Hypothesis HKB : HK_blocks_stmt HK.
Notation buf_rep := (buf_rep rsegs).
Notation buf_struct := (buf_struct rsegs).
Notation buf_data := (buf_data rsegs).
Notation lexer_rep := (lexer_rep rsegs).
Notation hand_rep := (hand_rep rsegs ryc).
Notation hand_struct := (hand_struct rsegs ryc).
Notation bs_rep := (bs_rep rsegs).
Notation ctx_rep := (ctx_rep rsegs).
Notation text_at := (text_at rsegs).
Notation RYST := (RYST HK).
Notation yparse_head_inv := (yparse_head_inv HK).
Notation yparse_exit_cont := (yparse_exit_cont HK).
Notation pmem := (pmem HK).
Notation again_cont := (again_cont HK).
Notation exit_cont := (exit_cont HK).
Notation yhead_invX := (yhead_invX HK).

Hypothesis YLX : ylex_lex_stmt HK.
Hypothesis YWR : ywrap_realloc_stmt HK.
Hypothesis YRP : yreset_parser_stmt.
Hypothesis YCN : ycb_null_stmt.
Hypothesis YCB : ycb_boolean_stmt.
Hypothesis YCNUM : ycb_number_stmt.
Hypothesis YCS : ycb_string_stmt.
Hypothesis YCSM : ycb_start_map_stmt.
Hypothesis YCSA : ycb_start_array_stmt.
Hypothesis YCEA : ycb_end_array_stmt.
Hypothesis VSE : val_esc_stmt HK.
Hypothesis YCEM : ycb_end_map_stmt.
Hypothesis YCMK : ycb_map_key_stmt.
Hypothesis YSD : ystring_decode_stmt HK.
Hypothesis YBC : ybuf_clear_stmt.
Hypothesis YBE : ybuf_err_stmt.
Hypothesis YBD : ybuf_data_stmt.
Hypothesis YBL : ybuf_len_stmt.
Hypothesis YBS : ybs_set_stmt.
Ltac lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       end).

Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in change c with v; cbv iota
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma pass_done : forall E m mo s h mh cx obw olw st rest
    (rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v : word),
  pok E -> pmem E m mo s [] h mh cx obw olw -> h = p_h E -> cx = p_cx E ->
  h_stack h = st :: rest -> lex_state st = false ->
  exit_cont E ->
  realizes_cfg acfg rsegs (mkCfg (yparse_head_state rav (p_sp E) (p_gp E) (p_tp E) (p_s0 E) (p_s1 E) (p_s2 E) (p_s3 E) (p_s4 E) (p_s5 E)
                           (p_s6 E) (p_s7 E) (p_s8 E) (p_s9 E) (p_s10 E) (p_s11 E) (p_F E) (p_fc E) m
                           (pH E) (p_T E) (pLEN E) (h_used h) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v) mo) (p_K E).
Proof.
  intros until s8v. intros OK PM EH ECX HST LS EX. open_env HKB OK PM.
  clear ERR TXT LXR DBR. unfold yparse_head_state, pH.
  rz_seg HKS HK0.
  eapply evt_cut.
  { eapply (head_dispatch _ _ _ _ (p_s0 E) (p_s1 E) (p_s2 E) (p_s3 E) (p_s4 E) (p_s5 E) (p_s6 E) (p_s7 E) (p_s8 E) (p_s9 E) (p_s10 E) (p_s11 E));
      [exact HST| exact EHA| reflexivity| | exact SC| clear -B2; lia| clear -B3; lia| exact MI].
    unfold hand_cells, hand_head_cells, alloc_cells. cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ryc app]. unfold wz. rewrite EHA. exact HC. }
  intros ms' ->. unfold wz.
  destruct st; try discriminate; cbn [state_target].
  - (* [comment removed for export] *)
    apply evt_done.
    pose proof (J_exit HK HKS E) as JE. unfold pstate, pH, wz in JE. eapply JE with (st := YS_ok); [exact OK| exact PM| | exact EX].
    subst h cx. unfold yparse_step. rewrite (ybs_current_eq _ _ _ HST). cbn [ybind]. apply yl_ret.
  - (* [comment removed for export] *)
    zstep. step. apply evt_done.
    pose proof (J_exit HK HKS E) as JE. unfold pstate, pH, wz in JE. eapply JE with (st := YS_error); [exact OK| exact PM| | exact EX].
    subst h cx. unfold yparse_step. rewrite (ybs_current_eq _ _ _ HST). cbn [ybind]. apply yl_ret.
  - (* [comment removed for export] *)
    zstep. step. apply evt_done.
    pose proof (J_exit HK HKS E) as JE. unfold pstate, pH, wz in JE. eapply JE with (st := YS_error); [exact OK| exact PM| | exact EX].
    subst h cx. unfold yparse_step. rewrite (ybs_current_eq _ _ _ HST). cbn [ybind]. apply yl_ret.
Qed.

(* [comment removed for export] *)
Lemma pass_all : forall E m mo s h mh cx obw olw
    (rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v : word),
  pok E -> pmem E m mo s [] h mh cx obw olw -> h = p_h E -> cx = p_cx E ->
  again_cont E -> exit_cont E ->
  realizes_cfg acfg rsegs (mkCfg (yparse_head_state rav (p_sp E) (p_gp E) (p_tp E) (p_s0 E) (p_s1 E) (p_s2 E) (p_s3 E) (p_s4 E) (p_s5 E)
                           (p_s6 E) (p_s7 E) (p_s8 E) (p_s9 E) (p_s10 E) (p_s11 E) (p_F E) (p_fc E) m
                           (pH E) (p_T E) (pLEN E) (h_used h) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v) mo) (p_K E).
Proof.
  intros until s8v. intros OK PM EH ECX AG EX.
  pose proof OK as (_ & LP & U0 & _).
  destruct (h_stack h) as [|st rest] eqn:HST.
  { exfalso. subst h. unfold h_used in U0. rewrite HST in U0. revert U0. clear. intros U0. cbv in U0. discriminate. }
  destruct st.
  - eapply pass_val; try eassumption; reflexivity.
  - eapply pass_done; try eassumption; reflexivity.
  - eapply pass_done; try eassumption; reflexivity.
  - eapply pass_done; try eassumption; reflexivity.
  - eapply pass_map; try eassumption; reflexivity.
  - eapply pass_sep; try eassumption; reflexivity.
  - eapply pass_val; try eassumption; reflexivity.
  - eapply pass_mgv; try eassumption; reflexivity.
  - eapply pass_map; try eassumption; reflexivity.
  - eapply pass_val; try eassumption; reflexivity.
  - eapply pass_agv; try eassumption; reflexivity.
  - eapply pass_val; try eassumption; reflexivity.
Qed.

Lemma mh_same_trans : forall a b c, mh_same a b -> mh_same b c -> mh_same a c.
Proof.
  intros a b c H1 H2. unfold mh_same in *.
  destruct H1 as (? & ? & ? & ? & ? & ? & ? & ? & ?). destruct H2 as (? & ? & ? & ? & ? & ? & ? & ? & ?).
  repeat split; congruence.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma yparse_loopX : forall (fuel : nat) (K : TSet) (ra sp gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v : word)
    (mo : Model) (s : PState) (REST : list block) (h : yhandle) (mh : mhand) (cx : yctx) (T : Z) (txt : list Z) (lo B : Z),
  K [] ->
  yhead_invX ra sp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m mo s REST h mh cx T txt lo B ->
  passes_left (zlength txt) h <= Z.of_nat fuel ->
  yparse_exit_cont K ra sp gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m REST mh T txt lo B
     (yleaf (yparse_loop jf_callbacks txt (zlength txt) fuel h cx)) ->
  realizes_cfg acfg rsegs (mkCfg (yparse_head_state rav sp gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m
                           (mh_addr mh) T (zlength txt) (h_used h) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v) mo) K.
Proof.
  induction fuel as [|fuel IH]; intros until B; intros K0 HIX FUEL EXIT.
  { exfalso. destruct HIX as ((_ & _ & _ & _ & _ & _ & LP & _) & _). pose proof (loop_pre_passes_left_pos _ _ _ LP). clear -H FUEL. cbn in FUEL. lia. }
  destruct HIX as ((RY & HR & CXR & TXT & L26 & TB & LP & U0 & YR8 & (padw & obw & olw & FR) & AX & SPC & CXB & STK & CEIL & LO & ERR & MI & TP) & SB1).
  pose proof AX as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & _ & _ & _ & CB0 & Bav & AV144 & _).
  set (E := mkPE ra sp gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc T txt lo B K m REST mh h cx).
  assert (OK : pok E).
  { unfold pok, E, pSP, pCX, pLEN. cbn. unfold alloc_ceiling, RY_DO_PARSE_STACK, RY_DECODE_STACK, RY_BUF_APPEND_STACK, RY_WRAP_STACK in *.
    repeat split; try assumption; clear -SPC CXB CEIL LO Bav AV144 CB0; lia. }
  assert (PM : pmem E m mo s [] h mh cx obw olw).
  { unfold RY_parse_kit.pmem, E, pSP, pCX. cbn. split; [exact RY|]. split; [exact HR|]. split; [repeat split; reflexivity|].
    split; [exact CXR|]. split; [exact TXT|]. split; [exists padw; exact FR|]. split; [exact AX|]. split; [exact STK|].
    split; [exact ERR|]. split; [exact MI|]. split; [apply ry_pres_refl|]. split; [exact SB1| reflexivity]. }
  change (realizes_cfg acfg rsegs (mkCfg (yparse_head_state rav (p_sp E) (p_gp E) (p_tp E) (p_s0 E) (p_s1 E) (p_s2 E) (p_s3 E) (p_s4 E) (p_s5 E)
                           (p_s6 E) (p_s7 E) (p_s8 E) (p_s9 E) (p_s10 E) (p_s11 E) (p_F E) (p_fc E) m
                           (pH E) (p_T E) (pLEN E) (h_used h) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v) mo) (p_K E)).
  eapply pass_all; [exact OK| exact PM| reflexivity| reflexivity| |].
  - (* [comment removed for export] *)
    unfold again_cont, E, pSP, pCX, pLEN, pH. cbn. intros rav' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' s5v' s6v' s8v' m' mo' s' h' cx' mh' LK YLS SAME PRES LKN HIX'.
    destruct (yparse_step_again_facts txt (zlength txt) h cx h' cx' eq_refl ltac:(clear -L26; lia) LP YLS) as (LP' & U1 & PL').
    pose proof SAME as (_ & EHA & _ & _ & _ & _ & _ & _ & ECX). rewrite <- EHA.
    eapply (IH K ra sp gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m' rav' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' s5v' s6v' s8v' mo' s' (LK ++ REST) h' mh' cx' T txt lo B);
      [exact K0| exact HIX'| clear -PL' FUEL; lia|].
    unfold yparse_exit_cont in EXIT |- *. intros until LK0. intros FP' R' A0' HR' SAME' CXR' TXT' LK0N RY' FS'.
    destruct FP' as (MI'' & STK'' & ERR'' & AX'' & PRES'').
    assert (E144 : bv_unsigned (wz (bv_unsigned sp + 144)) = bv_unsigned sp + 144) by (unfold wz; apply unsigned_lit; clear -SPC CXB Bav AV144; pose proof (bv_unsigned_in_range 64 sp); lia).
    rewrite E144 in STK'', PRES''.
    eapply (EXIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (LK0 ++ LK)).
    + split; [exact MI''|]. split; [rewrite E144; exact STK''|]. split; [exact ERR''|]. split; [exact AX''|]. rewrite E144.
      eapply ry_pres_trans; [exact PRES|]. rewrite ECX in PRES''. eapply ry_pres_weaken; [exact PRES''| clear; lia| intros b Hb; apply in_or_app; right; exact Hb| intros a Hx; exact Hx].
    + eapply yparse_loop_leaf_again; [exact YLS| exact R'].
    + exact A0'.
    + exact HR'.
    + eapply mh_same_trans; [exact SAME| exact SAME'].
    + rewrite <- ECX. exact CXR'.
    + exact TXT'.
    + rewrite LK0N, LKN. reflexivity.
    + rewrite <- app_assoc. exact RY'.
    + exact FS'.
  - (* [comment removed for export] *)
    unfold exit_cont, E. cbn. unfold yparse_exit_cont in EXIT |- *. intros until LK. intros FP' R' A0' HR' SAME' CXR' TXT' LKN RY' FS'.
    eapply EXIT; [exact FP'| apply yparse_loop_leaf_done; exact R'| exact A0'| exact HR'| exact SAME'| exact CXR'| exact TXT'| exact LKN| exact RY'| exact FS'].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ownE (H lo SP : Z) (iv : Z * Z) : Prop :=
  (H <= fst iv /\ snd iv <= H + 72) \/ (lo <= fst iv /\ snd iv <= SP).

Lemma ownE_outside : forall H lo SP W a,
  Forall (ownE H lo SP) W -> (a < H \/ H + 72 <= a) -> (a < lo \/ SP <= a) -> outside W a.
Proof.
  intros H lo SP W a HF H1 H2. induction HF as [| [lo' hi] W HO HF IH]; [exact I|].
  cbn. split; [| exact IH]. unfold ownE in HO. cbn [fst snd] in HO. lia.
Qed.

(* [comment removed for export] *)
Lemma entry_upd : forall s REST m m' mo h h' mh cx T txt (lo SP : Z) W,
  RYST s (yblocks mh h ++ REST) m mo -> hand_rep m h mh -> ctx_rep m (mh_ctx mh) cx -> text_at m T txt ->
  ((exists bt, In bt REST /\ blk_addr bt <= T /\ T + zlength txt <= blk_addr bt + blk_size bt) \/ zlength txt = 0) ->
  h_stack_blk h <> None ->
  munch W m m' -> wmono rsegs m m' -> Forall (ownE (mh_addr mh) lo SP) W ->
  alloc_ceiling <= lo -> lo <= SP -> SP <= mh_ctx mh ->
  hand_struct m' h' mh -> h_lexer h' = h_lexer h -> h_decbuf h' = h_decbuf h -> h_stack h' = h_stack h ->
  h_stack_size h' = h_stack_size h -> h_stack_blk h' = h_stack_blk h ->
  RYST s (yblocks mh h' ++ REST) m' mo /\ hand_rep m' h' mh /\ ctx_rep m' (mh_ctx mh) cx /\ text_at m' T txt.
Proof.
  intros until W. intros RY HR CXR TXT TB SB1 MU WM OWN CEIL LOSP SPC HS' EL ED EST ESZ EB.
  apply RYST_split in RY. destruct RY as [HK0 YS]. destruct (HK_blocks HK HKB _ _ _ _ HK0) as [RNG SEP].
  destruct HR as (HS & LXR & DBR & BSR).
  pose proof (munch_agree _ _ _ MU WM) as AG.
  rewrite <- (app_nil_l REST) in HK0, RNG, SEP. rewrite (yblocks_mid mh h [] REST SB1) in RNG, SEP, HK0.
  set (MID := mid_blocks mh h) in *.
  cbn [all_sep] in SEP. destruct SEP as [SEPH SEPT].
  pose proof (all_range_In _ _ RNG (or_introl eq_refl)) as R1. unfold rblock_range, alloc_ceiling, SIZEOF_HANDLE in R1. cbn [blk_addr blk_size fst snd] in R1.
  unfold alloc_ceiling in CEIL.
  assert (OUT : forall y a, In y (MID ++ (mh_sid mh, mh_stack mh, h_stack_size h) :: [] ++ REST) -> blk_addr y <= a < blk_addr y + blk_size y -> outside W a).
  { intros y a Hy Ha. pose proof (all_range_In _ _ RNG (or_intror Hy)) as Ry. unfold rblock_range, alloc_ceiling in Ry.
    pose proof (sep_from_In _ _ _ SEPH Hy) as D1. unfold bsep, SIZEOF_HANDLE in D1. cbn [blk_addr blk_size fst snd] in D1.
    eapply ownE_outside; [exact OWN| clear -Ha D1; lia| clear -Ha Ry CEIL; lia]. }
  assert (OUTI : forall a, 0x23000 <= a < 0x56000 -> outside W a).
  { intros a Ha. eapply ownE_outside; [exact OWN| clear -Ha R1; lia| clear -Ha CEIL; lia]. }
  assert (ILX : In (mh_lid mh, mh_lexer mh, SIZEOF_LEXER) MID) by (unfold MID, mid_blocks, lexer_blocks; left; reflexivity).
  assert (ILB : In (mb_id (mh_lexbuf mh), mb_addr (mh_lexbuf mh), SIZEOF_BUF) MID) by (unfold MID, mid_blocks, lexer_blocks, buf_blocks; right; left; reflexivity).
  assert (ILD : yb_data (lx_buf (h_lexer h)) <> None -> In (mb_did (mh_lexbuf mh), mb_data (mh_lexbuf mh), yb_len (lx_buf (h_lexer h))) MID).
  { intros HD. unfold MID, mid_blocks, lexer_blocks, buf_blocks. right. destruct (yb_data (lx_buf (h_lexer h))); [| congruence]. right. left. reflexivity. }
  assert (IDB : In (mb_id (mh_decbuf mh), mb_addr (mh_decbuf mh), SIZEOF_BUF) MID) by (unfold MID, mid_blocks; apply in_or_app; right; left; reflexivity).
  assert (IDD : yb_data (h_decbuf h) <> None -> In (mb_did (mh_decbuf mh), mb_data (mh_decbuf mh), yb_len (h_decbuf h)) MID).
  { intros HD. unfold MID, mid_blocks, buf_blocks. apply in_or_app. right. destruct (yb_data (h_decbuf h)); [| congruence]. right. left. reflexivity. }
  assert (INM : forall y, In y MID -> In y (MID ++ (mh_sid mh, mh_stack mh, h_stack_size h) :: [] ++ REST)) by (intros y Hy; apply in_or_app; left; exact Hy).
  split; [| split; [| split]].
  - apply RYST_split. rewrite <- (app_nil_l REST). rewrite (yblocks_mid mh h' [] REST) by (rewrite EB; exact SB1).
    replace (mid_blocks mh h') with MID by (unfold MID, mid_blocks; rewrite EL, ED; reflexivity). rewrite ESZ. split.
    + eapply HKF; [exact HK0| exact MU| exact WM|].
      eapply Forall_impl; [| exact OWN]. intros iv Hiv. unfold ownE in Hiv. unfold rclient_write_ok.
      destruct Hiv as [Hiv|Hiv]; [right; right; eexists; split; [left; reflexivity| cbn; unfold SIZEOF_HANDLE; clear -Hiv; lia]| left; clear -Hiv CEIL; unfold alloc_ceiling; lia].
    + eapply ystatics_munch; [exact YS| exact MU| exact WM|].
      eapply Forall_impl; [| exact OWN]. intros iv Hiv. unfold ownE in Hiv. unfold RY_CALLBACKS. clear -Hiv R1 CEIL. lia.
  - split; [exact HS'|]. split; [| split].
    + rewrite EL. eapply lexer_rep_agree; [exact AG| exact LXR| | |].
      * intros a Ha. apply (OUT _ a (INM _ ILX)). cbn. exact Ha.
      * intros a Ha. apply (OUT _ a (INM _ ILB)). cbn. exact Ha.
      * intros HD a Ha. apply (OUT _ a (INM _ (ILD HD))). cbn. exact Ha.
    + rewrite ED. eapply buf_rep_agree; [exact AG| exact DBR| |].
      * intros a Ha. apply (OUT _ a (INM _ IDB)). cbn. exact Ha.
      * intros HD a Ha. apply (OUT _ a (INM _ (IDD HD))). cbn. exact Ha.
    + eapply bs_rep_agree; [exact AG| | | ].
      * unfold RYajlRep.bs_rep in BSR |- *. rewrite EB, EST, ESZ. unfold h_used. rewrite EST. unfold h_used in BSR. exact BSR.
      * rewrite ESZ. intros a Ha. apply (OUT (mh_sid mh, mh_stack mh, h_stack_size h)); [apply in_or_app; right; left; reflexivity| cbn; exact Ha].
      * destruct HS as (_ & _ & _ & B3 & _). unfold h_used in B3 |- *. rewrite EST, ESZ. exact B3.
  - eapply ctx_rep_agree; [exact AG| exact CXR|]. intros a Ha. eapply ownE_outside; [exact OWN| clear -Ha R1 CEIL LOSP SPC; lia| clear -Ha SPC; lia].
  - eapply text_at_agree; [exact AG| exact TXT|]. intros a Ha. destruct TB as [(bt & HIN & HB)|Z0]; [| clear -Ha Z0; lia].
    apply (OUT bt a); [apply in_or_app; right; right; exact HIN| clear -Ha HB; lia].
Qed.

Lemma ydo_parse_spec : ydo_parse_stmt HK.
Proof.
  unfold ydo_parse_stmt. intros REST h mh cx T txt lo B errv K. intros until s. intros K0 RY HR CXR TXT L26 TB HINV SPC CXB YR8 FP A0 A1 A2 CONT.
  destruct FP as (AX & SPB & STK & CEIL & LO & ERR & MI & TP).
  pose proof HR as (HS & LXR & DBR & BSR). pose proof HS as ((pew & pad & HC & PW) & BC1 & BC2 & BC3 & BC4).
  pose proof HINV as (LXI & OFFB & DBI & DBOK & (FROK & USZ & BLK & SZK & EOL & EAL) & DEPTH & SZB). cbn [h_stack h_stack_blk h_set_off h_stack_size] in FROK, BLK.
  assert (U0 : 0 < h_used h). { unfold h_used. destruct (h_stack h); [destruct FROK| unfold zlength; cbn [length]; clear; lia]. }
  pose proof RY as RY0. apply RYST_split in RY. destruct RY as [HK0 YS].
  destruct (HK_blocks HK HKB _ _ _ _ HK0) as [RNG _].
  pose proof (all_range_In _ _ RNG (or_introl eq_refl)) as R1. unfold rblock_range, alloc_ceiling, SIZEOF_HANDLE in R1. cbn [blk_addr blk_size fst snd] in R1.
  pose proof AX as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & _ & _ & _ & CB0 & Bav & AV144 & _).
  unfold hand_cells, hand_head_cells, alloc_cells in HC. cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ryc app] in HC.
  subst a0 a1 a2. unfold RY_DO_PARSE, RY_DO_PARSE_STACK, RY_DECODE_STACK, RY_BUF_APPEND_STACK, RY_WRAP_STACK, alloc_ceiling in *. unfold wz in HC |- *.
  rewrite (ry_errno_lit tp TP) in ERR. unfold RERRNO in ERR.
  pose proof (rw_cells_bound _ _ _ _ HC) as HCB. cbn [cells_size csize Nat.add length] in HCB. unfold zlength in L26.
  pose proof (proj1 STK) as LO0.
  clear LXR DBR BSR.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (mh_addr mh + 32, mh_addr mh + 36)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  rz_seg HKS HK0.
  zstep. carve_frame 144%nat STK.
  do 14 zstep.
  zstep. zstep. rewrite ysx32_small by (clear -BC2 BC3; lia).
  zstep.
  zstep. if_cases KU; zify_cond KU. { exfalso. revert KU U0 BC2 BC3. clear. intros. rewrite ?unsigned_lit in KU by lia. lia. }
  do 13 zstep. lit_store.
  do 3 zstep.
  zstep. lit_store.
  match goal with FR : rw_cells _ _ (bv_unsigned sp + -144) _ |- _ =>
    eapply (rw_cells_split_CB rsegs _ _ [_; _] 16 _ _ [4%nat; 4%nat; 8%nat]) in FR; [|reflexivity];
    cbn [mk_CB_cells app] in FR; ywordify FR end.
  apply evt_done.
  lazymatch goal with H : rw_cells _ ?mx (bv_unsigned sp + -144) _ |- _ => rename H into FR; rename mx into m1 end.
  lazymatch goal with H : stk _ m1 _ _ |- _ => rename H into STK1 end.
  lazymatch goal with H : mem_inv _ m1 |- _ => rename H into MI1 end.
  (* [comment removed for export] *)
  destruct (entry_upd s REST m m1 mo h (h_set_off h 0) mh cx T txt lo (bv_unsigned sp)
              [(bv_unsigned sp - 144, bv_unsigned sp); (mh_addr mh + 32, mh_addr mh + 36)]
              RY0 HR CXR TXT TB BLK MU WM) as (RY1 & HR1 & CXR1 & TXT1).
  { constructor; [| constructor; [| constructor]]; unfold ownE; cbn [fst snd]; [right; clear -CEIL LO; lia| left; clear; lia]. }
  { unfold alloc_ceiling. exact CEIL. } { clear -LO; lia. } { exact SPC. }
  { split; [| cbn [h_set_off h_bytesConsumed h_stack_size h_stack_blk h_parseError]; replace (h_used (h_set_off h 0)) with (h_used h) by reflexivity; split; [clear; lia| exact (conj BC2 (conj BC3 BC4))]].
    exists pew, pad. split; [| exact PW]. unfold hand_cells, hand_head_cells, alloc_cells.
    cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ryc app h_set_off h_bytesConsumed h_stack_size h_parseError]. unfold wz.
    replace (h_used (h_set_off h 0)) with (h_used h) by reflexivity. exact HC. }
  all: try reflexivity.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -144)) = bv_unsigned sp + -144).
  { apply unsigned_lit. pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. clear -SPR LO CEIL LO0. lia. }
  pose proof (yparse_loopX (parse_fuel (zlength txt)) K ra (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m1) as LX.
  unfold yparse_head_state, RY_PARSE_HEAD, RY_JT_TOKVAL, RY_JT_STATE, wz in LX.
  replace (h_used h) with (h_used (h_set_off h 0)) by reflexivity.
  eapply LX; clear LX; [exact K0| | apply (ydo_parse_fuel (zlength txt) h cx); [clear; unfold zlength; lia| exact HINV]|].
  - (* [comment removed for export] *)
    split; [| exact BLK]. unfold RYajl_iface.yparse_head_inv. rewrite !ESP.
    split; [exact RY1|]. split; [exact HR1|]. split; [exact CXR1|]. split; [exact TXT1|]. split; [unfold zlength; exact L26|]. split; [exact TB|].
    split; [left; exact HINV|]. split; [exact U0|]. split; [exact YR8|].
    split; [eexists _, _, _; unfold yparse_frame; rewrite ?ESP; change (2 ^ 63 + 1) with 9223372036854775809; exact FR|].
    split.
    { eapply rauxv_ok_frame; [exact AX| exact MU| exact WM|]. constructor; [| constructor; [| constructor]]; cbn; unfold RAUXV_CELL; [clear -SPB CEIL LO LO0 SPC CXB CB0; lia| clear -R1 CB0; lia]. }
    split; [clear -SPC; lia|]. split; [exact CXB|]. split; [replace (bv_unsigned sp + -144) with (bv_unsigned sp - 144) in STK1 by (clear; lia); exact STK1|].
    split; [unfold alloc_ceiling; exact CEIL|]. split; [unfold RY_DO_PARSE_STACK, RY_DECODE_STACK, RY_BUF_APPEND_STACK, RY_WRAP_STACK; clear -LO; lia|].
    split; [eexists; rewrite (ry_errno_lit tp TP); unfold RERRNO; eassumption|]. split; [exact MI1| exact TP].
  - (* [comment removed for export] *)
    unfold yparse_exit_cont. rewrite !ESP. replace (bv_unsigned sp + -144 + 144) with (bv_unsigned sp) by (clear; lia). unfold wz. rewrite Z_to_bv_bv_unsigned.
    intros until LK. intros FP' R' A0' HR' SAME' CXR' TXT' LKN RY' FS'.
    eapply CONT; [| exact FS'].
    split; [| split; [rewrite ydo_parse_unfold; exact R'| split; [exact A0'| split; [exact HR'| split; [exact SAME'| split; [exact CXR'| split; [exact TXT'| split; [exact LKN| exact RY']]]]]]]].
    destruct FP' as (MI'' & STK'' & ERR'' & AX'' & PRES''). split; [exact MI''|]. split; [exact STK''|]. split; [exact ERR''|]. split; [exact AX''|].
    eapply ry_pres_trans; [| exact PRES''].
    eapply ryajl_pres_of_munch; [exact MU| exact WM|].
    intros a Ha Hc _. cbn. destruct (HK_blocks HK HKB _ _ _ _ HK0) as [_ SEP]. cbn [all_sep yblocks app] in SEP. destruct SEP as [SEPH _].
    destruct Hc as [Hc|[[Hc _]|(b & Hb & Hr)]]; [clear -Hc R1 CEIL LO LO0; lia| clear -Hc R1 CEIL LO LO0; lia|].
    pose proof (sep_from_In _ _ _ SEPH ltac:(apply in_or_app; right; exact Hb)) as X. unfold bsep, SIZEOF_HANDLE in X. cbn [blk_addr blk_size fst snd] in X.
    pose proof (all_range_In _ _ RNG ltac:(right; apply in_or_app; right; exact Hb)) as Rb. unfold rblock_range, alloc_ceiling in Rb.
    clear -X Hr Rb CEIL LO LO0. lia.
Qed.

(* [comment removed for export] *)
Lemma yparse_spec : yparse_stmt HK.
Proof.
  unfold yparse_stmt. intros REST h mh cx T txt lo B errv K. intros until s. intros K0 RY HR CXR TXT L26 TB HINV SPC CXB YR8 FP A0 A1 A2 CONT.
  pose proof RY as RY0. apply RYST_split in RY. destruct RY as [HK0 _].
  destruct (HK_blocks HK HKB _ _ _ _ HK0) as [RNG _].
  pose proof (all_range_In _ _ RNG (or_introl eq_refl)) as R1. unfold rblock_range, alloc_ceiling in R1. cbn [blk_addr blk_size fst snd] in R1.
  pose proof FP as (_ & _ & _ & _ & _ & _ & MI & _).
  subst a0. unfold RY_PARSE, wz.
  rz_seg HKS HK0.
  zstep. if_cases KZ; zify_cond KZ. { exfalso. revert KZ R1. clear. intros. rewrite ?unsigned_lit in KZ by lia. lia. }
  zstep. apply evt_done.
  eapply ydo_parse_spec; try eassumption; reflexivity.
Qed.

End S.

End RC__1.
