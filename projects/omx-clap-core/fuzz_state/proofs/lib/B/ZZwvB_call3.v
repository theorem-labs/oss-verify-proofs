(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AE2y.v, with its module paths and module names changed; 261 of its 290 lines of code are new or changed and 675 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/ZZwv_call3.v (a working branch
   1a5dc5b2e7c): same lemma names and statements; imports point at lib/B's image files and walk kit (YB1v, YB1w,
   FSH_Base, FSH_Rt, FSPstat, FSH_Fn_writer, FSH_Fn_alloc, FSW_K, FSW_K3, FSW_ret, FSW_rres, FSW_rd, FSW_pj,
   FSW_write_value_entry for image A's FSW_writer_tbl, ZZwvB_defs, ZZwvB_inv, ZZwvB_kit, ZZwvB_comp, ZZwvB_call,
   ZZwvB_call2); the image-agnostic FSupoison, FSupoisonU, FSH_YC20, FSH_Gen, FSupoisonStack stay lib/A's.
   lib/B has no FSW_writer_model / FSW_writer_kit; this file uses
   no name of either. Proof change: image B's frame is 192 bytes (WVC_F, lib/B/FSH_Base.FRAME_write_value), not 176;
   wvc_stk's five conjuncts hold for lib/B/FSH_Base.STK_write_value (FRAME_write_value = 192 plus the zmaxl of
   STK_RT_STR, STK_put, STK_indent, STK_put_string and the level below), with the same proof.
   rule 24: proves no function (kind: segment lemma) - the container arms of write_value B.
   write_value's CONTAINER arms (fs.asan-ubsan image B, write_value 0x84010): the writer facts across ONE CALL of a
   writer callee (put, indent, put_string or write_value). From the invariant's writer facts at the call
   (ZZwvB_inv.wvc_sem at the call's memory, model state st) and the callee's post, which the four writer specs state
   alike (journal from the call with the raised top ot, uswap, wout_ok, wbudget_kept, bswap, wkeep from the callee's
   sp, fs_glob), the writer facts at the return, against the model state with the callee's pieces Pc appended
   (putN st Pc).
   Template (not a copied proof): the bespoke ASan proof a working branch lib/A/Prog/write_value_cont.v
   (wvc_keep 296-310, wvc_lam_keep 696-720, wvc_node_keep 541-548, wvc_live_sub 581-605: the facts one writer step
   keeps); the transports are the kit's (ZZwvB_kit, from a Theorem Labs lane's FSW_pj_write.v).
   Rule 24: no function proved here (write_value's lookup: lane record (internal path), CHECKER CONFIRM
   a Theorem Labs lane). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
FSupoison FSupoisonU FSH_YC20 FSH_Gen FSupoisonStack.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSH_Fn_alloc FSW_K FSW_K3 FSW_ret FSW_rres FSW_rd FSW_pj
FSH_Fn_writer FSW_write_value_entry ZZwvB_defs ZZwvB_inv ZZwvB_kit ZZwvB_comp ZZwvB_call ZZwvB_call2.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterValue PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance
   resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section C. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the writer facts across one call: st is the model state at the call (any w_calls), the callee is called with its
   reset wv_rst st and writes Pc; its post is given at the callee state putN (wv_rst st) Pc *)
Lemma wvc_sem_call : forall F ly0 S0 U0 W0 mem0 regs0 ly S U (W : world tfibsegs) m md buf st Pc
    ly' S' U' (W' : world tfibsegs) m' md' buf' STKc kc spc peak,
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly S U W m buf st ->
  ARU tfibsegs B ly S U W m md ->
  0 <= wf_cap0 F -> wf_cap0 F <= WriterApp.w_cap st -> 0 <= wf_cnt0 F ->
  wf_cnt0 F + wcalls (WriterApp.putN st Pc) < 2 ^ 64 ->
  alloc_ceiling <= wf_sp F - WVC_F -> wf_o F + 32 <= wf_ot F ->
  wf_peak0 F <= peak <= Z.max (wf_peak0 F) (wf_live F - wf_cap0 F + WriterApp.w_cap st) ->
  ajournal tfibsegs B STKc (wf_ot F) (FS_PSTAT_FP ++ wbuf_fp buf (WriterApp.w_cap st)) ly S W (unpoison U m) md []
    ly' S' W' (unpoison U' m') md' kc ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' m' U' ->
  uswap U U' buf buf' (WriterApp.w_cap st) ->
  wout_ok B tfibsegs ly' S' W' m' (wf_o F) buf' (WriterApp.w_cap (WriterApp.putN (wv_rst st) Pc))
    (WriterApp.w_failed (WriterApp.putN (wv_rst st) Pc)) (WriterApp.w_text (WriterApp.putN (wv_rst st) Pc)) ->
  wbudget_kept S S' (WriterApp.w_failed st) (WriterApp.w_cap st) (WriterApp.w_cnt st)
    (WriterApp.w_failed (WriterApp.putN (wv_rst st) Pc)) (WriterApp.w_cap (WriterApp.putN (wv_rst st) Pc))
    (WriterApp.w_cnt (WriterApp.putN (wv_rst st) Pc)) ->
  bswap (ablocks B ly S) (ablocks B ly' S') buf buf' (WriterApp.w_cap st)
    (WriterApp.w_cap (WriterApp.putN (wv_rst st) Pc)) ->
  wkeep tfibsegs W W' m m' spc (wf_ot F) (wf_o F) 32 -> spc <= wf_sp F ->
  (exists peak', peak <= peak' <= Z.max peak ((wf_live F + WriterApp.w_cap st - wf_cap0 F) - WriterApp.w_cap st +
                                            WriterApp.w_cap (WriterApp.putN (wv_rst st) Pc)) /\
     fs_glob tfibsegs W' m' ((wf_live F + WriterApp.w_cap st - wf_cap0 F) +
                             WriterApp.w_cap (WriterApp.putN (wv_rst st) Pc) - WriterApp.w_cap st) peak'
       (WriterApp.w_cnt (WriterApp.putN (wv_rst st) Pc)) (WriterApp.w_fail (WriterApp.putN (wv_rst st) Pc))) ->
  ARU tfibsegs B ly' S' U' W' m' md' /\
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly' S' U' W' m' buf' (WriterApp.putN st Pc).
Proof.
intros F ly0 S0 U0 W0 mem0 regs0 ly S U W m md buf st Pc ly' S' U' W' m' md' buf' STKc kc spc peak
  HSEM HARU Hcap0 Hcap0i Hcnt0 Hcnt Hlo Hoot Hpk HJc OK' PO' HUS' HOUT' HBK' HBS' HWK' Hspc HGL'.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HWF : WVC_F = 192) by reflexivity.
pose proof (wvc_sem_o_sp B F ly0 S0 U0 W0 mem0 regs0 ly S U W m buf st HSEM) as Hosp.
pose proof (proj1 HARU) as HAR.
assert (HARU' : ARU tfibsegs B ly' S' U' W' m' md') by (split; [exact (proj1 HJc) | split; [exact OK' | exact PO']]).
pose proof (proj1 HARU') as HAR'.
split; [exact HARU'|].
(* the model: the callee state's fields are the full state's *)
destruct (wv_putN_calls_indep st Pc) as (Ef & Et & Ecp & En & El & Ecl).
set (stc := WriterApp.putN (wv_rst st) Pc) in *.
assert (Ewc : wcalls (WriterApp.putN st Pc) = wcalls st + wcalls stc).
{ unfold wcalls. rewrite Ecl, length_app, Nat2Z.inj_add. reflexivity. }
destruct HSEM as (HOUT & HGL & HHD & HUS & HBS & HBK & HCNT & HWK & HN & HPO & HNB & HUL & HD & HROOT & HBIN & HB0 &
  HRO & H8 & HC & HU0).
set (cap := WriterApp.w_cap st) in *.
set (cap' := WriterApp.w_cap stc) in *.
pose proof HOUT as (_ & _ & _ & _ & _ & Hcap64 & _).
pose proof HOUT' as (_ & _ & _ & _ & _ & Hcap64' & _ & _ & _ & _ & _ & _ & Hcase').
assert (Hc : 0 <= cap) by lia. assert (Hc' : 0 <= cap') by lia.
assert (Hnew : cap' <> 0 -> In (buf' - HEAD, cap' + HEAD) (ablocks B ly' S')).
{ intros Hz. destruct Hcase' as [(E & _) | (_ & (Hin & _) & _)]; [exfalso; exact (Hz E) | exact Hin]. }
assert (Hb0' : cap' = 0 -> buf' = 0).
{ intros Hz. destruct Hcase' as [(_ & E & _) | ((j & Hj & Ej) & _)]; [exact E|].
  exfalso. rewrite Ej in Hz. pose proof (Z.pow_pos_nonneg 2 j ltac:(lia) ltac:(lia)). lia. }
assert (Hmono : cap <= cap') by exact (wv_cap_mono (wv_rst st) Pc Hc).
(* the tree's footprint is off the call's footprint, its blocks stay live *)
pose proof (wvc_foot_off_fp B ly S W (unpoison U m) md m (wf_v F) (wf_D F) buf cap HAR HPO HUL
  (fun a k H => proj2 (HD a k H)) HROOT HBIN Hc) as HFOOT.
pose proof (wvc_foot_live B ly S ly' S' W W' (unpoison U m) md (unpoison U' m') md' (wf_v F) (wf_D F) buf buf' cap cap'
  HAR HAR' HBS' Hnew HB0 Hc HFOOT) as HLIVE.
destruct (wvc_fp_aux B ly S W (unpoison U m) md buf cap HAR HBIN Hc) as (HFPS & HCL & HFRO).
assert (HHD' : fs_heads B ly' S' U').
{ exact (wv_heads_swap B ly S U W m md ly' S' U' W' m' md' buf buf' cap cap' HARU HARU' HHD HUS' HBS' HBIN Hnew
    HB0 Hb0' Hc Hc'). }
pose proof (wvc_D_live B ly S ly' S' W W' (unpoison U' m') md' m (wf_D F) buf buf' cap cap' HAR' HBS' Hnew Hc' HUL
  (fun a k H => proj2 (HD a k H))) as HDL.
unfold wvc_sem.
split.
{ rewrite Ecp, Ef, Et. exact HOUT'. }
split.
{ destruct HGL' as (peak' & Hpk' & HG'). exists peak'.
  destruct (wv_peak_chain (wf_peak0 F) peak peak' (wf_live F) (wf_live F + cap - wf_cap0 F) (wf_cap0 F) cap cap'
    ltac:(lia) Hmono (proj1 Hpk) (proj2 Hpk) (proj1 Hpk') (proj2 Hpk')) as (P1 & P2).
  rewrite Ecp, En, El. split; [split; [exact P1 | exact P2]|].
  replace (wf_live F + cap' - wf_cap0 F) with (wf_live F + cap - wf_cap0 F + cap' - cap) by lia. exact HG'. }
split; [exact HHD'|].
split.
{ exact (wv_uswap_trans B ly S W (unpoison U m) md U0 U U' (wf_buf0 F) buf buf' (wf_cap0 F) cap HAR
    (proj1 (proj2 HARU)) HHD HB0 Hcap0 Hcap0i HUS HUS'). }
split.
{ rewrite Ecp. exact (wv_bswap_trans B ly S W (unpoison U m) md _ _ _ (wf_buf0 F) buf buf' (wf_cap0 F) cap cap'
    HAR eq_refl HBIN HB0 Hc Hc' HBS HBS'). }
split.
{ rewrite Ef, Ecp, En. exact (wv_budget_kept_trans S0 S S' _ _ _ _ _ _ _ _ _ HBK HBK'). }
split.
{ pose proof (wv_cnt_calls (wv_rst st) Pc eq_refl ltac:(cbn [wv_rst WriterApp.w_cnt]; unfold wcalls in *; lia)
    ltac:(cbn [wv_rst WriterApp.w_cnt]; fold stc; unfold wcalls in *; lia)) as EC.
  fold stc in EC. cbn [wv_rst WriterApp.w_cnt] in EC. rewrite En, Ewc. lia. }
split.
{ exact (wv_wkeep_trans W0 W W' mem0 m m' (wf_sp F) (wf_ot F) (wf_o F) HWK
    (wv_wkeep_mono W W' m m' spc (wf_sp F) (wf_ot F) (wf_o F) Hspc HWK')). }
split.
{ exact (zwk_pj_node_journal B STKc (wf_ot F) _ ly S U W m md [] ly' S' U' W' m' md' kc _ (wf_v F) (wf_t F) (wf_D F)
    (wf_D F) HJc HARU HARU' HPO HUL (fun a k H => H) HLIVE HFOOT HN). }
split.
{ exact (zwk_pobj_journal B STKc (wf_ot F) _ ly S U W m md [] ly' S' U' W' m' md' kc (wf_v F) (wf_D F) (wf_D F)
    HJc HARU HARU' HPO HUL (fun a k H => H) HLIVE HFOOT HHD' HFPS). }
split.
{ intros x Hx. rewrite <- (HNB x Hx). rewrite <- (Z_to_bv_bv_unsigned 64 x).
  refine (proj2 (zwk_j_foot_kept B STKc (wf_ot F) _ ly S U W m md [] ly' S' U' W' m' md' kc (wf_v F) (wf_D F) (wf_D F)
    (bv_unsigned x) HJc HARU HARU' HPO HUL (fun a k H => H) HLIVE HFOOT _)). left. exact Hx. }
split.
{ apply (zwk_ublocks_journal B STKc (wf_ot F) _ ly S U W m md [] ly' S' U' W' m' md' kc (wf_D F) HJc HARU HARU' HUL).
  - intros a kk Hak. exact (proj1 (HDL a kk Hak)).
  - intros a kk i Hak Hi Hin. destruct (HUL a kk Hak) as (Hin0 & _ & Hk & _).
    pose proof (req_size_pos (kk + HEAD) ltac:(unfold HEAD; lia)) as (_ & RQ).
    destruct (wvc_fp_cases buf cap _ Hin) as [Hs | (Hc0 & H1 & H2)].
    + exact (blk_img tfibsegs B LAWS ly S W (unpoison U m) md _ _ (a - HEAD + i) HAR Hin0
        ltac:(unfold HEAD in *; lia) (wvc_pstat_img _ Hs)).
    + assert (Hne : (a - HEAD, kk + HEAD) <> (buf - HEAD, cap + HEAD)).
      { intros E. injection E as E1 _. apply (proj2 (HD a kk Hak)). lia. }
      pose proof (sep_blocks tfibsegs B LAWS ly S W (unpoison U m) md _ _ _ _ HAR Hin0 (HBIN Hc0) Hne) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd.
      pose proof (req_size_pos (cap + HEAD) ltac:(unfold HEAD; lia)) as (_ & RQ2).
      unfold HEAD in *. lia. }
split.
{ intros a k Hak. split; [exact (proj1 (HD a k Hak))|].
  destruct (Z.eq_dec cap' 0) as [E0|E0].
  - rewrite (Hb0' E0). destruct (HUL a k Hak) as (Hin0 & _).
    destruct (fsw_ablock_low B ly S W (unpoison U m) md _ _ HAR Hin0) as (A1 & _). unfold HEAD in *. lia.
  - exact (proj2 (HDL a k Hak) E0). }
split.
{ rewrite Ecp. fold cap'. intros Hz.
  pose proof HJc as (_ & Hly & _ & _ & _ & Hfrs & _).
  apply (wvc_root_fresh B ly S ly' S' W W' (unpoison U m) md (unpoison U' m') md' m (wf_v F) buf buf' cap cap'
    HAR HAR'); [| exact HBS' | exact Hnew | exact Hc' | exact HPO | exact HROOT | exact HB0 | exact Hc | exact Hz].
  intros cid pos Hin. split; [rewrite Hfrs; exact Hin|].
  unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
split; [rewrite Ecp; exact Hnew|].
split; [rewrite Ecp; exact Hb0'|].
split; [exact (arodata_kept B _ _ _ ly S U W m md ly' S' U' W' m' md' kc HJc HARU OK' PO' HCL HFRO HRO)|].
(* the words at o - 8 and o - 16: stack bytes in [sp, o), kept by the callee's wkeep *)
assert (AVS : forall a, wf_sp F <= a < wf_o F ->
  aview tfibsegs (w_H W') (unpoison U' m') a = aview tfibsegs (w_H W) (unpoison U m) a).
{ intros a Ha.
  assert (Ha64 : alloc_ceiling <= a < 2 ^ 64).
  { pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
    destruct Hstk as (_ & _ & _ & _ & _ & H47 & _ & _ & Htop2).
    pose proof HOUT as (_ & _ & Hotop & _). split; [lia|].
    pose proof HJc as (_ & Hly2 & _). destruct Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). lia. }
  rewrite (aview_unpoison_out tfibsegs _ U' m' a (zwk_p_stack_not_ush B ly' S' U' W' m' md' a HARU' Ha64)).
  rewrite (aview_unpoison_out tfibsegs _ U m a (zwk_p_stack_not_ush B ly S U W m md a HARU Ha64)).
  unfold aview. destruct (HWK' a ltac:(lia) ltac:(lia)) as (E1 & _). rewrite E1. reflexivity. }
split.
{ rewrite (rdword_ext (aview tfibsegs (w_H W) (unpoison U m)) _ (wf_o F - 8)); [exact H8|].
  intros k Hk. apply AVS. lia. }
split.
2: { (* the new buffer's head: uswap keeps U with the buffer, or appends the new head *)
  rewrite Ecp. fold cap'. intros Hz.
  destruct HUS' as [(EU & Eb) | [(U1 & U2 & EU0 & EU1) | (Ec0 & EU1)]].
  - rewrite EU, Eb. apply HU0. intros E0. pose proof (Hnew Hz) as Hb. rewrite Eb, (HB0 E0) in Hb.
    destruct (fsw_ablock_low B ly' S' W' _ md' _ _ HAR' Hb) as (A1 & _). unfold HEAD in *. lia.
  - rewrite EU1. apply in_or_app. right. apply in_or_app. right. left. reflexivity.
  - rewrite EU1. apply in_or_app. right. left. reflexivity. }
destruct HC as [HC1 | (H16 & nfp & Hnfp & Hend)]; [left; exact HC1 | right].
split; [exact H16|]. exists nfp. split; [|exact Hend].
rewrite (rdword_ext (aview tfibsegs (w_H W) (unpoison U m)) _ (wf_o F - 16)); [exact Hnfp|].
intros k Hk. apply AVS. lia.
Qed.

(* a word read through the byte view is a 64-bit number *)
Lemma wvc_rdword_range : forall H mem a v, rdword (aview tfibsegs H mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros H mem a v Hw. unfold rdword in Hw.
destruct (aview tfibsegs H mem a) as [b0|] eqn:E0; [|discriminate].
destruct (aview tfibsegs H mem (a + 1)) as [b1|] eqn:E1; [|discriminate].
destruct (aview tfibsegs H mem (a + 2)) as [b2|] eqn:E2; [|discriminate].
destruct (aview tfibsegs H mem (a + 3)) as [b3|] eqn:E3; [|discriminate].
destruct (aview tfibsegs H mem (a + 4)) as [b4|] eqn:E4; [|discriminate].
destruct (aview tfibsegs H mem (a + 5)) as [b5|] eqn:E5; [|discriminate].
destruct (aview tfibsegs H mem (a + 6)) as [b6|] eqn:E6; [|discriminate].
destruct (aview tfibsegs H mem (a + 7)) as [b7|] eqn:E7; [|discriminate].
injection Hw as <-.
apply aview_byte in E0 as (c0 & _ & -> & R0). apply aview_byte in E1 as (c1 & _ & -> & R1).
apply aview_byte in E2 as (c2 & _ & -> & R2). apply aview_byte in E3 as (c3 & _ & -> & R3).
apply aview_byte in E4 as (c4 & _ & -> & R4). apply aview_byte in E5 as (c5 & _ & -> & R5).
apply aview_byte in E6 as (c6 & _ & -> & R6). apply aview_byte in E7 as (c7 & _ & -> & R7).
lia.
Qed.

(* write_value's stack covers its frame plus any callee's, the recursive one at the level below included *)
Lemma wvc_stk : forall m, WVC_F <= STK_write_value m /\ STK_put + WVC_F <= STK_write_value m /\
  STK_indent + WVC_F <= STK_write_value m /\ STK_put_string + WVC_F <= STK_write_value m /\
  (forall m', m = S m' -> STK_write_value m' + WVC_F <= STK_write_value m).
Proof.
intros m. destruct m as [|m]; cbn [STK_write_value]; unfold zmaxl, FRAME_write_value, WVC_F; cbn [fold_right].
- repeat split; try lia; intros m' E; discriminate.
- repeat split; try lia; intros m' E; injection E as <-; lia.
Qed.

(* ---- the premises every writer callee of the arms shares, at a call from the loop: its fpreU (the journal from the
   arm's entry, the frame chain at s0 = o by the one-node clause), the chain clause at o, the window presence ----
   CASE 1 (o = sp + 8, the arm called from pj_write): the word at o - 16 is write_value's own saved-ra slot
   (frame offset 184, the entry ra, below alloc_ceiling), which the caller reads off the frame chunks. *)
Lemma wvc_callpre : forall F ly0 S0 U0 W0 mem0 md0 regs0 ly S U (W : world tfibsegs) memC mdC k buf st regsC STKc,
  ajournal tfibsegs B (wvc_STK F) (wf_ot F) (wvc_FP F) ly0 S0 W0 (unpoison U0 mem0) md0 []
    ly S W (unpoison U memC) mdC k ->
  ARU tfibsegs B ly S U W memC mdC ->
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly S U W memC buf st ->
  (wf_o F = wf_sp F + 8 -> rdword (aview tfibsegs (w_H W) (unpoison U memC)) (wf_sp F - 8) = Some (raZ regs0)) ->
  spZ regsC = wf_sp F - WVC_F -> wf_sp F mod 16 = 0 -> wf_ot F mod 16 = 0 -> wf_sp F <= wf_ot F ->
  0 <= STKc -> STKc + WVC_F <= STK_write_value (wf_m F) ->
  YK0s.ret_ok (getr regsC 1) -> 4096 <= raZ regsC ->
  getr regsC 3 = w64 (as_gp B) -> getr regsC 4 = w64 (as_tp B) ->
  s0Z regsC = wf_o F ->
  wf_o F + 32 <= wf_ot F -> wf_ot F <= ly_top ly -> wf_o F mod 8 = 0 -> alloc_ceiling <= wf_sp F - WVC_F ->
  exists ch, spine ch = (if 4096 <=? wf_ra8 F then [wf_ra8 F] else []) /\
    fpreU tfibsegs B STKc ly S U W regsC memC mdC ch /\
    (wf_o F = spZ regsC + 8 /\ raZ regsC < alloc_ceiling \/
     spZ regsC + 16 <= wf_o F /\ exists ra nfp, rdword (aview tfibsegs (w_H W) (unpoison U memC)) (wf_o F - 8) = Some ra /\
       rdword (aview tfibsegs (w_H W) (unpoison U memC)) (wf_o F - 16) = Some nfp /\
       (ra < 4096 \/ nfp < alloc_ceiling)) /\
    (forall a, spZ regsC <= a < wf_ot F -> apresent (w_H W) memC a).
Proof.
intros F ly0 S0 U0 W0 mem0 md0 regs0 ly S U W memC mdC k buf st regsC STKc HJ HARU HSEM HC1 Hsp Hsp16 Hot16 Hspot
  HSTK0 HSTK Hret Hra4 Hgp Htp Hs0 Hoot Hottop Ho8 Hlo.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HWF : WVC_F = 192) by reflexivity.
pose proof (wvc_sem_o_sp B F ly0 S0 U0 W0 mem0 regs0 ly S U W memC buf st HSEM) as Hosp.
destruct HSEM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & H8 & HC & _).
(* the two words of the one-node chain at o, at this memory *)
assert (HW2 : exists nfp, rdword (aview tfibsegs (w_H W) (unpoison U memC)) (wf_o F - 16) = Some nfp /\
  (wf_ra8 F < 4096 \/ nfp < alloc_ceiling)).
{ destruct HC as [(E & Hra) | (_ & HW)]; [|exact HW].
  exists (raZ regs0). split; [|right; exact Hra]. rewrite E. replace (wf_sp F + 8 - 16) with (wf_sp F - 8) by lia.
  exact (HC1 E). }
destruct HW2 as (nfp & Hnfp & Hend).
pose proof (wvc_rdword_range _ _ _ _ H8) as R8. pose proof (wvc_rdword_range _ _ _ _ Hnfp) as R16.
destruct (wvc_achain ly (aview tfibsegs (w_H W) (unpoison U memC)) (spZ regsC) (wf_o F) (wf_ra8 F) nfp H8 Hnfp Hend
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Ho8) as (ch & Hch & Hsp1).
exists ch. split; [exact Hsp1|].
split.
{ apply (fsw_fpreU_atFP B (wvc_STK F) (wf_ot F) (wvc_FP F) ly0 S0 U W0 (unpoison U0 mem0) md0 [] ly S W memC mdC k
    regsC STKc (wf_sp F - WVC_F - wf_ot F) ch HJ HARU HRO).
  - lia.
  - rewrite Zminus_mod, (Zminus_mod (wf_sp F) WVC_F 16), Hsp16, Hot16. reflexivity.
  - lia.
  - exact HSTK0.
  - unfold wvc_STK. lia.
  - exact Hret.
  - exact Hra4.
  - exact Hgp.
  - exact Htp.
  - rewrite Hs0. exact Hch. }
split.
{ right. split; [lia|]. exists (wf_ra8 F), nfp. split; [exact H8|]. split; [exact Hnfp | exact Hend]. }
intros a Ha. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
destruct Hstk as (_ & _ & _ & _ & _ & H47 & _ & Htop1 & Htop2).
apply (fsw_apresent_unpoison B ly S U W memC mdC a HARU); [unfold kHighMemBeg in *; lia|].
apply Hpres. unfold wvc_STK. pose proof (wvc_stk (wf_m F)) as (HF & _). lia.
Qed.

End C.
