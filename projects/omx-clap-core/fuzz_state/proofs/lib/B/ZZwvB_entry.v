(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v; 1536 of its 1692 lines of code are new or changed and 1217 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_write_value.v, with its module paths and module names changed; 518 of its 589 lines of code are new or changed and 1621 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/ZZwv_cent.v, with its module paths, module names and numbers changed; 320 of its 394 lines of code are new or changed and 515 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the ENTRY STEP of the lib/B (fs.asan-ubsan) container arms of write_value:
   write_value's entry state (FSW_write_value_entry.wv_start / wv_ss0), the engine run to the put of the opening
   bracket (ZZwvB_runs1.wvc_seg_entry, through the two UBSan guards 0x8404c / 0x84060 on the root node and the inline
   ASan check of v->type at 0x84084), that put, and the resume at WVC_R_OPEN = 0x840dc as ZZwvB_inv.wvc_invO.
   Image A has no twin of this file: its container arms are unproved (wv_arr / wv_obj are hypotheses of
   lib/A/FSW_write_value.v).
   rule 24: proves no function (kind: segment lemma) - the entry step of the container arms of write_value B.
   Rule 24 (proof-index, a Theorem Labs lane, unpiped): write_value has RELEASED proofs for fs's PLAIN and UBSAN
   builds only (lib/Prog, lib/U/Prog), none for an ASan image; 0x84010 is not in the released set. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_rres FSW_ret FSW_rd FSW_pj FSH_Fn_writer
FSW_write_value_entry ZZwvB_defs ZZwvB_comp ZZwvB_kit ZZwvB_tree ZZwvB_inv ZZwvB_call ZZwvB_call2 ZZwvB_call3
ZZwvB_ret ZZwvB_res ZZwvB_runs1 ZZwvB_runs2 ZZwvB_step ZZwvB_arm.
(* YF0x.val_mem_rdword: a word read back through the byte view (the entry ra at the frame slot 184) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSH_Fn_reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterValue PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section A. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HSS : FsShadowSyms B.
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis HPUT : put_spec B tfibsegs.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Section St.
(* the arm instance: its fixed data and the ENTRY state, which is the Section's (ly0, S0, U0, W0, mem0, md0, regs0) *)
Variable F : wvc_fix.
Variables (ly0 : alayout) (S0 : astate) (U0 : list (Z * Z)) (W0 : world tfibsegs) (mem0 : word -> option byte)
  (md0 : Model) (regs0 : bvmap 5 word).
Hypothesis HE_sp16 : wf_sp F mod 16 = 0.
Hypothesis HE_ot16 : wf_ot F mod 16 = 0.
Hypothesis HE_oot : wf_o F + 32 <= wf_ot F.
Hypothesis HE_o8 : wf_o F mod 8 = 0.
Hypothesis HE_top : wf_ot F <= ly_top ly0.
Hypothesis HE_top47 : ly_top ly0 <= 2 ^ 47.
Hypothesis HE_lo : alloc_ceiling + STK_write_value (wf_m F) <= wf_sp F.
Hypothesis HE_gp : YK11.getr regs0 3%bv = w64 (as_gp B).
Hypothesis HE_tp : YK11.getr regs0 4%bv = w64 (as_tp B).
Hypothesis HE_cap0 : 0 <= wf_cap0 F.
Hypothesis HE_capl : wf_cap0 F <= wf_live F.
Hypothesis HE_cnt0 : 0 <= wf_cnt0 F.
Hypothesis HE_p : 0 <= wf_p F < alloc_ceiling.
Hypothesis HE_d : 0 <= wf_d F.
Hypothesis HE_dd : wf_d F + Z.of_nat (PjTree.depth (wf_t F)) <= 2 ^ 31 - 1.
Hypothesis HE_room : Z.of_nat (length (wf_text0 F)) + Z.of_nat (length (concat (wvc_WP F))) + 1 <= WMAX.
Hypothesis HE_bud : wbudget_pre S0 (wf_cap0 F) (wf_cnt0 F) (wf_live F) (WriterApp.putN (wvc_st0 F) (wvc_WP F)).
Hypothesis HE_frl : Z.of_nat (length (frames S0)) <= FRL_CRT_CALLEE.
Hypothesis HE_foot : forall x, wf_o F <= x < wf_ot F -> ~ PjStruct.pj_foot (wf_v F) (wf_D F) x.
Hypothesis HE_plain : jv_plain (wf_t F).
Hypothesis HE_ty :
  (wf_ty F = 5 /\ exists items, wf_t F = PjTree.JArr items /\ wf_n F = Z.of_nat (length items) /\ wf_keys F = 0) \/
  (wf_ty F = 6 /\ exists members, wf_t F = PjTree.JObj members /\ wf_n F = Z.of_nat (length members)).
Hypothesis HE_hdr : exists num capn,
  PjStruct.pj_hdr tfibsegs (rdW W0 mem0) (wf_v F) (wf_ty F) num (wf_str F) (wf_kids F) (wf_keys F) (wf_n F) capn.
Hypothesis HE_n : 0 <= wf_n F < 2 ^ 54.
Hypothesis HE_kk : 0 < wf_n F -> 4096 <= wf_kids F /\ wf_kids F + 56 * wf_n F <= alloc_ceiling /\
                   (wf_ty F = 6 -> 4096 <= wf_keys F /\ wf_keys F + 8 * wf_n F <= alloc_ceiling).

(* ---- the entry state's writer facts: wvc_sem at the model state with no piece written ---- *)
Lemma wvc_sem_init : forall ch,
  fpreU tfibsegs B (STK_write_value (wf_m F)) ly0 S0 U0 W0 regs0 mem0 md0 ch ->
  wout_ok B tfibsegs ly0 S0 W0 mem0 (wf_o F) (wf_buf0 F) (wf_cap0 F) (wf_failed0 F) (wf_text0 F) ->
  fs_glob tfibsegs W0 mem0 (wf_live F) (wf_peak0 F) (wf_cnt0 F) (wf_fail0 F) ->
  fs_heads B ly0 S0 U0 ->
  (wf_cap0 F <> 0 -> In (wf_buf0 F - HEAD, HEAD) U0) ->
  PjStruct.pj_node tfibsegs (rdW W0 mem0) (fun a k => In (a, k) (wf_UL F)) (wf_v F) (wf_t F) (wf_D F) ->
  FSH_Fn_reader.pobj tfibsegs B ly0 S0 W0 mem0 (wf_v F) ->
  ublocks_ok B tfibsegs ly0 S0 W0 mem0 (wf_D F) ->
  (forall a k, In (a, k) (wf_D F) -> In (a, k) (wf_UL F) /\ a <> wf_buf0 F) ->
  (wf_cap0 F <> 0 -> wf_v F + 56 <= wf_buf0 F - HEAD \/ wf_buf0 F + wf_cap0 F <= wf_v F) ->
  wf_cap0 F <= WMAX ->
  rdword (aview tfibsegs (w_H W0) (unpoison U0 mem0)) (wf_o F - 8) = Some (wf_ra8 F) ->
  ((wf_o F = wf_sp F + 8 /\ raZ regs0 < alloc_ceiling) \/
   (wf_sp F + 16 <= wf_o F /\
    exists nfp, rdword (aview tfibsegs (w_H W0) (unpoison U0 mem0)) (wf_o F - 16) = Some nfp /\
      (wf_ra8 F < 4096 \/ nfp < alloc_ceiling))) ->
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly0 S0 U0 W0 mem0 (wf_buf0 F) (wvc_st0 F).
Proof.
intros ch HPRE HOUT HGLOB HHD HUH HN HPO HUL HD Hroot HCAP H8 HC.
pose proof HPRE as (_ & HRO).
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcase).
unfold wvc_sem, wvc_st0.
cbn [WriterApp.w_cap WriterApp.w_failed WriterApp.w_text WriterApp.w_cnt WriterApp.w_fail].
split; [exact HOUT|].
split.
{ exists (wf_peak0 F). split; [lia|].
  replace (wf_live F + wf_cap0 F - wf_cap0 F) with (wf_live F) by lia. exact HGLOB. }
split; [exact HHD|].
(* uswap / bswap: the reflexive arms (the buffer has not moved) *)
split; [left; split; reflexivity|].
split; [left; split; [reflexivity | split; reflexivity]|].
split; [split; [exact HCAP | split; lia]|].
(* no allocator request recorded yet *)
split; [unfold wcalls; cbn [WriterApp.w_calls length Z.of_nat]; lia|].
split; [intros a _ _; split; [reflexivity | split; intros Hw; exact Hw]|].
split; [exact HN|]. split; [exact HPO|]. split; [intros x _; reflexivity|].
split; [exact HUL|]. split; [exact HD|]. split; [exact Hroot|].
(* the live buffer's block, and the NULL buffer, from wout_ok's two cases *)
split.
{ intros Hz. destruct Hcase as [(E & _) | (_ & (Hin & _) & _)]; [exfalso; exact (Hz E) | exact Hin]. }
split.
{ intros Hz. destruct Hcase as [(_ & E & _) | ((j & Hj & Ej) & _)]; [exact E|].
  exfalso. rewrite Ej in Hz. pose proof (Z.pow_pos_nonneg 2 j ltac:(lia) ltac:(lia)). lia. }
split; [exact HRO|]. split; [exact H8|]. split; [exact HC | exact HUH].
Qed.

(* ---- the resume at WVC_R_OPEN after the put of the opening bracket: the open invariant ---- *)
Lemma wvc_ret_invO : forall Pc Rest ly S U (W : world tfibsegs) memC mdC buf regsC R0 ke key
    STKc peak ly' S' U' (W' : world tfibsegs) regs' mem' md' buf',
  wvc_WP F = Pc ++ Rest -> Pc = wvc_POPEN F ->
  ajournal tfibsegs B (wvc_STK F) (wf_ot F) (wvc_FP F) ly0 S0 W0 (unpoison U0 mem0) md0 []
    ly S W (unpoison U memC) mdC 0 ->
  ARU tfibsegs B ly S U W memC mdC ->
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly S U W memC buf (wvc_st0 F) ->
  wf_peak0 F <= peak <= wf_peak0 F ->
  Forall (YP09.chunk_ok tfibsegs
     (Ereg R0 (fs_extraT ++ wvc_xs regs0 (wf_str F) (wf_kids F) (wf_keys F) (wf_n F) (wf_d F) ke key))
     (rdW W memC) (wf_sp F - WVC_F)) wvc_cs0 ->
  YK11.getr R0 9%bv = w64 (wf_v F) ->
  spZ regsC = wf_sp F - WVC_F ->
  YK11.getr regsC 8%bv = w64 (wf_o F) -> YK11.getr regsC 9%bv = w64 (wf_v F) ->
  YK11.getr regsC 19%bv = w64 (wf_p F) ->
  YK11.getr regsC 3%bv = YK11.getr regs0 3%bv -> YK11.getr regsC 4%bv = YK11.getr regs0 4%bv ->
  ajournal tfibsegs B (STKc + (wf_ot F - spZ regsC)) (wf_ot F)
    (FS_PSTAT_FP ++ wbuf_fp buf (wf_cap0 F)) ly S W (unpoison U memC) mdC []
    ly' S' W' (unpoison U' mem') md' (wevk (wf_cap0 F) (WriterApp.putN (wv_rst (wvc_st0 F)) Pc)) ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' -> aregs_preserved regsC regs' ->
  0 <= STKc -> STKc + WVC_F <= STK_write_value (wf_m F) ->
  uswap U U' buf buf' (wf_cap0 F) ->
  wout_ok B tfibsegs ly' S' W' mem' (wf_o F) buf'
    (WriterApp.w_cap (WriterApp.putN (wv_rst (wvc_st0 F)) Pc))
    (WriterApp.w_failed (WriterApp.putN (wv_rst (wvc_st0 F)) Pc))
    (WriterApp.w_text (WriterApp.putN (wv_rst (wvc_st0 F)) Pc)) ->
  wbudget_kept S S' (wf_failed0 F) (wf_cap0 F) (wf_cnt0 F)
    (WriterApp.w_failed (WriterApp.putN (wv_rst (wvc_st0 F)) Pc))
    (WriterApp.w_cap (WriterApp.putN (wv_rst (wvc_st0 F)) Pc))
    (WriterApp.w_cnt (WriterApp.putN (wv_rst (wvc_st0 F)) Pc)) ->
  bswap (ablocks B ly S) (ablocks B ly' S') buf buf' (wf_cap0 F)
    (WriterApp.w_cap (WriterApp.putN (wv_rst (wvc_st0 F)) Pc)) ->
  wkeep tfibsegs W W' memC mem' (spZ regsC) (wf_ot F) (wf_o F) 32 ->
  (exists peak', peak <= peak' <= Z.max peak (wf_live F - wf_cap0 F +
       WriterApp.w_cap (WriterApp.putN (wv_rst (wvc_st0 F)) Pc)) /\
     fs_glob tfibsegs W' mem' (wf_live F + WriterApp.w_cap (WriterApp.putN (wv_rst (wvc_st0 F)) Pc) - wf_cap0 F)
       peak' (WriterApp.w_cnt (WriterApp.putN (wv_rst (wvc_st0 F)) Pc))
       (WriterApp.w_fail (WriterApp.putN (wv_rst (wvc_st0 F)) Pc))) ->
  wvc_invO B F ly0 S0 U0 W0 mem0 md0 regs0
    W' (mkst regs' (Z_to_bv 64 WVC_R_OPEN) mem' (seg_rom tfibsegs)) md' ly' S' U' buf'.
Proof.
intros Pc Rest ly S U W memC mdC buf regsC R0 ke key STKc peak ly' S' U' W' regs' mem' md' buf'
  HWP HPc HJ HARU HSEM Hpk HCH HR09 Hsp R8 R9 R19 R3 R4 HJc OK' PO' HP HSTK0 HSTKc HUS' HOUT' HBK' HBS' HWK'
  HGL'.
subst Pc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HWF : WVC_F = 192) by reflexivity.
pose proof (wvc_stk (wf_m F)) as (HSTKF & _).
pose proof (wvc_sem_o_sp B F ly0 S0 U0 W0 mem0 regs0 ly S U W memC buf _ HSEM) as Hosp.
pose proof (proj1 HARU) as HAR.
assert (Hlo' : alloc_ceiling <= wf_sp F - WVC_F) by lia.
(* the count stays below 2^64 *)
assert (Hcnt : wf_cnt0 F + wcalls (WriterApp.putN (wvc_st0 F) (wvc_POPEN F)) < 2 ^ 64).
{ pose proof HE_bud as (_ & _ & _ & HB4). rewrite HWP, WriterApp.putN_app in HB4.
  pose proof (zzwv_calls_mono Rest (WriterApp.putN (wvc_st0 F) (wvc_POPEN F))) as M. lia. }
(* the callee's glob clause in wvc_sem_call's form (the model state at the call is the entry's, cap = cap0) *)
set (cP := WriterApp.w_cap (WriterApp.putN (wv_rst (wvc_st0 F)) (wvc_POPEN F))) in *.
assert (HGL2 : exists peak', peak <= peak' <= Z.max peak ((wf_live F + WriterApp.w_cap (wvc_st0 F) - wf_cap0 F) -
    WriterApp.w_cap (wvc_st0 F) + cP) /\
  fs_glob tfibsegs W' mem' ((wf_live F + WriterApp.w_cap (wvc_st0 F) - wf_cap0 F) + cP - WriterApp.w_cap (wvc_st0 F))
    peak' (WriterApp.w_cnt (WriterApp.putN (wv_rst (wvc_st0 F)) (wvc_POPEN F)))
    (WriterApp.w_fail (WriterApp.putN (wv_rst (wvc_st0 F)) (wvc_POPEN F)))).
{ change (WriterApp.w_cap (wvc_st0 F)) with (wf_cap0 F).
  destruct HGL' as (pk' & Hpk' & HG'). exists pk'. split; [lia|].
  replace (wf_live F + wf_cap0 F - wf_cap0 F + cP - wf_cap0 F) with (wf_live F + cP - wf_cap0 F) by lia.
  exact HG'. }
(* the writer facts at the return *)
destruct (wvc_sem_call B F ly0 S0 U0 W0 mem0 regs0 ly S U W memC mdC buf (wvc_st0 F) (wvc_POPEN F) ly' S' U' W' mem'
  md' buf' (STKc + (wf_ot F - spZ regsC)) _ (spZ regsC) peak HSEM HARU HE_cap0 (Z.le_refl _) HE_cnt0 Hcnt Hlo'
  HE_oot ltac:(change (WriterApp.w_cap (wvc_st0 F)) with (wf_cap0 F); lia) HJc OK' PO' HUS' HOUT' HBK' HBS' HWK'
  ltac:(lia) HGL2) as (HARU' & HSEM').
pose proof HSEM as (HOUT & _ & _ & _ & HBS & _ & _ & _ & _ & _ & _ & _ & _ & _ & HBIN & _).
pose proof HSEM' as (_ & _ & HHD' & _ & _ & _ & _ & _ & HN' & HPO' & HNB' & _).
(* the node's header at the return memory: its bytes are the entry's *)
assert (HHDR' : exists num capn,
  PjStruct.pj_hdr tfibsegs (rdW W' mem') (wf_v F) (wf_ty F) num (wf_str F) (wf_kids F) (wf_keys F) (wf_n F) capn).
{ destruct HE_hdr as (num & capn & H). exists num, capn.
  apply (PjStruct.pj_hdr_eq tfibsegs (rdW W0 mem0)); [exact H | exact HNB']. }
destruct HHDR' as (num & capn & HHDR').
(* the journal's footprint at the call *)
pose proof (wv_fp_sub_swap B ly0 S0 ly S W (unpoison U memC) mdC (wf_buf0 F) (wf_cap0 F) buf (wf_cap0 F)
  HAR HBS HBIN HE_cap0 wvc_pstat_img) as HFPSUB.
assert (Hrs : forall q : bv 5, acallee_saved (bv_unsigned q) -> getr regs' q = getr regsC q)
  by (intros q Hq; exact (fsw_pres regsC regs' q HP Hq)).
(* the env at the open point: the callee's registers, the arm's extras with ke = keys, key = 0 *)
set (xs := wvc_xs regs0 (wf_str F) (wf_kids F) (wf_keys F) (wf_n F) (wf_d F) (wf_keys F) 0).
set (E' := Ereg regs' (fs_extraT ++ xs)).
assert (E2' : bv_unsigned (ew E' 2) = wf_sp F - WVC_F).
{ unfold E'. rewrite (ew_Ereg_nat regs' _ 2 2%bv eq_refl), (Hrs 2%bv ltac:(apply (wvc_cs_z _ 2); [reflexivity | lia])).
  exact Hsp. }
assert (E9' : ew E' 9 = Z_to_bv 64 (wf_v F)).
{ unfold E'. rewrite (ew_Ereg_nat regs' _ 9 9%bv eq_refl), (Hrs 9%bv ltac:(apply (wvc_cs_z _ 9); [reflexivity | lia])).
  exact R9. }
assert (E32' : ew E' 32 = Z_to_bv 64 SHADOW_OFF) by (unfold E'; apply wvr1_e32).
assert (EX : forall j, ew E' (xatom j) = nth j xs (Z_to_bv 64 0)) by (intros j; unfold E'; apply fsw_ew_xatom).
(* the frame chunks at the return, in the return env *)
assert (HCH' : Forall (YP09.chunk_ok tfibsegs E' (rdW W' mem') (wf_sp F - WVC_F)) wvc_cs0).
{ apply (wvc_cs0_after _ E' W W' memC mem' (wf_sp F) (spZ regsC) (wf_ot F) (wf_o F) HCH HWK'); [lia | lia | lia | | |].
  - rewrite E9', (ew_Ereg_nat R0 _ 9 9%bv eq_refl). symmetry. exact HR09.
  - rewrite E32', wvr1_e32. reflexivity.
  - intros j Hj. rewrite EX, fsw_ew_xatom. unfold xs.
    do 18 (destruct j as [|j]; [cbn [nth wvc_xs app map]; reflexivity|]). exfalso. lia. }
(* the node's region, the regions apart, atom 9's fact, the node's shadow entry *)
destruct (wvc_resume_rs0 B ly' S' U' W' mem' md' E' (wf_ty F) wvc_cs0 (wf_v F) num (wf_str F) (wf_kids F)
  (wf_keys F) (wf_n F) capn (wf_sp F) HARU' HPO' HHDR' E2' Hlo' ltac:(lia) E9' E32'
  ltac:(rewrite EX; reflexivity) ltac:(rewrite EX; reflexivity)
  ltac:(rewrite EX; reflexivity) ltac:(rewrite EX; reflexivity)) as (HRS & HPD & HGF & HSH).
(* the after-call step *)
destruct (wvc_after_call2 B (wvc_STK F) (wf_ot F) (wvc_FP F) [] ly0 S0 U0 W0 W mem0 md0 ly S U memC mdC
  0 STKc (FS_PSTAT_FP ++ wbuf_fp buf (wf_cap0 F)) (wf_ot F) WVC_F regsC ly' S' U' W'
  regs' mem' md' (wevk (wf_cap0 F) (WriterApp.putN (wv_rst (wvc_st0 F)) (wvc_POPEN F)))
  xs wvc_cs0 [wvc_node (wf_ty F)] wvc_gf0 WVC_R_OPEN (wf_sp F) HSS HJ HARU HJc HFPSUB OK' PO' HP Hsp
  ltac:(unfold WVC_F; lia) HSTK0 ltac:(unfold wvc_STK; lia) ltac:(reflexivity) HE_sp16
  ltac:(lia) ltac:(lia) ltac:(lia) (wvc_rs0_wf (wf_ty F)) HCH' HRS HPD HGF) as (HJ' & HARU'' & HST).
rewrite Z.add_0_l in HJ'.
assert (Hval : forall (q : bv 5) z, acallee_saved (bv_unsigned q) -> getr regsC q = w64 z ->
  YK11.getr (ms_regs (mkst regs' (Z_to_bv 64 WVC_R_OPEN) mem' (seg_rom tfibsegs))) q = w64 z).
{ intros q z Hq E. cbn [ms_regs mkst]. rewrite (Hrs q Hq). exact E. }
unfold wvc_invO. cbv zeta.
split.
{ split; [exact (wvc_ssO_ret _ (wf_ty F) _ HST)|]. split; [exact HSH|]. split; [exact HJ' | exact HARU'']. }
split; [cbn [ms_mem mkst]; exact HSEM'|].
split; [exact (Hval 8%bv _ ltac:(apply (wvc_cs_z _ 8); [reflexivity | lia]) R8)|].
split; [exact (Hval 9%bv _ ltac:(apply (wvc_cs_z _ 9); [reflexivity | lia]) R9)|].
split; [exact (Hval 19%bv _ ltac:(apply (wvc_cs_z _ 19); [reflexivity | lia]) R19)|].
split; [cbn [ms_regs mkst]; rewrite (Hrs 3%bv ltac:(apply (wvc_cs_z _ 3); [reflexivity | lia])); exact R3|].
split; [cbn [ms_regs mkst]; rewrite (Hrs 4%bv ltac:(apply (wvc_cs_z _ 4); [reflexivity | lia])); exact R4|].
cbn [ms_regs mkst]. unfold spZ. rewrite (Hrs 2%bv ltac:(apply (wvc_cs_z _ 2); [reflexivity | lia])). exact Hsp.
Qed.

(* ---- the entry step: from write_value's entry configuration to the open invariant ---- *)
Lemma wvc_step_entry : forall ch (Q : world tfibsegs -> config -> Prop),
  fpreU tfibsegs B (STK_write_value (wf_m F)) ly0 S0 U0 W0 regs0 mem0 md0 ch ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W0) mem0) ->
  YK11.getr regs0 10%bv = w64 (wf_o F) -> YK11.getr regs0 11%bv = w64 (wf_v F) ->
  YK11.getr regs0 12%bv = w64 (wf_p F) -> YK11.getr regs0 13%bv = w64 (wf_d F) ->
  spZ regs0 = wf_sp F ->
  wout_ok B tfibsegs ly0 S0 W0 mem0 (wf_o F) (wf_buf0 F) (wf_cap0 F) (wf_failed0 F) (wf_text0 F) ->
  fs_glob tfibsegs W0 mem0 (wf_live F) (wf_peak0 F) (wf_cnt0 F) (wf_fail0 F) ->
  fs_heads B ly0 S0 U0 ->
  (wf_cap0 F <> 0 -> In (wf_buf0 F - HEAD, HEAD) U0) ->
  PjStruct.pj_node tfibsegs (rdW W0 mem0) (fun a k => In (a, k) (wf_UL F)) (wf_v F) (wf_t F) (wf_D F) ->
  FSH_Fn_reader.pobj tfibsegs B ly0 S0 W0 mem0 (wf_v F) ->
  ublocks_ok B tfibsegs ly0 S0 W0 mem0 (wf_D F) ->
  (forall a k, In (a, k) (wf_D F) -> In (a, k) (wf_UL F) /\ a <> wf_buf0 F) ->
  (wf_cap0 F <> 0 -> wf_v F + 56 <= wf_buf0 F - HEAD \/ wf_buf0 F + wf_cap0 F <= wf_v F) ->
  wf_cap0 F <= WMAX ->
  (forall a, spZ regs0 <= a < wf_ot F -> apresent (w_H W0) mem0 a) ->
  rdword (aview tfibsegs (w_H W0) (unpoison U0 mem0)) (wf_o F - 8) = Some (wf_ra8 F) ->
  ((wf_o F = wf_sp F + 8 /\ raZ regs0 < alloc_ceiling) \/
   (wf_sp F + 16 <= wf_o F /\
    exists nfp, rdword (aview tfibsegs (w_H W0) (unpoison U0 mem0)) (wf_o F - 16) = Some nfp /\
      (wf_ra8 F < 4096 \/ nfp < alloc_ceiling))) ->
  (forall W' ms' mdc' ly' S' U' buf',
     wle W0 W' ->
     wvc_invO B F ly0 S0 U0 W0 mem0 md0 regs0 W' ms' mdc' ly' S' U' buf' ->
     SRr tfibsegs W' (mkCfg ms' mdc') Q) ->
  SRr tfibsegs W0 (cfg_at tfibsegs A_write_value regs0 mem0 md0) Q.
Proof.
intros ch Q HPRE HRO0 G10 G11 G12 G13 Hsp0 HOUT HGLOB HHD HUH HN HPO HUL HD Hroot HCAP HPRES H8 HC HK.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HWF : WVC_F = 192) by reflexivity.
pose proof (wvc_stk (wf_m F)) as (HSTKF & HSTKP & _).
pose proof (wv_stk_frame (wf_m F)) as HSTKw.
assert (HSTKp0 : 0 <= STK_put) by (vm_compute; intro Hc; discriminate Hc).
assert (Hosp : wf_sp F + 8 <= wf_o F) by (destruct HC as [(E & _) | (L & _)]; lia).
assert (Hlo : alloc_ceiling <= wf_sp F - WVC_F) by lia.
assert (Htyc : wf_ty F = 5 \/ wf_ty F = 6)
  by (destruct HE_ty as [(Hty & _) | (Hty & _)]; [left | right]; exact Hty).
pose proof HE_hdr as (num & capn & HH).
pose proof HH as (_ & _ & _ & (Hstr0 & _) & _).
pose proof HPRE as (HPREU & HRO).
(* the writer facts at the entry *)
pose proof (wvc_sem_init ch HPRE HOUT HGLOB HHD HUH HN HPO HUL HD Hroot HCAP H8 HC) as HSEM0.
(* the arm's pieces start with the opening bracket (ZZwvB_tree.wv_pieces_arr / wv_pieces_obj) *)
assert (HWPe : exists Rest, wvc_WP F = wvc_POPEN F ++ Rest).
{ unfold wvc_WP, wvc_POPEN.
  destruct HE_ty as [(Hty & items & Ht & _) | (Hty & members & Ht & _)]; rewrite Ht, Hty.
  - rewrite wv_pieces_arr. eexists. reflexivity.
  - rewrite wv_pieces_obj. eexists. reflexivity. }
destruct HWPe as (Rest & HWPe).
(* put's room and budget for the bracket, from the arm's (ZZwvB_comp.wv_budget_pre_prefix) *)
assert (Hroom1 : Z.of_nat (length (wf_text0 F)) + 1 + 1 <= WMAX).
{ pose proof HE_room as HR. rewrite HWPe, concat_app, length_app in HR.
  assert (Hl : length (concat (wvc_POPEN F)) = 1%nat) by (unfold wvc_POPEN; destruct (wf_ty F =? 6); reflexivity).
  rewrite Hl in HR. lia. }
assert (HBUD1 : wbudget_pre S0 (wf_cap0 F) (wf_cnt0 F) (wf_live F)
  (WriterApp.putN (WriterApp.mkW (wf_failed0 F) (wf_text0 F) (wf_cap0 F) (wf_cnt0 F) (wf_fail0 F) [])
     (wvc_POPEN F))).
{ apply (wv_budget_pre_prefix S0 _ _ _ _ _ _ (wvc_POPEN F) Rest HE_cap0). rewrite <- HWPe. exact HE_bud. }
(* the entry state (FSW_write_value_entry.wv_start at the stack STK_write_value (wf_m F)): the symbolic state and the
   shadow entry (wv_entry: it rules out the two UBSan guards on the root node, 0x8404c by 4096 <= v and 0x84060 by
   v mod 8 = 0, from the node's atom fact), the journal at the raised top ot, ARU *)
destruct (wv_entry B HSS IMG (STK_write_value (wf_m F)) ly0 S0 U0 W0 regs0 mem0 md0 ch (wf_v F) (wf_ty F) num
  (wf_str F) (wf_kids F) (wf_keys F) (wf_n F) capn 0 (2 ^ 64 - 1) HPREU HRO HSTKw G11 HPO HH ltac:(lia))
  as [HS SHOK].
assert (HJ0 : ajournal tfibsegs B (STK_write_value (wf_m F) + (wf_ot F - spZ regs0)) (wf_ot F) (wvc_FP F)
  ly0 S0 W0 (unpoison U0 mem0) md0 [] ly0 S0 W0 (unpoison U0 mem0) md0 0)
  by exact (fsw_ajournal_init_ot B _ _ ly0 S0 U0 W0 regs0 mem0 md0 ch (wf_ot F) HPREU ltac:(lia) HE_ot16 HE_top
    HPRES).
pose proof (fsw_ARU B _ ly0 S0 U0 W0 regs0 mem0 md0 ch HPREU) as HARU0.
unfold cfg_at. change (w64 A_write_value) with (Z_to_bv 64 A_write_value).
(* the entry run to the put of the opening bracket *)
apply (wvc_seg_entry B W0 (mkst regs0 (Z_to_bv 64 A_write_value) mem0 (seg_rom tfibsegs)) md0 regs0 (wf_ty F)
  0 (2 ^ 64 - 1) (wf_str F) (wf_kids F) (wf_keys F) (wf_n F) (wf_d F) (STK_write_value (wf_m F)) (wf_ot F)
  (wvc_FP F) ly0 S0 W0 (unpoison U0 mem0) md0 [] ly0 S0 U0 0 Q).
- exact (conj HS (conj SHOK (conj HJ0 HARU0))).
- exact Htyc.
- lia.
- exact HSTKF.
- exact G13.
- lia.
- intros ms' mdc' HJ1 HARU1 HFR1 HCH1 R1 R10 R11 R12 R2 R8 R9 R19 Rcs Ems'.
  rewrite Ems'.
  change (SRr tfibsegs W0 (cfg_at tfibsegs A_put (ms_regs ms') (ms_mem ms') mdc') Q).
  rewrite Hsp0 in HJ1, HFR1, HCH1, R2.
  set (regsC := ms_regs ms') in *. set (memC := ms_mem ms') in *.
  assert (Hsp : spZ regsC = wf_sp F - WVC_F) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
  assert (Hra : raZ regsC = WVC_R_OPEN)
    by (unfold raZ; rewrite R1; apply unsigned_lit_small; unfold WVC_R_OPEN; lia).
  assert (Hs0 : s0Z regsC = wf_o F) by (unfold s0Z; rewrite R8, G10; apply unsigned_lit_small; lia).
  (* the writer facts at the call: the run wrote write_value's own frame only *)
  assert (HFR : forall x : word, ~ (wf_sp F - WVC_F <= bv_unsigned x < wf_sp F) -> rdW W0 memC x = rdW W0 mem0 x)
    by exact HFR1.
  pose proof (wvc_sem_run B F ly0 S0 U0 W0 mem0 regs0 ly0 S0 U0 W0 mem0 memC mdc' (wf_buf0 F) (wvc_st0 F)
    HSEM0 HARU1 HFR Hlo ltac:(lia) ltac:(lia)) as HSEMC.
  pose proof HSEMC as (HOUTC & _).
  assert (AVB : zwk_avb W0 mem0 memC).
  { intros a Ha. apply aview_eq_of. apply HFR. rewrite unsigned_lit_small by lia. lia. }
  pose proof (zwk_fs_glob_avb W0 mem0 memC _ _ _ _ AVB HGLOB) as HGLOBC.
  (* the frame chunks at the call, in the env of the open point *)
  pose proof (HCH1 regsC (wf_keys F) 0 R9) as HCHC.
  (* the entry ra, at the frame slot 184 (= o - 16 when o = sp + 8): wvc_callpre's side condition *)
  assert (HRA8 : rdword (aview tfibsegs (w_H W0) (unpoison U0 memC)) (wf_sp F - 8) = Some (raZ regs0)).
  { assert (Hin : In (YP09.mkChunk 184 (CVal 8 (SOff (xatom 17) 0))) wvc_cs0).
    { unfold wvc_cs0. apply in_or_app. right. apply in_map_iff. exists 12%nat.
      split; [reflexivity | apply in_seq; lia]. }
    pose proof (proj1 (Forall_forall _ _) HCHC _ Hin) as Hck.
    assert (Hv : val_mem tfibsegs (rdW W0 memC) (wf_sp F - WVC_F + 184) (N.to_nat 8) (raZ regs0)).
    { apply (val_of_chunk_ok tfibsegs _ _ _ 184 8%N (SOff (xatom 17) 0) (raZ regs0) Hck).
      - rewrite fsw_SOff0, fsw_ew_xatom. cbn [nth wvc_xs app map wvc_saved].
        unfold raZ. symmetry. apply Z_to_bv_bv_unsigned.
      - cbn [Z.of_N]. unfold raZ. apply u64_range.
      - cbn [Z.of_N]. lia. }
    replace (wf_sp F - WVC_F + 184) with (wf_sp F - 8) in Hv by lia.
    rewrite (rdword_ext (aview tfibsegs (w_H W0) memC) _ (wf_sp F - 8)).
    - exact (YF0x.val_mem_rdword (w_H W0) memC _ _ ltac:(unfold raZ; apply u64_range) Hv).
    - intros k Hk.
      exact (aview_unpoison_out tfibsegs _ U0 _ (wf_sp F - 8 + k)
        (zwk_p_stack_not_ush B ly0 S0 U0 W0 memC mdc' (wf_sp F - 8 + k) HARU1 ltac:(lia))). }
  (* put's fpreU at the call, the one-node chain clause at o, the window presence (ZZwvB_call3.wvc_callpre) *)
  assert (Hret : YK0s.ret_ok (getr regsC 1)).
  { apply YK0s.ret_ok_even. change (raZ regsC mod 2 = 0). rewrite Hra. reflexivity. }
  assert (Hra4 : 4096 <= raZ regsC) by (rewrite Hra; unfold WVC_R_OPEN; lia).
  assert (Hgp : getr regsC 3 = w64 (as_gp B)) by (rewrite (Rcs 3%bv ltac:(left; reflexivity)); exact HE_gp).
  assert (Htp : getr regsC 4 = w64 (as_tp B)) by (rewrite (Rcs 4%bv ltac:(right; left; reflexivity)); exact HE_tp).
  destruct (wvc_callpre B F ly0 S0 U0 W0 mem0 md0 regs0 ly0 S0 U0 W0 memC mdc' 0 (wf_buf0 F) (wvc_st0 F) regsC
    STK_put HJ1 HARU1 HSEMC (fun _ => HRA8) Hsp HE_sp16 HE_ot16 ltac:(lia) HSTKp0 HSTKP Hret Hra4 Hgp Htp Hs0
    HE_oot HE_top HE_o8 Hlo) as (chp & _ & HPREc & HCHc & HPRc).
  pose proof HPREc as (HPREUc & HROc).
  pose proof (wv_rom_view B STK_put ly0 S0 U0 W0 regsC memC mdc' chp IMG HPREUc HROc) as HROMV.
  (* the literal '[' / '{' in .rodata *)
  assert (HLIT : In (wvc_open (wf_ty F), if wf_ty F =? 6 then [123] else [91]) FS_RO_STRS).
  { destruct Htyc as [Ety | Ety]; rewrite Ety; unfold wvc_open, WVC_LBRACE, WVC_LBRACKET; cbn; tauto. }
  assert (HZB : zbytes_at tfibsegs W0 memC (wvc_open (wf_ty F)) (if wf_ty F =? 6 then [123] else [91])).
  { destruct Htyc as [Ety | Ety]; rewrite Ety; (apply wv_rom_zbytes; [exact HROMV | vm_compute; reflexivity]). }
  assert (HSA : 4096 <= wvc_open (wf_ty F) <= 0x21180)
    by (unfold wvc_open, WVC_LBRACE, WVC_LBRACKET; destruct (wf_ty F =? 6); lia).
  (* put of the opening bracket (HPUT) *)
  eapply SRr_bind.
  { apply (HPUT ly0 S0 U0 W0 regsC memC mdc' chp (wf_ot F) (wf_o F) (wvc_open (wf_ty F)) 1 (wf_buf0 F)
      (wf_cap0 F) (wf_failed0 F) (wf_text0 F) (if wf_ty F =? 6 then [123] else [91]) (wf_live F) (wf_peak0 F)
      (wf_cnt0 F) (wf_fail0 F) HPREc HHD ltac:(lia)
      ltac:(rewrite R10; exact G10) R11 R12 HOUTC HGLOBC HUH ltac:(lia) HE_oot HE_ot16 HE_top HCHc HPRc HZB).
    - right; right; right. exists (if wf_ty F =? 6 then [123] else [91]).
      split; [exact HLIT | apply Nat.le_succ_diag_r].
    - destruct (wf_ty F =? 6); reflexivity.
    - unfold WriterSpec.bytes_ok. destruct (wf_ty F =? 6); (constructor; [cbv beta; lia | constructor]).
    - lia.
    - left. lia.
    - exact Hroom1.
    - exact HCAP.
    - exact HE_capl.
    - exact HBUD1. }
  (* put's post, composed back into write_value's journal: the open invariant (wvc_ret_invO) *)
  cbv beta. intros W3 c3 Hwle (st' & buf' & U3 & Est & Husw & Hpost).
  unfold wpost, fpostU in Hpost.
  destruct Hpost as (ly3 & S3 & regs3 & mem3 & md3 & Ec3 & HJc & OK3 & PO3 & HPRS & HOUT3 & HBK3 & HBSW & HWK &
    HGL3 & _).
  subst c3 st'.
  rewrite R1.
  apply (HK W3 (mkst regs3 (Z_to_bv 64 WVC_R_OPEN) mem3 (seg_rom tfibsegs)) md3 ly3 S3 U3 buf' Hwle).
  exact (wvc_ret_invO (wvc_POPEN F) Rest ly0 S0 U0 W0 memC mdc' (wf_buf0 F) regsC regsC (wf_keys F) 0 STK_put
    (wf_peak0 F) ly3 S3 U3 W3 regs3 mem3 md3 buf' HWPe eq_refl HJ1 HARU1 HSEMC (conj (Z.le_refl _) (Z.le_refl _))
    HCHC (eq_trans R9 G11) Hsp (eq_trans R8 G10) (eq_trans R9 G11) (eq_trans R19 G12)
    (Rcs 3%bv ltac:(left; reflexivity)) (Rcs 4%bv ltac:(right; left; reflexivity)) HJc OK3 PO3 HPRS HSTKp0 HSTKP
    Husw HOUT3 HBK3 HBSW HWK HGL3).
Qed.

End St.
End A.
