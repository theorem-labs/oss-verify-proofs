(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v; 1536 of its 1692 lines of code are new or changed and 1217 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_write_value.v, with its module names changed; 222 of its 422 lines of code are new or changed and 1492 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/ZZwv_cps.v; 469 of its 545 lines of code are new or changed and 346 lines of the source are left out. *)
(* write_value's CONTAINER arms (fs.asan image A, write_value 0x83d84): the two CALL SITES of the callee indent.
   - wvc_comma_ind: the comma's put returned (WVC_R_COMMA); the segment wvc_seg_comma runs to the next item's indent,
     indent writes WriterValue.wind pretty (d + 1), and the loop invariant holds at WVC_R_IND with the same item;
   - wvc_item_close: the last item's write_value returned (WVC_R_ITEM, i + 1 = n); the segment wvc_seg_item_last runs
     to the closing indent, indent writes WriterValue.wind pretty d, and the close-point invariant ZZwv_inv.wvc_invC
     holds at WVC_R_CLOSE (the node alone, the cursor at n);
   with the call step they share (wvc_ind_call: indent's premises from the invariant's facts at the call, its post
   handed on) and the close point's resume (wvc_ssN_ret: ZZwv_res.wvc_ssL_ret for wvc_ssN; wvc_ret_invC:
   ZZwv_step.wvc_ret_inv with the close-point invariant as its conclusion, regions from ZZwv_res.wvc_resume_rs0).
   Rule 24: no function proved here (call-site steps inside write_value's container arms; write_value's lookup: lane
   record (internal path), CHECKER CONFIRM a Theorem Labs lane). *)
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
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat
FSH_Fn_writer FSH_Fn_alloc FSW_K FSW_K3 FSW_ret FSW_rres FSW_writer_tbl FSW_writer_model FSW_writer_kit
FSH_Fn_reader FSW_rd FSupoisonStack FSW_pj ZZwv_defs ZZwv_inv ZZwv_kit ZZwv_comp ZZwv_tree ZZwv_call ZZwv_call2
ZZwv_call3 ZZwv_res ZZwv_ret ZZwv_runs2 ZZwv_step.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require AF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterValue PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the close state's regions (the frame with the prelude slots, the node alone) are well formed *)
Lemma wvc_rsN_wf : forall ty p, regions_wf (fsT_ret_regions WVC_F (wvc_csL p) [wvc_node ty]) = true.
Proof. intros ty p. vm_compute. reflexivity. Qed.

Section A. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Hypothesis HSS : FsShadowSyms B.
(* the arm instance: its fixed data and the entry state *)
Variable F : wvc_fix.
Variables (ly0 : alayout) (S0 : astate) (U0 : list (Z * Z)) (W0 : world tfibsegs) (mem0 : word -> option byte)
  (md0 : Model) (regs0 : bvmap 5 word).
(* the entry facts the arms' callers discharge once *)
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
Hypothesis HE_kk : 0 <= wf_kids F /\ wf_kids F + 56 * wf_n F <= alloc_ceiling /\
                   0 <= wf_keys F /\ wf_keys F + 8 * wf_n F <= alloc_ceiling.

(* ZZwv_step.wvc_d1 at this instance: the item depth d + 1 is an int32 *)
Lemma wvc_d1c : wf_d F + 1 < 2 ^ 31.
Proof.
destruct HE_ty as [(_ & items & Ht & _ & _) | (_ & members & Ht & _)];
  rewrite Ht in HE_dd; cbn [PjTree.depth] in HE_dd; lia.
Qed.

(* membership in a kept-register list *)
Local Ltac wvc_inq := cbv [In]; repeat (first [left; reflexivity | right]).

(* ================= the close state from the plain resumed state (ZZwv_res.wvc_ssL_ret, node alone) ============ *)
Lemma wvc_ssN_ret : forall E ty p ms n,
  st_ok tfibsegs E (fss_retT WVC_R_CLOSE WVC_F (wvc_csL p) [wvc_node ty] wvc_gf0) ms ->
  YK11.getr (ms_regs ms) 18%bv = sv_denot E (wvc_shv 9 40) ->
  YK11.getr (ms_regs ms) 20%bv = sv_denot E (SOff 9 40) ->
  YK11.getr (ms_regs ms) 22%bv = sv_denot E (SAlu ALU_SUB (SOff (xatom 18) 0) (SOff (xatom 2) 0)) ->
  YK11.getr (ms_regs ms) 23%bv = sv_denot E (SOff 9 24) ->
  YK11.getr (ms_regs ms) 24%bv = sv_denot E (SAlu ALU_ADD (SAluw ALU_ADD (SOff (xatom 4) 0) (SLit 1)) (SLit 0)) ->
  YK11.getr (ms_regs ms) 26%bv = sv_denot E (wvc_shv 9 24) ->
  YK11.getr (ms_regs ms) 27%bv = sv_denot E (wvc_shv 9 0) ->
  ew E 19 = Z_to_bv 64 p -> 0 <= p < 2 ^ 64 -> ew E (xatom 3) = Z_to_bv 64 n -> 0 < n < 2 ^ 64 ->
  st_ok tfibsegs E (wvc_ssN ty p) ms.
Proof.
intros E ty p ms n HS R18 R20 R22 R23 R24 R26 R27 E19 Hp En Hn.
unfold wvc_ssN.
apply st_ok_add_cond.
2: { rewrite branch_ne_U, U_SLit, (U_atom E (xatom 3) n En) by lia.
     change (zcanon 0) with 0. apply negb_true_iff, Z.eqb_neq. lia. }
apply st_ok_add_cond.
2: { destruct (Z.eqb_spec p 0) as [->|Hp0]; cbv beta iota.
     - rewrite branch_eq_U, U_SLit, (U_atom E 19 0 E19) by lia. vm_compute. reflexivity.
     - rewrite branch_ne_U, U_SLit, (U_atom E 19 p E19) by lia.
       change (zcanon 0) with 0. apply negb_true_iff, Z.eqb_neq. exact Hp0. }
apply wvc_st_ok_setr; [exact HS|].
repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  (split; [intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz | assumption]).
Qed.

(* ================= the return of the closing indent: the close-point invariant at WVC_R_CLOSE =================
   ZZwv_step.wvc_ret_inv's statement and proof with wvc_invC as its conclusion: the cursor at n, no key slot (the
   env's key slot is keys + 8 * n with key 0), the regions of the node alone (ZZwv_res.wvc_resume_rs0) *)
Lemma wvc_ret_invC : forall Pd Pc Rest ly S U (W : world tfibsegs) memC mdC buf regsC R0 ke key
    STKc peak ly' S' U' (W' : world tfibsegs) regs' mem' md' buf',
  wvc_WP F = Pd ++ Pc ++ Rest ->
  ajournal tfibsegs B (wvc_STK F) (wf_ot F) (wvc_FP F) ly0 S0 W0 (unpoison U0 mem0) md0 []
    ly S W (unpoison U memC) mdC (wevk (wf_cap0 F) (wvc_stP F Pd)) ->
  ARU tfibsegs B ly S U W memC mdC ->
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly S U W memC buf (wvc_stP F Pd) ->
  wf_peak0 F <= peak <= Z.max (wf_peak0 F) (wf_live F - wf_cap0 F + WriterApp.w_cap (wvc_stP F Pd)) ->
  Forall (YP09.chunk_ok tfibsegs (wvc_E F regs0 R0 ke key) (rdW W memC) (wf_sp F - WVC_F)) (wvc_csL (wf_p F)) ->
  YK11.getr R0 9%bv = w64 (wf_v F) ->
  spZ regsC = wf_sp F - WVC_F ->
  YK11.getr regsC 8%bv = w64 (wf_o F) -> YK11.getr regsC 9%bv = w64 (wf_v F) ->
  YK11.getr regsC 19%bv = w64 (wf_p F) -> YK11.getr regsC 21%bv = w64 (wf_n F) ->
  YK11.getr regsC 25%bv = w64 (56 * wf_n F) -> YK11.getr regsC 22%bv = w64 (8 * wf_n F) ->
  YK11.getr regsC 3%bv = YK11.getr regs0 3%bv -> YK11.getr regsC 4%bv = YK11.getr regs0 4%bv ->
  YK11.getr regsC 18%bv = w64 ((wf_v F + 40) / 8 + SHADOW_OFF) ->
  YK11.getr regsC 20%bv = w64 (wf_v F + 40) -> YK11.getr regsC 23%bv = w64 (wf_v F + 24) ->
  YK11.getr regsC 24%bv = w64 (wf_d F + 1) ->
  YK11.getr regsC 26%bv = w64 ((wf_v F + 24) / 8 + SHADOW_OFF) ->
  YK11.getr regsC 27%bv = w64 (wf_v F / 8 + SHADOW_OFF) ->
  0 < wf_n F ->
  ajournal tfibsegs B (STKc + (wf_ot F - spZ regsC)) (wf_ot F)
    (FS_PSTAT_FP ++ wbuf_fp buf (WriterApp.w_cap (wvc_stP F Pd))) ly S W (unpoison U memC) mdC []
    ly' S' W' (unpoison U' mem') md'
    (wevk (WriterApp.w_cap (wvc_stP F Pd)) (WriterApp.putN (wv_rst (wvc_stP F Pd)) Pc)) ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' -> aregs_preserved regsC regs' ->
  0 <= STKc -> STKc + WVC_F <= STK_write_value (wf_m F) ->
  uswap U U' buf buf' (WriterApp.w_cap (wvc_stP F Pd)) ->
  wout_ok B tfibsegs ly' S' W' mem' (wf_o F) buf' (WriterApp.w_cap (WriterApp.putN (wv_rst (wvc_stP F Pd)) Pc))
    (WriterApp.w_failed (WriterApp.putN (wv_rst (wvc_stP F Pd)) Pc))
    (WriterApp.w_text (WriterApp.putN (wv_rst (wvc_stP F Pd)) Pc)) ->
  wbudget_kept S S' (WriterApp.w_failed (wvc_stP F Pd)) (WriterApp.w_cap (wvc_stP F Pd))
    (WriterApp.w_cnt (wvc_stP F Pd))
    (WriterApp.w_failed (WriterApp.putN (wv_rst (wvc_stP F Pd)) Pc))
    (WriterApp.w_cap (WriterApp.putN (wv_rst (wvc_stP F Pd)) Pc))
    (WriterApp.w_cnt (WriterApp.putN (wv_rst (wvc_stP F Pd)) Pc)) ->
  bswap (ablocks B ly S) (ablocks B ly' S') buf buf' (WriterApp.w_cap (wvc_stP F Pd))
    (WriterApp.w_cap (WriterApp.putN (wv_rst (wvc_stP F Pd)) Pc)) ->
  wkeep tfibsegs W W' memC mem' (spZ regsC) (wf_ot F) (wf_o F) 32 ->
  (exists peak', peak <= peak' <= Z.max peak ((wf_live F + WriterApp.w_cap (wvc_stP F Pd) - wf_cap0 F) -
                    WriterApp.w_cap (wvc_stP F Pd) + WriterApp.w_cap (WriterApp.putN (wv_rst (wvc_stP F Pd)) Pc)) /\
     fs_glob tfibsegs W' mem' ((wf_live F + WriterApp.w_cap (wvc_stP F Pd) - wf_cap0 F) +
       WriterApp.w_cap (WriterApp.putN (wv_rst (wvc_stP F Pd)) Pc) - WriterApp.w_cap (wvc_stP F Pd)) peak'
       (WriterApp.w_cnt (WriterApp.putN (wv_rst (wvc_stP F Pd)) Pc))
       (WriterApp.w_fail (WriterApp.putN (wv_rst (wvc_stP F Pd)) Pc))) ->
  wvc_invC B F (Pd ++ Pc) ly0 S0 U0 W0 mem0 md0 regs0
    W' (mkst regs' (Z_to_bv 64 WVC_R_CLOSE) mem' (seg_rom tfibsegs)) md' ly' S' U' buf'.
Proof.
intros Pd Pc Rest ly S U W memC mdC buf regsC R0 ke key STKc peak ly' S' U' W' regs' mem' md' buf'
  HWP HJ HARU HSEM Hpk HCH HR09 Hsp R8 R9 R19 R21 R25 R22 R3 R4 R18 R20 R23 R24 R26 R27 Hn
  HJc OK' PO' HP HSTK0 HSTKc HUS' HOUT' HBK' HBS' HWK' HGL'.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HWF : WVC_F = 176) by reflexivity.
pose proof (wvc_stk (wf_m F)) as (HSTKF & _).
pose proof (wvc_sem_o_sp B F ly0 S0 U0 W0 mem0 regs0 ly S U W memC buf _ HSEM) as Hosp.
pose proof (proj1 HARU) as HAR.
pose proof (wvc_v_low B F ly0 S0 U0 W0 mem0 regs0 ly S U W (unpoison U memC) mdC memC buf _ HAR HSEM) as (Hv1 & Hv2).
assert (Hlo' : alloc_ceiling <= wf_sp F - WVC_F) by lia.
set (st := wvc_stP F Pd) in *.
(* the count stays below 2^64, the cap only grows from the entry's *)
assert (Hcnt : wf_cnt0 F + wcalls (WriterApp.putN st Pc) < 2 ^ 64).
{ pose proof HE_bud as (_ & _ & _ & HB4). rewrite HWP, app_assoc, WriterApp.putN_app, WriterApp.putN_app in HB4.
  pose proof (zzwv_calls_mono Rest (WriterApp.putN (WriterApp.putN (wvc_st0 F) Pd) Pc)) as M.
  unfold st, wvc_stP in *. lia. }
assert (Hcap0i : wf_cap0 F <= WriterApp.w_cap st) by exact (wv_cap_mono (wvc_st0 F) Pd HE_cap0).
(* the writer facts at the return *)
destruct (wvc_sem_call B F ly0 S0 U0 W0 mem0 regs0 ly S U W memC mdC buf st Pc ly' S' U' W' mem' md' buf'
  (STKc + (wf_ot F - spZ regsC)) _ (spZ regsC) peak HSEM HARU HE_cap0 Hcap0i HE_cnt0 Hcnt Hlo' HE_oot Hpk HJc OK' PO'
  HUS' HOUT' HBK' HBS' HWK' ltac:(lia) HGL') as (HARU' & HSEM').
pose proof HSEM as (HOUT & _ & _ & _ & HBS & _ & _ & _ & _ & _ & _ & _ & _ & _ & HBIN & _).
pose proof HOUT as (_ & _ & _ & _ & _ & Hcap64 & _).
pose proof HSEM' as (_ & _ & HHD' & _ & _ & _ & _ & _ & HN' & HPO' & HNB' & HUL' & HDb' & _).
destruct (wvc_hdr_at B F ly0 S0 U0 W0 mem0 regs0 HE_hdr ly' S' U' W' mem' buf' _ HSEM') as (num & capn & HHDR').
(* the journal's footprint at the call *)
pose proof (wv_fp_sub_swap B ly0 S0 ly S W (unpoison U memC) mdC (wf_buf0 F) (wf_cap0 F) buf (WriterApp.w_cap st)
  HAR HBS HBIN ltac:(lia) wvc_pstat_img) as HFPSUB.
assert (Hrs : forall q : bv 5, acallee_saved (bv_unsigned q) -> getr regs' q = getr regsC q)
  by (intros q Hq; exact (fsw_pres regsC regs' q HP Hq)).
(* the close point's env: the key slot past the last item, no key *)
set (E' := wvc_E F regs0 regs' (wf_keys F + 8 * wf_n F) 0).
assert (E2' : bv_unsigned (ew E' 2) = wf_sp F - WVC_F).
{ unfold E'. rewrite (wvc_E_r F regs0 regs' _ _ 2%bv 2 eq_refl),
    (Hrs 2%bv ltac:(apply (wvc_cs_z _ 2); [reflexivity | lia])).
  exact Hsp. }
assert (E9' : ew E' 9 = Z_to_bv 64 (wf_v F)).
{ unfold E'. rewrite (wvc_E_r F regs0 regs' _ _ 9%bv 9 eq_refl),
    (Hrs 9%bv ltac:(apply (wvc_cs_z _ 9); [reflexivity | lia])).
  exact R9. }
assert (E19' : ew E' 19 = Z_to_bv 64 (wf_p F)).
{ unfold E'. rewrite (wvc_E_r F regs0 regs' _ _ 19%bv 19 eq_refl),
    (Hrs 19%bv ltac:(apply (wvc_cs_z _ 19); [reflexivity | lia])).
  exact R19. }
assert (E32' : ew E' 32 = Z_to_bv 64 SHADOW_OFF) by (unfold E'; apply wvc_E_32).
assert (EX : forall j, ew E' (xatom j) =
  nth j (wvc_xs regs0 (wf_str F) (wf_kids F) (wf_keys F) (wf_n F) (wf_d F) (wf_keys F + 8 * wf_n F) 0)
    (Z_to_bv 64 0)) by (intros j; unfold E'; apply wvc_E_x).
(* the frame chunks at the return, in the return env *)
assert (HCH' : Forall (YP09.chunk_ok tfibsegs E' (rdW W' mem') (wf_sp F - WVC_F)) (wvc_csL (wf_p F))).
{ apply (wvc_csL_after (wvc_E F regs0 R0 ke key) E' W W' memC mem' (wf_sp F) (spZ regsC) (wf_ot F) (wf_o F) (wf_p F)
    HCH HWK'); [lia | lia | lia | | |].
  - rewrite E9', (wvc_E_r F regs0 R0 ke key 9%bv 9 eq_refl). symmetry. exact HR09.
  - rewrite E32'. unfold wvc_E. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity.
  - intros j Hj. rewrite EX, wvc_E_x.
    do 18 (destruct j as [|j]; [cbn [nth wvc_xs app map]; reflexivity|]). exfalso. lia. }
(* the regions of the close state at the return: the node alone *)
destruct (wvc_resume_rs0 B ly' S' U' W' mem' md' E' (wf_ty F) (wvc_csL (wf_p F)) (wf_v F) num (wf_str F) (wf_kids F)
  (wf_keys F) (wf_n F) capn (wf_sp F) HARU' HPO' HHDR' E2' Hlo' ltac:(lia) E9' E32'
  ltac:(rewrite EX; reflexivity) ltac:(rewrite EX; reflexivity)
  ltac:(rewrite EX; reflexivity) ltac:(rewrite EX; reflexivity))
  as (HRS & HPD & HGF & HSH).
(* the after-call step *)
destruct (wvc_after_call2 B (wvc_STK F) (wf_ot F) (wvc_FP F) [] ly0 S0 U0 W0 W mem0 md0 ly S U memC mdC
  (wevk (wf_cap0 F) st) STKc (FS_PSTAT_FP ++ wbuf_fp buf (WriterApp.w_cap st)) (wf_ot F) WVC_F regsC ly' S' U' W'
  regs' mem' md' (wevk (WriterApp.w_cap st) (WriterApp.putN (wv_rst st) Pc))
  (wvc_xs regs0 (wf_str F) (wf_kids F) (wf_keys F) (wf_n F) (wf_d F) (wf_keys F + 8 * wf_n F) 0)
  (wvc_csL (wf_p F)) [wvc_node (wf_ty F)] wvc_gf0 WVC_R_CLOSE (wf_sp F) HSS HJ HARU HJc HFPSUB OK' PO' HP Hsp
  ltac:(unfold WVC_F; lia) HSTK0 ltac:(unfold wvc_STK; lia) ltac:(reflexivity) HE_sp16
  ltac:(lia) ltac:(lia) ltac:(lia)
  (wvc_rsN_wf (wf_ty F) (wf_p F))
  HCH' HRS HPD HGF) as (HJ' & HARU'' & HST).
(* the close state *)
assert (HSL : st_ok tfibsegs E' (wvc_ssN (wf_ty F) (wf_p F))
  (restrict (w_H W') (mkst regs' (Z_to_bv 64 WVC_R_CLOSE) mem' (seg_rom tfibsegs)))).
{ apply (wvc_ssN_ret E' (wf_ty F) (wf_p F) _ (wf_n F) HST).
  - cbn [ms_regs restrict mkst]; rewrite (Hrs 18%bv ltac:(apply (wvc_cs_z _ 18); [reflexivity | lia])), R18,
      (wvc_den_val E' (wvc_shv 9 40) _ (wvc_shv_U E' 40 (wf_v F) E9' E32' ltac:(lia) ltac:(lia) ltac:(lia))).
    reflexivity.
  - cbn [ms_regs restrict mkst]; rewrite (Hrs 20%bv ltac:(apply (wvc_cs_z _ 20); [reflexivity | lia])), R20,
      (wvc_den_val E' (SOff 9 40) _ (wvc_u_off E' 9 (wf_v F) 40 E9' ltac:(lia) ltac:(lia))).
    reflexivity.
  - cbn [ms_regs restrict mkst]; rewrite (Hrs 22%bv ltac:(apply (wvc_cs_z _ 22); [reflexivity | lia])), R22,
      (wvc_den_val E' _ _ (wvc_sub_U E' (wf_keys F + 8 * wf_n F) (wf_keys F) ltac:(rewrite EX; reflexivity)
         ltac:(rewrite EX; reflexivity) ltac:(lia) ltac:(lia))).
    unfold w64. f_equal. lia.
  - cbn [ms_regs restrict mkst]; rewrite (Hrs 23%bv ltac:(apply (wvc_cs_z _ 23); [reflexivity | lia])), R23,
      (wvc_den_val E' (SOff 9 24) _ (wvc_u_off E' 9 (wf_v F) 24 E9' ltac:(lia) ltac:(lia))).
    reflexivity.
  - cbn [ms_regs restrict mkst]; rewrite (Hrs 24%bv ltac:(apply (wvc_cs_z _ 24); [reflexivity | lia])), R24,
      (wvc_den_val E' _ _ (wvc_d1_U E' (wf_d F) ltac:(rewrite EX; reflexivity) HE_d wvc_d1c)).
    reflexivity.
  - cbn [ms_regs restrict mkst]; rewrite (Hrs 26%bv ltac:(apply (wvc_cs_z _ 26); [reflexivity | lia])), R26,
      (wvc_den_val E' (wvc_shv 9 24) _ (wvc_shv_U E' 24 (wf_v F) E9' E32' ltac:(lia) ltac:(lia) ltac:(lia))).
    reflexivity.
  - cbn [ms_regs restrict mkst]; rewrite (Hrs 27%bv ltac:(apply (wvc_cs_z _ 27); [reflexivity | lia])), R27,
      (wvc_den_val E' (wvc_shv 9 0) _ (wvc_shv_U E' 0 (wf_v F) E9' E32' ltac:(lia) ltac:(lia) ltac:(lia))).
    rewrite Z.add_0_r. reflexivity.
  - exact E19'.
  - lia.
  - rewrite EX. reflexivity.
  - lia. }
assert (Hval : forall (q : bv 5) z, acallee_saved (bv_unsigned q) -> getr regsC q = w64 z ->
  YK11.getr (ms_regs (mkst regs' (Z_to_bv 64 WVC_R_CLOSE) mem' (seg_rom tfibsegs))) q = w64 z).
{ intros q z Hq E. cbn [ms_regs mkst]. rewrite (Hrs q Hq). exact E. }
unfold wvc_invC. cbv zeta. fold E'.
split.
{ split; [exact HSL|]. split; [exact HSH|].
  split.
  - assert (ESP : wevk (wf_cap0 F) (WriterApp.putN (wvc_st0 F) (Pd ++ Pc))
       = wevk (wf_cap0 F) st
         + wevk (WriterApp.w_cap st) (WriterApp.putN (wv_rst st) Pc))
      by exact (wv_wevk_split (wvc_st0 F) Pd Pc eq_refl HE_cap0).
    unfold wvc_stP. rewrite ESP. exact HJ'.
  - exact HARU''. }
split.
{ unfold wvc_stP. rewrite WriterApp.putN_app. cbn [ms_mem mkst]. exact HSEM'. }
split; [exact (Hval 8%bv _ ltac:(apply (wvc_cs_z _ 8); [reflexivity | lia]) R8)|].
split; [exact (Hval 9%bv _ ltac:(apply (wvc_cs_z _ 9); [reflexivity | lia]) R9)|].
split; [exact (Hval 19%bv _ ltac:(apply (wvc_cs_z _ 19); [reflexivity | lia]) R19)|].
split; [exact (Hval 21%bv _ ltac:(apply (wvc_cs_z _ 21); [reflexivity | lia]) R21)|].
split; [exact (Hval 25%bv _ ltac:(apply (wvc_cs_z _ 25); [reflexivity | lia]) R25)|].
split; [cbn [ms_regs mkst]; rewrite (Hrs 3%bv ltac:(apply (wvc_cs_z _ 3); [reflexivity | lia])); exact R3|].
split; [cbn [ms_regs mkst]; rewrite (Hrs 4%bv ltac:(apply (wvc_cs_z _ 4); [reflexivity | lia])); exact R4|].
split; [exact (Hval 18%bv _ ltac:(apply (wvc_cs_z _ 18); [reflexivity | lia]) R18)|].
split; [exact (Hval 20%bv _ ltac:(apply (wvc_cs_z _ 20); [reflexivity | lia]) R20)|].
split; [exact (Hval 22%bv _ ltac:(apply (wvc_cs_z _ 22); [reflexivity | lia]) R22)|].
split; [exact (Hval 23%bv _ ltac:(apply (wvc_cs_z _ 23); [reflexivity | lia]) R23)|].
split; [exact (Hval 24%bv _ ltac:(apply (wvc_cs_z _ 24); [reflexivity | lia]) R24)|].
split; [exact (Hval 26%bv _ ltac:(apply (wvc_cs_z _ 26); [reflexivity | lia]) R26)|].
split; [exact (Hval 27%bv _ ltac:(apply (wvc_cs_z _ 27); [reflexivity | lia]) R27)|].
split.
{ cbn [ms_regs mkst]. unfold spZ. rewrite (Hrs 2%bv ltac:(apply (wvc_cs_z _ 2); [reflexivity | lia])). exact Hsp. }
exact Hn.
Qed.

(* ================= one call of indent from the loop, at the call registers the segment hands over =================
   indent's premises from the invariant's facts at the call memory (ms_mem ms'): fpreU, the chain clause at o and the
   window presence by ZZwv_call3.wvc_callpre (its case-1 premise from the frame's saved-ra chunk at offset 168), the
   writer facts by wvc_sem, the frames bound by the journal, room and budget by the model split; its post is handed
   on in the form ZZwv_step.wvc_ret_inv / wvc_ret_invC take *)
Lemma wvc_ind_call : forall Pd Rest dd ly S U (W : world tfibsegs) ms' mdc' buf R0 ke key
    (Q : world tfibsegs -> config -> Prop),
  indent_spec B tfibsegs ->
  wvc_WP F = Pd ++ WriterValue.wind (negb (wf_p F =? 0)) dd ++ Rest ->
  ms' = mkst (ms_regs ms') (w64 A_indent) (ms_mem ms') (seg_rom tfibsegs) ->
  ajournal tfibsegs B (wvc_STK F) (wf_ot F) (wvc_FP F) ly0 S0 W0 (unpoison U0 mem0) md0 []
    ly S W (unpoison U (ms_mem ms')) mdc' (wevk (wf_cap0 F) (wvc_stP F Pd)) ->
  ARU tfibsegs B ly S U W (ms_mem ms') mdc' ->
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly S U W (ms_mem ms') buf (wvc_stP F Pd) ->
  Forall (YP09.chunk_ok tfibsegs (wvc_E F regs0 R0 ke key) (rdW W (ms_mem ms')) (wf_sp F - WVC_F))
    (wvc_csL (wf_p F)) ->
  spZ (ms_regs ms') = wf_sp F - WVC_F ->
  YK0s.ret_ok (YK11.getr (ms_regs ms') 1%bv) -> 4096 <= raZ (ms_regs ms') ->
  YK11.getr (ms_regs ms') 3%bv = YK11.getr regs0 3%bv -> YK11.getr (ms_regs ms') 4%bv = YK11.getr regs0 4%bv ->
  YK11.getr (ms_regs ms') 8%bv = w64 (wf_o F) ->
  YK11.getr (ms_regs ms') 10%bv = w64 (wf_o F) -> YK11.getr (ms_regs ms') 11%bv = w64 (wf_p F) ->
  YK11.getr (ms_regs ms') 12%bv = w64 dd -> 0 <= dd < 2 ^ 31 ->
  (forall peak ly' S' U' (W' : world tfibsegs) regs' mem' md' buf',
     wf_peak0 F <= peak <= Z.max (wf_peak0 F) (wf_live F - wf_cap0 F + WriterApp.w_cap (wvc_stP F Pd)) ->
     ajournal tfibsegs B (STK_indent + (wf_ot F - spZ (ms_regs ms'))) (wf_ot F)
       (FS_PSTAT_FP ++ wbuf_fp buf (WriterApp.w_cap (wvc_stP F Pd))) ly S W (unpoison U (ms_mem ms')) mdc' []
       ly' S' W' (unpoison U' mem') md'
       (wevk (WriterApp.w_cap (wvc_stP F Pd))
          (WriterApp.putN (wv_rst (wvc_stP F Pd)) (WriterValue.wind (negb (wf_p F =? 0)) dd))) ->
     upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' -> aregs_preserved (ms_regs ms') regs' ->
     uswap U U' buf buf' (WriterApp.w_cap (wvc_stP F Pd)) ->
     wout_ok B tfibsegs ly' S' W' mem' (wf_o F) buf'
       (WriterApp.w_cap (WriterApp.putN (wv_rst (wvc_stP F Pd)) (WriterValue.wind (negb (wf_p F =? 0)) dd)))
       (WriterApp.w_failed (WriterApp.putN (wv_rst (wvc_stP F Pd)) (WriterValue.wind (negb (wf_p F =? 0)) dd)))
       (WriterApp.w_text (WriterApp.putN (wv_rst (wvc_stP F Pd)) (WriterValue.wind (negb (wf_p F =? 0)) dd))) ->
     wbudget_kept S S' (WriterApp.w_failed (wvc_stP F Pd)) (WriterApp.w_cap (wvc_stP F Pd))
       (WriterApp.w_cnt (wvc_stP F Pd))
       (WriterApp.w_failed (WriterApp.putN (wv_rst (wvc_stP F Pd)) (WriterValue.wind (negb (wf_p F =? 0)) dd)))
       (WriterApp.w_cap (WriterApp.putN (wv_rst (wvc_stP F Pd)) (WriterValue.wind (negb (wf_p F =? 0)) dd)))
       (WriterApp.w_cnt (WriterApp.putN (wv_rst (wvc_stP F Pd)) (WriterValue.wind (negb (wf_p F =? 0)) dd))) ->
     bswap (ablocks B ly S) (ablocks B ly' S') buf buf' (WriterApp.w_cap (wvc_stP F Pd))
       (WriterApp.w_cap (WriterApp.putN (wv_rst (wvc_stP F Pd)) (WriterValue.wind (negb (wf_p F =? 0)) dd))) ->
     wkeep tfibsegs W W' (ms_mem ms') mem' (spZ (ms_regs ms')) (wf_ot F) (wf_o F) 32 ->
     (exists peak', peak <= peak' <= Z.max peak ((wf_live F + WriterApp.w_cap (wvc_stP F Pd) - wf_cap0 F) -
                       WriterApp.w_cap (wvc_stP F Pd) +
                       WriterApp.w_cap (WriterApp.putN (wv_rst (wvc_stP F Pd))
                         (WriterValue.wind (negb (wf_p F =? 0)) dd))) /\
        fs_glob tfibsegs W' mem' ((wf_live F + WriterApp.w_cap (wvc_stP F Pd) - wf_cap0 F) +
          WriterApp.w_cap (WriterApp.putN (wv_rst (wvc_stP F Pd)) (WriterValue.wind (negb (wf_p F =? 0)) dd)) -
          WriterApp.w_cap (wvc_stP F Pd)) peak'
          (WriterApp.w_cnt (WriterApp.putN (wv_rst (wvc_stP F Pd)) (WriterValue.wind (negb (wf_p F =? 0)) dd)))
          (WriterApp.w_fail (WriterApp.putN (wv_rst (wvc_stP F Pd)) (WriterValue.wind (negb (wf_p F =? 0)) dd)))) ->
     SRr tfibsegs W' (mkCfg (mkst regs' (YK11.getr (ms_regs ms') 1%bv) mem' (seg_rom tfibsegs)) md') Q) ->
  SRr tfibsegs W (mkCfg ms' mdc') Q.
Proof.
intros Pd Rest dd ly S U W ms' mdc' buf R0 ke key Q HIND HWP Ems HJ HARU HSEM HCH Hsp Hret Hra4 G3 G4 G8 G10 G11
  G12 Hdd K.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HWF : WVC_F = 176) by reflexivity.
pose proof (wvc_stk (wf_m F)) as (HSTKF & _ & HSTKi & _).
pose proof (wvc_sem_o_sp B F ly0 S0 U0 W0 mem0 regs0 ly S U W (ms_mem ms') buf _ HSEM) as Hosp.
assert (Hlo : alloc_ceiling <= wf_sp F - WVC_F) by lia.
set (st := wvc_stP F Pd) in *.
pose proof HJ as (_ & HLY & _ & _ & _ & HFRS & HNEV & _).
assert (Etop : ly_top ly = ly_top ly0) by (destruct HLY as (_ & _ & _ & _ & _ & _ & _ & _ & E & _); exact E).
pose proof HSEM as (HOUT & (peak & Hpk & HG) & HHD & _ & _ & (HCAPW & HBB & _) & HCNT & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & HUH).
(* case 1 of the chain clause: the word at sp - 8 is write_value's saved ra, the frame chunk at offset 168 *)
assert (HC1 : wf_o F = wf_sp F + 8 ->
  rdword (aview tfibsegs (w_H W) (unpoison U (ms_mem ms'))) (wf_sp F - 8) = Some (raZ regs0)).
{ intros _.
  assert (Hc : YP09.chunk_ok tfibsegs (wvc_E F regs0 R0 ke key) (rdW W (ms_mem ms')) (wf_sp F - WVC_F)
                 (YP09.mkChunk 168 (CVal 8 (SOff (xatom 17) 0)))).
  { apply (proj1 (Forall_forall _ _) HCH). unfold wvc_csL, wvc_cs0.
    apply in_or_app. right. apply in_cons. apply in_map_iff. exists 12%nat.
    split; [reflexivity | apply in_seq; lia]. }
  assert (He : sv_denot (wvc_E F regs0 R0 ke key) (SOff (xatom 17) 0) = Z_to_bv 64 (raZ regs0)).
  { rewrite fsw_SOff0, wvc_E_x. cbn [nth wvc_xs app map wvc_saved]. unfold raZ.
    rewrite Z_to_bv_bv_unsigned. reflexivity. }
  pose proof (val_of_chunk_ok tfibsegs _ _ _ 168 8 (SOff (xatom 17) 0) (raZ regs0) Hc He
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold raZ; apply u64_range) ltac:(cbn; lia)) as VM.
  replace (wf_sp F - WVC_F + 168) with (wf_sp F - 8) in VM by lia.
  change (N.to_nat 8) with 8%nat in VM.
  pose proof (AF0x.val_mem_rdword (w_H W) (ms_mem ms') (wf_sp F - 8) (raZ regs0)
    ltac:(unfold raZ; apply u64_range) VM) as RW.
  rewrite (rdword_ext (aview tfibsegs (w_H W) (ms_mem ms')) _ (wf_sp F - 8)); [exact RW|].
  intros k Hk. apply aview_unpoison_out.
  apply (zwk_p_stack_not_ush B ly S U W (ms_mem ms') mdc' _ HARU). lia. }
assert (Hs0 : s0Z (ms_regs ms') = wf_o F).
{ unfold s0Z. rewrite G8. unfold w64. apply unsigned_lit_small. lia. }
destruct (wvc_callpre B F ly0 S0 U0 W0 mem0 md0 regs0 ly S U W (ms_mem ms') mdc' (wevk (wf_cap0 F) st) buf st
  (ms_regs ms') STK_indent HJ HARU HSEM HC1 Hsp HE_sp16 HE_ot16 ltac:(lia) ltac:(vm_compute; discriminate)
  HSTKi Hret Hra4 ltac:(rewrite G3; exact HE_gp) ltac:(rewrite G4; exact HE_tp) Hs0 HE_oot ltac:(lia) HE_o8 Hlo)
  as (ch & _ & HPRE & HCHO & HPRES).
(* the frames, the room, the cap and the budget at the call *)
assert (HFRL : Z.of_nat (length (frames S)) <= FRL_CRT_CALLEE) by (rewrite HFRS; exact HE_frl).
assert (HROOM : Z.of_nat (length (WriterApp.w_text st)) +
    Z.of_nat (length (concat (WriterValue.wind (negb (wf_p F =? 0)) dd))) + 1 <= WMAX).
{ pose proof (wv_room_mid (wvc_st0 F) Pd (WriterValue.wind (negb (wf_p F =? 0)) dd ++ Rest)) as R.
  assert (L1 : length (concat (WriterValue.wind (negb (wf_p F =? 0)) dd ++ Rest)) =
    Nat.add (length (concat (WriterValue.wind (negb (wf_p F =? 0)) dd))) (length (concat Rest)))
    by (rewrite concat_app, length_app; reflexivity).
  pose proof HE_room as HR. rewrite HWP in HR.
  change (WriterApp.w_text (wvc_st0 F)) with (wf_text0 F) in R.
  unfold st, wvc_stP. lia. }
assert (HCAPL : WriterApp.w_cap st <= wf_live F + WriterApp.w_cap st - wf_cap0 F) by lia.
assert (HBUD : wbudget_pre S (WriterApp.w_cap st) (WriterApp.w_cnt st) (wf_live F + WriterApp.w_cap st - wf_cap0 F)
  (WriterApp.putN (wv_rst st) (WriterValue.wind (negb (wf_p F =? 0)) dd))).
{ pose proof HE_bud as HB. rewrite HWP, app_assoc in HB. unfold wvc_st0 in HB.
  pose proof (wv_budget_pre_prefix S0 (wf_cap0 F) (wf_cnt0 F) (wf_live F) (wf_failed0 F) (wf_text0 F) (wf_fail0 F)
    (Pd ++ WriterValue.wind (negb (wf_p F =? 0)) dd) Rest HE_cap0 HB) as HB2.
  pose proof (wv_budget_pre_mid S0 S (wf_cap0 F) (wf_cnt0 F) (wf_live F) (wf_failed0 F) (wf_text0 F) (wf_fail0 F)
    Pd (WriterValue.wind (negb (wf_p F =? 0)) dd) HE_cap0 HB2 HNEV HBB HCNT) as HB3.
  replace (wf_live F + WriterApp.w_cap st - wf_cap0 F) with (wf_live F - wf_cap0 F + WriterApp.w_cap st) by lia.
  exact HB3. }
(* the call *)
rewrite Ems.
eapply SRr_bind.
{ exact (HIND ly S U W (ms_regs ms') (ms_mem ms') mdc' ch (wf_ot F) (wf_o F) (wf_p F) dd buf
    (WriterApp.w_cap st) (WriterApp.w_failed st) (WriterApp.w_text st) (wf_live F + WriterApp.w_cap st - wf_cap0 F)
    peak (WriterApp.w_cnt st) (WriterApp.w_fail st) HPRE HHD HFRL G10 G11 G12 HE_p ltac:(lia) HOUT HG HUH
    ltac:(lia) HE_oot HE_ot16 ltac:(lia) HCHO HPRES HROOM HCAPW HCAPL HBUD). }
(* the return *)
cbv beta. intros W' c' _ (st' & buf' & U' & Est & HUS' & HWPOST).
unfold wpost, fpostU in HWPOST.
destruct HWPOST as (ly' & S' & regs' & mem' & md' & Ec & HJc & OK' & PO' & HP & HOUT2 & HBK' & HBS' & HWK' & HGL2).
subst c' st'.
exact (K peak ly' S' U' W' regs' mem' md' buf' Hpk HJc OK' PO' HP HUS' HOUT2 HBK' HBS' HWK' HGL2).
Qed.

(* ================= (1) the comma's put returned: the next item's indent, to WVC_R_IND ================= *)
Lemma wvc_comma_ind : forall i ke key Pd Rest ly S U (W : world tfibsegs) ms mdc buf
    (Q : world tfibsegs -> config -> Prop),
  indent_spec B tfibsegs ->
  wvc_WP F = Pd ++ WriterValue.wind (negb (wf_p F =? 0)) (wf_d F + 1) ++ Rest ->
  wvc_inv B F WVC_R_COMMA i ke key Pd ly0 S0 U0 W0 mem0 md0 regs0 W ms mdc ly S U buf ->
  (forall ly' S' U' (W' : world tfibsegs) regs' mem' md' buf' key',
     wvc_inv B F WVC_R_IND i ke key' (Pd ++ WriterValue.wind (negb (wf_p F =? 0)) (wf_d F + 1))
       ly0 S0 U0 W0 mem0 md0 regs0
       W' (mkst regs' (Z_to_bv 64 WVC_R_IND) mem' (seg_rom tfibsegs)) md' ly' S' U' buf' ->
     SRr tfibsegs W' (cfg_at tfibsegs WVC_R_IND regs' mem' md') Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros i ke key Pd Rest ly S U W ms mdc buf Q HIND HWP HINV K.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HWF : WVC_F = 176) by reflexivity.
pose proof (wvc_stk (wf_m F)) as (HSTKF & _ & HSTKi & _).
pose proof wvc_d1c as Hd1.
unfold wvc_inv in HINV. cbv zeta in HINV.
destruct HINV as (HAT & HSEM & R8 & R9 & R19 & R21 & R25 & R3 & R4 & R18 & R20 & R22 & R23 & R24 & R26 & R27 & Hsp &
  Hi & Eke).
subst ke.
pose proof (wvc_sem_o_sp B F ly0 S0 U0 W0 mem0 regs0 ly S U W (ms_mem ms) buf _ HSEM) as Hosp.
set (E := wvc_E F regs0 (ms_regs ms) (wf_keys F + 8 * i) key).
assert (ER : forall (r : bv 5) n, Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr (ms_regs ms) r)
  by (intros r n Hn; exact (wvc_E_r F regs0 (ms_regs ms) _ key r n Hn)).
eapply (wvc_seg_comma B W ms mdc E (wf_ty F) (wf_p F) (wf_d F) (wvc_STK F) (wf_ot F) (wf_sp F) (wvc_FP F)
  ly0 S0 W0 (unpoison U0 mem0) md0 [] ly S U (wevk (wf_cap0 F) (wvc_stP F Pd)) Q HAT).
- destruct HE_ty as [(Hty & _) | (Hty & _)]; [left | right]; exact Hty.
- unfold E. rewrite wvc_E_x. reflexivity.
- exact HE_d.
- exact Hd1.
- rewrite (ER 2%bv 2%nat eq_refl). exact Hsp.
- lia.
- unfold wvc_STK. lia.
- intros ms' mdc' Ems HJ' HARU' HFR HCH R1' R10' R11' R12' R2' RK'.
  assert (Hlo : alloc_ceiling <= wf_sp F - WVC_F) by lia.
  pose proof (wvc_sem_run B F ly0 S0 U0 W0 mem0 regs0 ly S U W (ms_mem ms) (ms_mem ms') mdc' buf _ HSEM HARU' HFR Hlo
    ltac:(lia) ltac:(lia)) as HSEM'.
  assert (Hsp' : spZ (ms_regs ms') = wf_sp F - WVC_F) by (unfold spZ; rewrite R2'; exact Hsp).
  assert (Hret : YK0s.ret_ok (YK11.getr (ms_regs ms') 1%bv)).
  { rewrite R1'. apply ret_ok_even. unfold w64. rewrite unsigned_lit_small by (unfold WVC_R_IND; lia). reflexivity. }
  assert (Hra4 : 4096 <= raZ (ms_regs ms')).
  { unfold raZ. rewrite R1'. unfold w64. rewrite unsigned_lit_small by (unfold WVC_R_IND; lia).
    unfold WVC_R_IND. lia. }
  assert (G3 : YK11.getr (ms_regs ms') 3%bv = YK11.getr regs0 3%bv) by (rewrite RK' by wvc_inq; exact R3).
  assert (G4 : YK11.getr (ms_regs ms') 4%bv = YK11.getr regs0 4%bv) by (rewrite RK' by wvc_inq; exact R4).
  assert (G8 : YK11.getr (ms_regs ms') 8%bv = w64 (wf_o F)) by (rewrite RK' by wvc_inq; exact R8).
  assert (G9 : YK11.getr (ms_regs ms') 9%bv = w64 (wf_v F)) by (rewrite RK' by wvc_inq; exact R9).
  assert (G19 : YK11.getr (ms_regs ms') 19%bv = w64 (wf_p F)) by (rewrite RK' by wvc_inq; exact R19).
  assert (G21 : YK11.getr (ms_regs ms') 21%bv = w64 i) by (rewrite RK' by wvc_inq; exact R21).
  assert (G25 : YK11.getr (ms_regs ms') 25%bv = w64 (56 * i)) by (rewrite RK' by wvc_inq; exact R25).
  assert (G22 : YK11.getr (ms_regs ms') 22%bv = w64 (8 * i)) by (rewrite RK' by wvc_inq; exact R22).
  assert (G18 : YK11.getr (ms_regs ms') 18%bv = w64 ((wf_v F + 40) / 8 + SHADOW_OFF))
    by (rewrite RK' by wvc_inq; exact R18).
  assert (G20 : YK11.getr (ms_regs ms') 20%bv = w64 (wf_v F + 40)) by (rewrite RK' by wvc_inq; exact R20).
  assert (G23 : YK11.getr (ms_regs ms') 23%bv = w64 (wf_v F + 24)) by (rewrite RK' by wvc_inq; exact R23).
  assert (G24 : YK11.getr (ms_regs ms') 24%bv = w64 (wf_d F + 1)) by (rewrite RK' by wvc_inq; exact R24).
  assert (G26 : YK11.getr (ms_regs ms') 26%bv = w64 ((wf_v F + 24) / 8 + SHADOW_OFF))
    by (rewrite RK' by wvc_inq; exact R26).
  assert (G27 : YK11.getr (ms_regs ms') 27%bv = w64 (wf_v F / 8 + SHADOW_OFF)) by (rewrite RK' by wvc_inq; exact R27).
  assert (G10 : YK11.getr (ms_regs ms') 10%bv = w64 (wf_o F)) by (rewrite R10', (ER 8%bv 8%nat eq_refl); exact R8).
  assert (G11 : YK11.getr (ms_regs ms') 11%bv = w64 (wf_p F)) by (rewrite R11', (ER 19%bv 19%nat eq_refl); exact R19).
  apply (wvc_ind_call Pd Rest (wf_d F + 1) ly S U W ms' mdc' buf (ms_regs ms) (wf_keys F + 8 * i) key Q HIND HWP
    Ems HJ' HARU' HSEM' HCH Hsp' Hret Hra4 G3 G4 G8 G10 G11 R12' ltac:(lia)).
  intros peak ly' S' U' W' regs' mem' md' buf' Hpk HJc OK' PO' HP HUS' HOUT2 HBK' HBS' HWK' HGL2.
  destruct (wvc_ret_inv B HSS F ly0 S0 U0 W0 mem0 md0 regs0 HE_sp16 HE_oot HE_top HE_top47 HE_lo HE_cap0 HE_cnt0
    HE_p HE_d HE_dd HE_bud HE_ty HE_hdr HE_n HE_kk WVC_R_IND i Pd _ Rest ly S U W (ms_mem ms') mdc' buf (ms_regs ms')
    (ms_regs ms) (wf_keys F + 8 * i) key STK_indent peak ly' S' U' W' regs' mem' md' buf'
    HWP HJ' HARU' HSEM' Hpk HCH R9 Hsp' G8 G9 G19 G21 G25 G22 G3 G4 G18 G20 G23 G24 G26 G27 Hi HJc OK' PO' HP
    ltac:(vm_compute; discriminate) HSTKi HUS' HOUT2 HBK' HBS' HWK' HGL2) as (key' & HINV').
  rewrite R1'. exact (K ly' S' U' W' regs' mem' md' buf' key' HINV').
Qed.

(* ================= (2) the last item's write_value returned: the closing indent, to WVC_R_CLOSE ================= *)
Lemma wvc_item_close : forall i ke key Pd Rest ly S U (W : world tfibsegs) ms mdc buf
    (Q : world tfibsegs -> config -> Prop),
  indent_spec B tfibsegs ->
  wvc_WP F = Pd ++ WriterValue.wind (negb (wf_p F =? 0)) (wf_d F) ++ Rest ->
  wvc_inv B F WVC_R_ITEM i ke key Pd ly0 S0 U0 W0 mem0 md0 regs0 W ms mdc ly S U buf ->
  i + 1 = wf_n F ->
  (forall ly' S' U' (W' : world tfibsegs) regs' mem' md' buf',
     wvc_invC B F (Pd ++ WriterValue.wind (negb (wf_p F =? 0)) (wf_d F)) ly0 S0 U0 W0 mem0 md0 regs0
       W' (mkst regs' (Z_to_bv 64 WVC_R_CLOSE) mem' (seg_rom tfibsegs)) md' ly' S' U' buf' ->
     SRr tfibsegs W' (cfg_at tfibsegs WVC_R_CLOSE regs' mem' md') Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros i ke key Pd Rest ly S U W ms mdc buf Q HIND HWP HINV Hlast K.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HWF : WVC_F = 176) by reflexivity.
pose proof (wvc_stk (wf_m F)) as (HSTKF & _ & HSTKi & _).
pose proof wvc_d1c as Hd1.
unfold wvc_inv in HINV. cbv zeta in HINV.
destruct HINV as (HAT & HSEM & R8 & R9 & R19 & R21 & R25 & R3 & R4 & R18 & R20 & R22 & R23 & R24 & R26 & R27 & Hsp &
  Hi & Eke).
subst ke.
pose proof (wvc_sem_o_sp B F ly0 S0 U0 W0 mem0 regs0 ly S U W (ms_mem ms) buf _ HSEM) as Hosp.
set (E := wvc_E F regs0 (ms_regs ms) (wf_keys F + 8 * i) key).
assert (ER : forall (r : bv 5) n, Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr (ms_regs ms) r)
  by (intros r n Hn; exact (wvc_E_r F regs0 (ms_regs ms) _ key r n Hn)).
eapply (wvc_seg_item_last B W ms mdc E (wf_ty F) (wf_p F) i (wf_n F) (wf_d F) (wf_keys F) (wvc_STK F) (wf_ot F)
  (wf_sp F) (wvc_FP F) ly0 S0 W0 (unpoison U0 mem0) md0 [] ly S U (wevk (wf_cap0 F) (wvc_stP F Pd)) Q HAT).
- destruct HE_ty as [(Hty & _) | (Hty & _)]; [left | right]; exact Hty.
- rewrite (ER 21%bv 21%nat eq_refl). exact R21.
- rewrite (ER 25%bv 25%nat eq_refl). exact R25.
- unfold E. rewrite wvc_E_x. reflexivity.
- unfold E. rewrite wvc_E_x. reflexivity.
- unfold E. rewrite wvc_E_x. reflexivity.
- unfold E. rewrite wvc_E_x. reflexivity.
- lia.
- exact Hlast.
- lia.
- lia.
- lia.
- exact HE_d.
- lia.
- rewrite (ER 2%bv 2%nat eq_refl). exact Hsp.
- lia.
- unfold wvc_STK. lia.
- intros ms' mdc' Ems HJ' HARU' HFR HCH R1' R10' R11' R12' R21' R22' R25' R2' RK'.
  assert (Hlo : alloc_ceiling <= wf_sp F - WVC_F) by lia.
  pose proof (wvc_sem_run B F ly0 S0 U0 W0 mem0 regs0 ly S U W (ms_mem ms) (ms_mem ms') mdc' buf _ HSEM HARU' HFR Hlo
    ltac:(lia) ltac:(lia)) as HSEM'.
  assert (Hsp' : spZ (ms_regs ms') = wf_sp F - WVC_F) by (unfold spZ; rewrite R2'; exact Hsp).
  assert (Hret : YK0s.ret_ok (YK11.getr (ms_regs ms') 1%bv)).
  { rewrite R1'. apply ret_ok_even. unfold w64. rewrite unsigned_lit_small by (unfold WVC_R_CLOSE; lia).
    reflexivity. }
  assert (Hra4 : 4096 <= raZ (ms_regs ms')).
  { unfold raZ. rewrite R1'. unfold w64. rewrite unsigned_lit_small by (unfold WVC_R_CLOSE; lia).
    unfold WVC_R_CLOSE. lia. }
  assert (G3 : YK11.getr (ms_regs ms') 3%bv = YK11.getr regs0 3%bv) by (rewrite RK' by wvc_inq; exact R3).
  assert (G4 : YK11.getr (ms_regs ms') 4%bv = YK11.getr regs0 4%bv) by (rewrite RK' by wvc_inq; exact R4).
  assert (G8 : YK11.getr (ms_regs ms') 8%bv = w64 (wf_o F)) by (rewrite RK' by wvc_inq; exact R8).
  assert (G9 : YK11.getr (ms_regs ms') 9%bv = w64 (wf_v F)) by (rewrite RK' by wvc_inq; exact R9).
  assert (G19 : YK11.getr (ms_regs ms') 19%bv = w64 (wf_p F)) by (rewrite RK' by wvc_inq; exact R19).
  assert (G21 : YK11.getr (ms_regs ms') 21%bv = w64 (wf_n F)) by (rewrite R21', Hlast; reflexivity).
  assert (G25 : YK11.getr (ms_regs ms') 25%bv = w64 (56 * wf_n F)) by (rewrite R25', Hlast; reflexivity).
  assert (G22 : YK11.getr (ms_regs ms') 22%bv = w64 (8 * wf_n F)) by (rewrite R22', Hlast; reflexivity).
  assert (G18 : YK11.getr (ms_regs ms') 18%bv = w64 ((wf_v F + 40) / 8 + SHADOW_OFF))
    by (rewrite RK' by wvc_inq; exact R18).
  assert (G20 : YK11.getr (ms_regs ms') 20%bv = w64 (wf_v F + 40)) by (rewrite RK' by wvc_inq; exact R20).
  assert (G23 : YK11.getr (ms_regs ms') 23%bv = w64 (wf_v F + 24)) by (rewrite RK' by wvc_inq; exact R23).
  assert (G24 : YK11.getr (ms_regs ms') 24%bv = w64 (wf_d F + 1)) by (rewrite RK' by wvc_inq; exact R24).
  assert (G26 : YK11.getr (ms_regs ms') 26%bv = w64 ((wf_v F + 24) / 8 + SHADOW_OFF))
    by (rewrite RK' by wvc_inq; exact R26).
  assert (G27 : YK11.getr (ms_regs ms') 27%bv = w64 (wf_v F / 8 + SHADOW_OFF)) by (rewrite RK' by wvc_inq; exact R27).
  assert (G10 : YK11.getr (ms_regs ms') 10%bv = w64 (wf_o F)) by (rewrite R10', (ER 8%bv 8%nat eq_refl); exact R8).
  assert (G11 : YK11.getr (ms_regs ms') 11%bv = w64 (wf_p F)) by (rewrite R11', (ER 19%bv 19%nat eq_refl); exact R19).
  apply (wvc_ind_call Pd Rest (wf_d F) ly S U W ms' mdc' buf (ms_regs ms) (wf_keys F + 8 * i) key Q HIND HWP
    Ems HJ' HARU' HSEM' HCH Hsp' Hret Hra4 G3 G4 G8 G10 G11 R12' ltac:(lia)).
  intros peak ly' S' U' W' regs' mem' md' buf' Hpk HJc OK' PO' HP HUS' HOUT2 HBK' HBS' HWK' HGL2.
  pose proof (wvc_ret_invC Pd _ Rest ly S U W (ms_mem ms') mdc' buf (ms_regs ms') (ms_regs ms) (wf_keys F + 8 * i) key
    STK_indent peak ly' S' U' W' regs' mem' md' buf' HWP HJ' HARU' HSEM' Hpk HCH R9 Hsp' G8 G9 G19 G21 G25 G22 G3 G4
    G18 G20 G23 G24 G26 G27 ltac:(lia) HJc OK' PO' HP ltac:(vm_compute; discriminate) HSTKi HUS' HOUT2 HBK' HBS' HWK'
    HGL2) as HINV'.
  rewrite R1'. exact (K ly' S' U' W' regs' mem' md' buf' HINV').
Qed.

End A.
