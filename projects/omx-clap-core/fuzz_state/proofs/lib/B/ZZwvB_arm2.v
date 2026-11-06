(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v; 1536 of its 1692 lines of code are new or changed and 1217 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_write_value.v, with its module paths and module names changed; 518 of its 589 lines of code are new or changed and 1621 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/ZZwv_cent.v, with its module paths, module names and numbers changed; 256 of its 331 lines of code are new or changed and 514 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the CLOSING-INDENT call step of the lib/B (fs.asan-ubsan) container arms of
   write_value (split out of ZZwvB_arm.v, whose Section header it repeats): the indent after the last item (jal at
   0x842c0, depth d), from the facts the engine run of ZZwvB_runs2 left at the call to the CLOSE invariant
   ZZwvB_arm.wvc_invN at its return address WVC_R_CLOSE = 0x842c4, through ZZwvB_arm.wvc_call_facts (the callee's
   fpreU and the one-node frame chain at s0 = o, by ZZwvB_call3.wvc_callpre) and wvc_room_mid / wvc_bud_mid, the
   indent contract (FSH_Fn_writer.indent_spec), ZZwvB_call3.wvc_sem_call (the writer facts across the call) and
   wvc_ret_invN below (the return). The close state is ZZwvB_defs.wvc_ssN: the
   node alone, no key-slot region (after the last item the key cursor keys + 8 n may lie past the keys block), so the
   return is ZZwvB_step.wvc_ret_inv's twin at i' = n, with ZZwvB_res.wvc_resume_rs0 / wvc_ssN_ret in place of
   wvc_resume_rs / wvc_ssL_ret.
   Image A has no twin of this file: its container arms are unproved (wv_arr / wv_obj are hypotheses of
   lib/A/FSW_write_value.v); the pieces it does have are mirrored in ZZwvB_*.v with A's names.
   rule 24: proves no function (kind: segment lemma) - one call step of the container arms of write_value B.
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

(* the close state's regions are well formed (the frame chunks with the prelude's slots, and the node) *)
Lemma wvc_rsN_wf : forall ty p, regions_wf (fsT_ret_regions WVC_F (wvc_csL p) [wvc_node ty]) = true.
Proof. intros ty p. vm_compute. reflexivity. Qed.

Section A. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HSS : FsShadowSyms B.
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis HPUT : put_spec B tfibsegs.
Hypothesis HPS : put_string_spec B tfibsegs.
Hypothesis HIND : indent_spec B tfibsegs.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Section St.
(* the arm instance: its fixed data and the entry state, as ZZwvB_step's Section (the hypotheses are that file's,
   word for word) *)
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

(* ================= the return of the closing indent: the close invariant at WVC_R_CLOSE ================= *)
(* ZZwvB_step.wvc_ret_inv's twin at i' = n: the close state wvc_ssN holds the node alone (wvc_resume_rs0, wvc_gf0,
   wvc_SH0) and the loop registers of wvc_Lregs with the key cursor s9 = keys + 8 n - keys (xatom 18 = keys + 8 n), so
   no key slot is read and no key exists; the loop's s5 / s7 are not part of the close invariant, and 0 < n is the
   close state's n <> 0 condition *)
Lemma wvc_ret_invN : forall Pd Pc Rest ly S U (W : world tfibsegs) memC mdC buf regsC R0 ke key
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
  YK11.getr regsC 19%bv = w64 (wf_p F) -> YK11.getr regsC 25%bv = w64 (8 * wf_n F) ->
  YK11.getr regsC 3%bv = YK11.getr regs0 3%bv -> YK11.getr regsC 4%bv = YK11.getr regs0 4%bv ->
  YK11.getr regsC 18%bv = w64 (wf_v F + 40) ->
  YK11.getr regsC 20%bv = w64 ((wf_v F + 24) / 8 + SHADOW_OFF) ->
  YK11.getr regsC 22%bv = w64 (wf_d F + 1) ->
  YK11.getr regsC 24%bv = w64 (wf_v F + 24) ->
  YK11.getr regsC 26%bv = w64 0 ->
  YK11.getr regsC 27%bv = w64 ((wf_v F + 40) / 8 + SHADOW_OFF) ->
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
  wvc_invN B F ly0 S0 U0 W0 mem0 md0 regs0 (Pd ++ Pc)
    W' (mkst regs' (Z_to_bv 64 WVC_R_CLOSE) mem' (seg_rom tfibsegs)) md' ly' S' U' buf'.
Proof.
intros Pd Pc Rest ly S U W memC mdC buf regsC R0 ke key STKc peak ly' S' U' W' regs' mem' md' buf'
  HWP HJ HARU HSEM Hpk HCH HR09 Hsp R8 R9 R19 R25 R3 R4 R18 R20 R22 R24 R26 R27 Hn
  HJc OK' PO' HP HSTK0 HSTKc HUS' HOUT' HBK' HBS' HWK' HGL'.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HWF : WVC_F = 192) by reflexivity.
pose proof (wvc_stk (wf_m F)) as (HSTKF & _).
pose proof (wvc_sem_o_sp B F ly0 S0 U0 W0 mem0 regs0 ly S U W memC buf _ HSEM) as Hosp.
pose proof (proj1 HARU) as HAR.
pose proof (wvc_v_low B F ly0 S0 U0 W0 mem0 regs0 ly S U W (unpoison U memC) mdC memC buf _ HAR HSEM) as (Hv1 & Hv2).
assert (Hlo' : alloc_ceiling <= wf_sp F - WVC_F) by lia.
pose proof (wvc_d1 F S0 HE_p HE_dd HE_ty HE_n) as Hd1.
(* the keys field: an array's is 0; an object's block holds n keys (the arm is past n <> 0) *)
destruct (HE_kk Hn) as (_ & _ & Hky).
assert (Hkeys : 0 <= wf_keys F /\ wf_keys F + 8 * wf_n F <= alloc_ceiling).
{ destruct HE_ty as [(_ & _ & _ & _ & Hk0) | (Hty & _)]; [rewrite Hk0; lia|].
  destruct (Hky Hty). lia. }
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
pose proof HSEM as (_ & _ & _ & _ & HBS & _ & _ & _ & _ & _ & _ & _ & _ & _ & HBIN & _).
pose proof HSEM' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HPO' & _).
destruct (wvc_hdr_at B F ly0 S0 U0 W0 mem0 regs0 HE_hdr ly' S' U' W' mem' buf' _ HSEM') as (num & capn & HHDR').
(* the journal's footprint at the call *)
pose proof (wv_fp_sub_swap B ly0 S0 ly S W (unpoison U memC) mdC (wf_buf0 F) (wf_cap0 F) buf (WriterApp.w_cap st)
  HAR HBS HBIN ltac:(lia) wvc_pstat_img) as HFPSUB.
assert (Hrs : forall q : bv 5, acallee_saved (bv_unsigned q) -> getr regs' q = getr regsC q)
  by (intros q Hq; exact (fsw_pres regsC regs' q HP Hq)).
(* the close env: the key cursor keys + 8 n, no key *)
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
{ apply (wvc_csL_after (wvc_E F regs0 R0 ke key) E' W W' memC mem' (wf_sp F) (spZ regsC) (wf_ot F) (wf_o F)
    (wf_p F) HCH HWK'); [lia | lia | lia | | |].
  - rewrite E9', (wvc_E_r F regs0 R0 ke key 9%bv 9 eq_refl). symmetry. exact HR09.
  - rewrite E32'. unfold wvc_E. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity.
  - intros j Hj. rewrite EX, wvc_E_x.
    do 18 (destruct j as [|j]; [cbn [nth wvc_xs app map]; reflexivity|]). exfalso. lia. }
(* the node alone: its region, the regions apart, its atom fact and its shadow entry *)
destruct (wvc_resume_rs0 B ly' S' U' W' mem' md' E' (wf_ty F) (wvc_csL (wf_p F)) (wf_v F) num (wf_str F)
  (wf_kids F) (wf_keys F) (wf_n F) capn (wf_sp F) HARU' HPO' HHDR' E2' Hlo' ltac:(lia) E9' E32'
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
  ltac:(lia) ltac:(lia) ltac:(lia) (wvc_rsN_wf (wf_ty F) (wf_p F))
  HCH' HRS HPD HGF) as (HJ' & HARU'' & HST).
(* the close state *)
assert (HSN : st_ok tfibsegs E' (wvc_ssN (wf_ty F) (wf_p F))
  (restrict (w_H W') (mkst regs' (Z_to_bv 64 WVC_R_CLOSE) mem' (seg_rom tfibsegs)))).
{ apply (wvc_ssN_ret E' (wf_ty F) (wf_p F) _ (wf_n F) HST).
  - cbn [ms_regs restrict mkst]; rewrite (Hrs 18%bv ltac:(apply (wvc_cs_z _ 18); [reflexivity | lia])), R18,
      (wvc_den_val E' (SOff 9 40) _ (wvc_u_off E' 9 (wf_v F) 40 E9' ltac:(lia) ltac:(lia))).
    reflexivity.
  - cbn [ms_regs restrict mkst]; rewrite (Hrs 20%bv ltac:(apply (wvc_cs_z _ 20); [reflexivity | lia])), R20,
      (wvc_den_val E' (wvc_shv 9 24) _ (wvc_shv_U E' 24 (wf_v F) E9' E32' ltac:(lia) ltac:(lia) ltac:(lia))).
    reflexivity.
  - cbn [ms_regs restrict mkst]; rewrite (Hrs 22%bv ltac:(apply (wvc_cs_z _ 22); [reflexivity | lia])), R22,
      (wvc_den_val E' _ _ (wvc_d1_U E' (wf_d F) ltac:(rewrite EX; reflexivity) HE_d Hd1)).
    reflexivity.
  - cbn [ms_regs restrict mkst]; rewrite (Hrs 24%bv ltac:(apply (wvc_cs_z _ 24); [reflexivity | lia])), R24,
      (wvc_den_val E' (SOff 9 24) _ (wvc_u_off E' 9 (wf_v F) 24 E9' ltac:(lia) ltac:(lia))).
    reflexivity.
  - cbn [ms_regs restrict mkst]; rewrite (Hrs 25%bv ltac:(apply (wvc_cs_z _ 25); [reflexivity | lia])), R25,
      (wvc_den_val E' _ _ (wvc_sub_U E' (wf_keys F + 8 * wf_n F) (wf_keys F) ltac:(rewrite EX; reflexivity)
         ltac:(rewrite EX; reflexivity) ltac:(lia) ltac:(lia))).
    unfold w64. f_equal. lia.
  - cbn [ms_regs restrict mkst]; rewrite (Hrs 26%bv ltac:(apply (wvc_cs_z _ 26); [reflexivity | lia])), R26,
      (wvc_den_val E' (SLit 0) 0 ltac:(rewrite U_SLit; reflexivity)).
    reflexivity.
  - cbn [ms_regs restrict mkst]; rewrite (Hrs 27%bv ltac:(apply (wvc_cs_z _ 27); [reflexivity | lia])), R27,
      (wvc_den_val E' (wvc_shv 9 40) _ (wvc_shv_U E' 40 (wf_v F) E9' E32' ltac:(lia) ltac:(lia) ltac:(lia))).
    reflexivity.
  - exact E19'.
  - lia.
  - rewrite EX. reflexivity.
  - lia. }
unfold wvc_invN. cbv zeta. fold E'.
split.
{ split; [exact HSN|]. split; [exact HSH|].
  split.
  - assert (ESP : wevk (wf_cap0 F) (WriterApp.putN (wvc_st0 F) (Pd ++ Pc))
       = wevk (wf_cap0 F) st
         + wevk (WriterApp.w_cap st) (WriterApp.putN (wv_rst st) Pc))
      by exact (wv_wevk_split (wvc_st0 F) Pd Pc eq_refl HE_cap0).
    unfold wvc_stP. rewrite ESP. exact HJ'.
  - exact HARU''. }
split.
{ unfold wvc_stP. rewrite WriterApp.putN_app. cbn [ms_mem mkst]. exact HSEM'. }
assert (Hval : forall (q : bv 5) z, acallee_saved (bv_unsigned q) -> getr regsC q = w64 z ->
  YK11.getr (ms_regs (mkst regs' (Z_to_bv 64 WVC_R_CLOSE) mem' (seg_rom tfibsegs))) q = w64 z).
{ intros q z Hq E. cbn [ms_regs mkst]. rewrite (Hrs q Hq). exact E. }
split; [exact (Hval 8%bv _ ltac:(apply (wvc_cs_z _ 8); [reflexivity | lia]) R8)|].
split; [exact (Hval 9%bv _ ltac:(apply (wvc_cs_z _ 9); [reflexivity | lia]) R9)|].
split; [exact (Hval 19%bv _ ltac:(apply (wvc_cs_z _ 19); [reflexivity | lia]) R19)|].
split; [cbn [ms_regs mkst]; rewrite (Hrs 3%bv ltac:(apply (wvc_cs_z _ 3); [reflexivity | lia])); exact R3|].
split; [cbn [ms_regs mkst]; rewrite (Hrs 4%bv ltac:(apply (wvc_cs_z _ 4); [reflexivity | lia])); exact R4|].
cbn [ms_regs mkst]. unfold spZ. rewrite (Hrs 2%bv ltac:(apply (wvc_cs_z _ 2); [reflexivity | lia])). exact Hsp.
Qed.

(* ---- the CLOSING indent (after the last item, at depth d): its return point is WVC_R_CLOSE, whose state is the
   close state wvc_ssN (the node alone: after the last item the key cursor keys + 8 n may lie past the keys block),
   so this one returns wvc_invN, not wvc_inv, and its register premises hold at i = wf_n F ---- *)
Lemma wvc_call_indent_close : forall Pd Pc Rest ly S U (W : world tfibsegs) regsC memC mdC buf
    (Q : world tfibsegs -> config -> Prop),
  wvc_WP F = Pd ++ Pc ++ Rest -> Pc = WriterValue.wind (wvc_pp F) (wf_d F) ->
  ajournal tfibsegs B (wvc_STK F) (wf_ot F) (wvc_FP F) ly0 S0 W0 (unpoison U0 mem0) md0 []
    ly S W (unpoison U memC) mdC (wevk (wf_cap0 F) (wvc_stP F Pd)) ->
  ARU tfibsegs B ly S U W memC mdC ->
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly S U W memC buf (wvc_stP F Pd) ->
  Forall (YP09.chunk_ok tfibsegs (wvc_E F regs0 regsC (wf_keys F + 8 * wf_n F) 0) (rdW W memC)
    (wf_sp F - WVC_F)) (wvc_csL (wf_p F)) ->
  spZ regsC = wf_sp F - WVC_F ->
  YK11.getr regsC 1%bv = w64 WVC_R_CLOSE ->
  YK11.getr regsC 10%bv = w64 (wf_o F) -> YK11.getr regsC 11%bv = w64 (wf_p F) ->
  YK11.getr regsC 12%bv = w64 (wf_d F) ->
  YK11.getr regsC 8%bv = w64 (wf_o F) -> YK11.getr regsC 9%bv = w64 (wf_v F) ->
  YK11.getr regsC 19%bv = w64 (wf_p F) -> YK11.getr regsC 21%bv = w64 (wf_n F) ->
  YK11.getr regsC 23%bv = w64 (56 * wf_n F) -> YK11.getr regsC 25%bv = w64 (8 * wf_n F) ->
  YK11.getr regsC 18%bv = w64 (wf_v F + 40) ->
  YK11.getr regsC 20%bv = w64 ((wf_v F + 24) / 8 + SHADOW_OFF) ->
  YK11.getr regsC 22%bv = w64 (wf_d F + 1) -> YK11.getr regsC 24%bv = w64 (wf_v F + 24) ->
  YK11.getr regsC 26%bv = w64 0 ->
  YK11.getr regsC 27%bv = w64 ((wf_v F + 40) / 8 + SHADOW_OFF) ->
  YK11.getr regsC 3%bv = YK11.getr regs0 3%bv -> YK11.getr regsC 4%bv = YK11.getr regs0 4%bv ->
  0 < wf_n F ->
  (forall W' ms2 mdc2 ly' S' U' buf', wle W W' ->
     wvc_invN B F ly0 S0 U0 W0 mem0 md0 regs0 (Pd ++ Pc) W' ms2 mdc2 ly' S' U' buf' ->
     SRr tfibsegs W' (mkCfg ms2 mdc2) Q) ->
  SRr tfibsegs W (cfg_at tfibsegs A_indent regsC memC mdC) Q.
Proof.
intros Pd Pc Rest ly S U W regsC memC mdC buf Q HWP HPc HJ HARU HSEM HCH Hsp R1 R10 R11 R12 R8 R9 R19 _ _ R25
  R18 R20 R22 R24 R26 R27 R3 R4 Hn HK.
subst Pc.
pose proof (wvc_stk (wf_m F)) as (_ & _ & HSI & _).
assert (HSI0 : 0 <= STK_indent) by (vm_compute; discriminate).
assert (Hin : In WVC_R_CLOSE WV_CONT_RAS) by (unfold WV_CONT_RAS; cbn [In]; do 6 right; left; reflexivity).
pose proof (wvc_d1 F S0 HE_p HE_dd HE_ty HE_n) as Hd1.
(* the writer facts at the call *)
pose proof HSEM as (HOUT & (peak & Hpk & HGL) & HHD & _ & _ & HBK & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & HU0).
(* the premises every loop callee shares (ZZwvB_arm.wvc_call_facts), the room and the budget of the call *)
destruct (wvc_call_facts B F ly0 S0 U0 W0 mem0 md0 regs0 HE_sp16 HE_ot16 HE_oot HE_o8 HE_top HE_top47 HE_lo HE_gp
  HE_tp HE_p HE_frl HE_ty HE_n Pd WVC_R_CLOSE regsC (wf_keys F + 8 * wf_n F) 0 ly S U W memC mdC buf STK_indent
  HJ HARU HSEM HCH Hsp R1 Hin R8 R3 R4 HSI0 HSI)
  as (ch & HPRE & HCHO & HPRES & _ & Htop & HFRL & _ & Hosp).
pose proof (wvc_room_mid F S0 HE_p HE_room HE_ty HE_n Pd (WriterValue.wind (wvc_pp F) (wf_d F)) Rest HWP) as HROOM.
pose proof (wvc_bud_mid B F ly0 S0 U0 W0 mem0 md0 regs0 HE_cap0 HE_p HE_bud HE_n Pd
  (WriterValue.wind (wvc_pp F) (wf_d F)) Rest ly S U W memC mdC buf HWP HJ HSEM) as HBUD.
(* the indent call *)
eapply SRr_bind.
{ apply (HIND ly S U W regsC memC mdC ch (wf_ot F) (wf_o F) (wf_p F) (wf_d F) buf
    (WriterApp.w_cap (wvc_stP F Pd)) (WriterApp.w_failed (wvc_stP F Pd)) (WriterApp.w_text (wvc_stP F Pd))
    (wf_live F + WriterApp.w_cap (wvc_stP F Pd) - wf_cap0 F) peak (WriterApp.w_cnt (wvc_stP F Pd))
    (WriterApp.w_fail (wvc_stP F Pd)) HPRE HHD).
  - exact HFRL.
  - exact R10.
  - exact R11.
  - exact R12.
  - exact HE_p.
  - lia.
  - exact HOUT.
  - exact HGL.
  - exact HU0.
  - rewrite Hsp. unfold WVC_F. lia.
  - exact HE_oot.
  - exact HE_ot16.
  - exact Htop.
  - exact HCHO.
  - exact HPRES.
  - exact HROOM.
  - exact (proj1 HBK).
  - lia.
  - exact HBUD. }
(* its post, to the close invariant at the return *)
cbv beta. intros W' c' Hle (st' & buf' & U' & Est & HUS' & Hpost).
unfold wpost, fpostU in Hpost.
destruct Hpost as (ly' & S' & regs' & mem' & md' & Ec' & HJc & OK' & PO' & HP & HOUT' & HBK' & HBS' & HWK' & HGL').
subst c' st'.
rewrite R1.
apply (HK W' _ md' ly' S' U' buf' Hle).
exact (wvc_ret_invN Pd (WriterValue.wind (wvc_pp F) (wf_d F)) Rest ly S U W memC mdC buf regsC regsC
  (wf_keys F + 8 * wf_n F) 0 STK_indent peak ly' S' U' W' regs' mem' md' buf' HWP HJ HARU HSEM Hpk HCH R9 Hsp
  R8 R9 R19 R25 R3 R4 R18 R20 R22 R24 R26 R27 Hn HJc OK' PO' HP HSI0 HSI HUS' HOUT' HBK' HBS' HWK' HGL').
Qed.

End St.
End A.
