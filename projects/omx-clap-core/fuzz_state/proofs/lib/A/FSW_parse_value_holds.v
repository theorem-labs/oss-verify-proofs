(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFl3.v:106-108
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:383-389, 448-454, 493-498, 501-509 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:625-631 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:208-214, 227-233 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan
   build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg10.v, with its module paths and module names changed; 2634 of its 2686 lines of code are new or changed and 608 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_parse_value.v, with its module paths and module names changed; 63 of its 98 lines of code are new or changed and 2651 lines of the source are left out. *)
(* parse_value 0x82f9c on fs.asan: parse_value_holds, the composition of the walk into FSH_Fn_reader.v
   parse_value_spec k (a Theorem Labs lane's agreed shape: the callees parse_string_spec and, for k <= 1, parse_items_spec k
   as premises; the mutual recursion with parse_items (k + 1) is closed at the reader's top, FSW_reader_top.v).
   u is a string or an object (FS_DOC_STRS (i)); FSW_parse_value_front.pv_front runs the entry to the arm entry, then
   FSW_parse_value_str.pv_strarm (byte 34) or FSW_parse_value_obj.pv_objarm (byte 123) runs the arm to the post, with
   the two frame chains at the arm memory by FSW_parse_value_str.pv_arm_chains.
   Section hypotheses (the runtime and kit laws the walk takes, each discharged at the image top):
     HGUAR / HUCELL : the use-after-return GOT slot and cell (as FSW_parse_value_front.v, owner RELOC / the kit);
     SM0 : FsRt's class-0 stack-malloc field (the integrator's narrowing rule, a Theorem Labs lane 12:0xZ);
     errno_low : api_env; ML : model_laws; SMP : stack_malloc_progressP (the runtime record and unit laws, S0);
     ASF : astack_free_law; FFL : frame_flag_lawP (the fake-frame kit, a Theorem Labs lane);
     IMG : fs_img_facts (FSH_Rt.v; FSImgFacts.fs_img_facts_TfibB for TfibB).
   *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_frame FSW_ret FSH_Fn_reader FSW_rd
FSW_parse_value_tbl FSH_Fn_entry FSH_Fn_alloc FSW_K3 FSW_parse_string FSH_parse_value FSW_parse_value_calls
FSW_parse_value_obj FSW_parse_value_front FSW_parse_value_str.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterValue PjIn PjStruct ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Prog Require FSDocStrs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSW_parse_items_mdl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved.
   YI14 is required (not imported) so that the second probe names a loaded class. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14.
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.
Fail Definition probe_SH : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI14.sink_syms := _.

Section PVH. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HGUAR : as_got_uar B = fs_D_GOT_uar.
Hypothesis HUCELL : as_uar_cell B = fs_D_uar_cell.
Hypothesis SM0 : pc_stack_malloc (as_code B) 0 = PC_stack_malloc_0 /\
  FSupoisonU.astack_malloc_realizesU tfibsegs B 0.
Hypothesis errno_low : api_env tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis ASF : astack_free_law tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.

Theorem parse_value_holds : forall k : nat, (k <= 2)%nat -> FsShadowSyms B -> @parse_string_spec fx rc SK tfibsegs B ->
  ((k <= 1)%nat -> @parse_items_spec fx rc SK tfibsegs B k) -> @parse_value_spec fx rc SK tfibsegs B k.
Proof.
intros k Hk0 HSS HPS HPI. unfold parse_value_spec.
intros ly S U W regs mem md ch q ot v text len p tb tcap u pr ws rest live peak cnt fail.
cbv zeta.
intros Hk HPRE FH HFRL H10 H11 HIN HWIN HCHS HTX HREST HWS HDV HDS HWF HDEP HPO HZO HVST HVTX HGL HQT HSZ HLIVE
  HEV HBB.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HPREU & HRO). pose proof HPREU as (HAPRE & OK0 & PO0).
pose proof HAPRE as (HAR0 & Hret & Hra4 & Hgp & Htp & Hstk & _ & HCHe & _).
assert (HARU0 : ARU tfibsegs B ly S U W mem md) by (split; [exact HAR0 | split; [exact OK0 | exact PO0]]).
pose proof (fsw_sp B _ ly S U W regs mem md ch HPREU) as (Hal16 & Hceil & H47 & HSTK0).
pose proof HWIN as (Hsq & Hq24 & Hot16 & Hotly & Hpot).
pose proof Hstk as (_ & _ & Hlo0 & Hslo & Hshi & H47' & _ & _ & Htop2).
pose proof (pv_stk k Hk) as FS4.
destruct HSS as (HGOT & HCELL).
(* u is a string or an object: FS_DOC_STRS (i) *)
pose proof (HDV u (or_introl eq_refl)) as Hsoo.
destruct u as [| | | txt bits | s | items | ms]; cbn [FSDocStrs.str_or_obj] in Hsoo; try contradiction.
- (* the string arm: in->p at the opening quote 34 *)
  assert (Hplain : plain_bytes s) by (apply HDS; left; reflexivity).
  assert (Hwt : concat (WriterValue.wvpieces (PjTree.JStr s) pr (Z.of_nat k)) = 34 :: s ++ [34]).
  { cbn [WriterValue.wvpieces]. exact (FSW_parse_items_mdl.pim_spieces_plain s Hplain). }
  assert (HR34 : ReaderRes.rest_at tb text p = ws ++ 34 :: (s ++ 34 :: rest)).
  { rewrite HREST, Hwt. cbn [app]. rewrite <- app_assoc. reflexivity. }
  apply (pv_front B HGOT HCELL HGUAR HUCELL SM0 errno_low ML SMP IMG k ly S U W regs mem md ch q ot v text len p tb tcap
    ws 34 (s ++ 34 :: rest) live peak cnt fail _ Hk HPRE FH HFRL H10 H11 HIN HWIN HTX HR34 HWS (or_introl eq_refl)
    HZO HPO HGL).
  intros ms' mdx' S2 pos Hin0 Hfrs2 Hab2 Hnev2 Hbb2 Harm R8 R9 R18 R19 R20 R23 R24 R26 R3 R4 R2 Vq0 HINV HJ HARU
    HWK HINa HTXa HPoa HZoa HGLa AGR.
  destruct Harm as [(_ & Hshape) | (E & _)]; [|discriminate E].
  destruct (pv_arm_chains B ly S S2 U W regs mem md (ms_mem ms') mdx' q (32 * ((spZ regs - 160) / 32)) ch HCHe Hra4
    ltac:(lia) ltac:(lia) ltac:(lia) Hsq ltac:(lia) ltac:(lia) HARU0 HARU HCHS AGR (proj1 HINV)) as (HC0 & HCq).
  assert (HCq' : exists chq, achain ly (aview tfibsegs (w_H W) (unpoison U (ms_mem ms')))
    (32 * ((spZ regs - 160) / 32)) q chq) by (destruct HCq as (chq & Hc & _); exists chq; exact Hc).
  exact (pv_strarm B ML ASF FFL HPS k ly S U W regs mem md ch q ot v text len p tb tcap s pr ws rest live peak cnt fail
    S2 pos ms' mdx' Hk HPRE FH HIN HWIN HREST Hplain HPO HVST HVTX HQT HSZ HLIVE HEV HBB Hin0 Hfrs2 Hab2 Hnev2 Hbb2
    Hshape R8 R9 R18 R19 R20 R23 R24 R26 R3 R4 HINV HJ HARU R2 HWK HINa HTXa HPoa HZoa HGLa HC0 HCq').
- (* the object arm: in->p at the opening brace 123 *)
  assert (Hk1 : (k <= 1)%nat) by (cbn [PjTree.depth] in HDEP; lia).
  assert (HR123 : ReaderRes.rest_at tb text p =
    ws ++ 123 :: (concat (tl (WriterValue.wvpieces (PjTree.JObj ms) pr (Z.of_nat k))) ++ rest)).
  { rewrite HREST. cbn [WriterValue.wvpieces concat tl]. reflexivity. }
  apply (pv_front B HGOT HCELL HGUAR HUCELL SM0 errno_low ML SMP IMG k ly S U W regs mem md ch q ot v text len p tb tcap
    ws 123 (concat (tl (WriterValue.wvpieces (PjTree.JObj ms) pr (Z.of_nat k))) ++ rest) live peak cnt fail _
    Hk HPRE FH HFRL H10 H11 HIN HWIN HTX HR123 HWS (or_intror eq_refl) HZO HPO HGL).
  intros ms' mdx' S2 pos Hin0 Hfrs2 Hab2 Hnev2 Hbb2 Harm R8 R9 R18 R19 R20 R23 R24 R26 R3 R4 R2 Vq0 HINV HJ HARU
    HWK HINa HTXa HPoa HZoa HGLa AGR.
  destruct Harm as [(E & _) | (_ & Hshape)]; [discriminate E|].
  destruct (pv_arm_chains B ly S S2 U W regs mem md (ms_mem ms') mdx' q (32 * ((spZ regs - 160) / 32)) ch HCHe Hra4
    ltac:(lia) ltac:(lia) ltac:(lia) Hsq ltac:(lia) ltac:(lia) HARU0 HARU HCHS AGR (proj1 HINV)) as (HC0 & HCq).
  exact (pv_objarm B ML ASF FFL k (HPI Hk1) ly S U W regs mem md ch q ot v text len p tb tcap ms pr ws rest live peak
    cnt fail S2 pos ms' mdx' Hk HPRE FH HFRL HIN HWIN HREST HDV HDS HWF HDEP HPO HVST HVTX HQT HSZ HLIVE HEV HBB
    Hin0 Hfrs2 Hab2 Hnev2 Hbb2 Hshape R8 R9 R18 R19 R20 R23 R24 R26 R3 R4 Vq0 HINV HJ HARU R2 HWK HINa HTXa HPoa
    HZoa HGLa HC0 HCq).
Qed.
End PVH.
