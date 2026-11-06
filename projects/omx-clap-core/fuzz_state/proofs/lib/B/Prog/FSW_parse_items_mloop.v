(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) the MEMBER INDUCTION of parse_items' loop on image B: from the
   call-site invariant at grow for member i (pib_IG dn (kk, x) rm) to parse_items_spec k's post (pib_Q), by induction on
   the members left, chaining the step lemmas
     pi_step_G  (FSW_parse_items_stG.v, pib_IG -> pib_IP: grow, skip_ws #2, segment D),
     pi_step_P  (FSW_parse_items_stP.v, pib_IP -> pib_IE: parse_string),
     HVAL       (pib_IE -> pib_IH: the segment 0x85048 .. 0x851d0, a Theorem Labs lane's FSW_parse_items_val.v piv_val in the
                 shape agreed through a Theorem Labs lane; a Section hypothesis HERE, discharged in FSW_parse_items_holds.v),
     pi_step_H1 (FSW_parse_items_stH.v, pib_IH -> pib_IW4: segment H, the member closed),
     pi_step_Ic (FSW_parse_items_stI.v, pib_IW4 -> pib_IG for the next member at `,`) and
     pi_step_Ie (FSW_parse_items_stI.v, pib_IW4 with no member left -> pib_Q at `}`).
   pi_holds_cons: the object with members, from parse_items' entry, through HINIT (pib_IG [] at the first grow call:
   a Theorem Labs lane's FSW_parse_items_init.v pi_init in the agreed shape; a Section hypothesis HERE) and pi_members.
   rule 24: proves no function (kind: composition lemmas under the Section hypotheses HVAL / HINIT). *)
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
FSupoison FSupoisonU FSupoisonStack FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSW_K FSW_K3 FSW_ret FSW_rd FSW_pj FSPstat FSH_Fn_reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjIn PjStruct ReaderRes WriterValue WriterSpec
  parse_items_shape.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Prog Require FSDocStrs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.Prog Require Import
FSW_parse_items_tbl FSW_parse_items FSW_parse_items_calls FSW_parse_items_kit FSW_parse_items_mdl FSW_parse_items_seg
FSW_parse_items_loop FSW_parse_items_mem FSW_parse_items_sw FSW_parse_items_obj FSW_parse_items_lh
FSW_parse_items_sws FSW_parse_items_grow FSW_parse_items_stG FSW_parse_items_stP FSW_parse_items_stH FSW_parse_items_stI.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14.
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section ML. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variables (k : nat) (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (q ot v text len p tcap : Z) (tb : list byte)
  (ms : list (list Z * PjTree.jv)) (pr : bool) (rest : list Z) (live peak cnt fail : Z).
Let sp0 : Z := spZ regs.
Let dd : Z := Z.of_nat k.
Let FP : list (Z * Z) := [(v, v + 56)] ++ FS_PSTAT_FP.
Let STKt : Z := STK_parse_items (1 - k) + (ot - sp0).
Let xr : list word := map (YK11.getr regs) pi_saved_regs.
#[local] Abbreviation JC := (pib_jc B k ly S U W regs mem md ot v).
#[local] Abbreviation RP := (pib_regsP B regs q v).
#[local] Abbreviation STKP := (pib_stack k ly W regs mem q ot text len tb).
#[local] Abbreviation BLK := (pib_blocks B ly S U v text len tcap live peak cnt fail).
#[local] Abbreviation OBJ := (pib_obj v).
#[local] Abbreviation IG := (pib_IG B k ly S U W regs mem md q ot v text len tcap tb ms pr rest live peak cnt fail).
#[local] Abbreviation IP := (pib_IP B k ly S U W regs mem md q ot v text len tcap tb ms pr rest live peak cnt fail).

Variable ch : list (Z * Z * Z).
Hypothesis Hk : (k <= 1)%nat.
Hypothesis HSS : FsShadowSyms B.
Hypothesis HPRE : fpreU tfibsegs B (STK_parse_items (1 - k)) ly S U W regs mem md ch.
Hypothesis HHEADS : FSupoisonU.fs_heads B ly S U.
Hypothesis HWIN : rd_win tfibsegs regs ly W mem q ot.
Hypothesis HQ16 : spZ regs + 16 <= q.
Hypothesis HTX : rd_text tfibsegs B ly S W mem text len tcap.
Hypothesis HIN0 : PjIn.pj_in_ok tfibsegs (rdW W mem) q text len p dd tb.
Hypothesis HVTX : v + 56 <= text - HEAD \/ text + tcap <= v.
Hypothesis HPO0 : pobj tfibsegs B ly S W mem v.
Hypothesis HQT : quiet cnt fail (Z.of_nat (length (PjRoundTrip.ttrace (PjTree.JObj ms)))).
Hypothesis HSZ : rd_sizes_ok (PjRoundTrip.ttrace (PjTree.JObj ms)).
Hypothesis HLIVE : live + rd_live (PjRoundTrip.ttrace (PjTree.JObj ms)) < 2 ^ 64.
Hypothesis HEV : st_nev S + rd_ev (PjRoundTrip.ttrace (PjTree.JObj ms)) <= EV_MAX.
Hypothesis HBB : blocks_bytes S + rd_live (PjRoundTrip.ttrace (PjTree.JObj ms)) <= LIVE_MAX.
Hypothesis HFRL : Z.of_nat (length (frames S)) <= FRL_parse_value (Z.of_nat k + 1).
Hypothesis H10 : YK11.getr regs 10 = w64 q.
Hypothesis H11 : YK11.getr regs 11 = w64 v.
Hypothesis H12 : YK11.getr regs 12 = w64 1.
Hypothesis HCH0 : exists chq, achain ly (aview tfibsegs (w_H W) (unpoison U mem)) (spZ regs) q chq /\
  Forall (fun r => bad_next (fst (fst r)) (ly_top ly) (snd r) = true \/ q + 40 <= snd r) chq.
Hypothesis HREST : ReaderRes.rest_at tb text p = concat (WriterValue.wvpieces (PjTree.JObj ms) pr (Z.of_nat k)) ++ rest.
Hypothesis HDV : FSDocStrs.fs_doc_values (PjTree.JObj ms).
Hypothesis HDS : FSDocStrs.fs_doc_strings (PjTree.JObj ms).
Hypothesis HWF : PjRoundTrip.pj_wf ReaderRes.jr_strtod (PjTree.JObj ms).
Hypothesis HDEP : (PjTree.depth (PjTree.JObj ms) <= 2 - k)%nat.
Hypothesis HZERO : PjStruct.pj_zero tfibsegs (rdW W mem) v.
Hypothesis HVSP : v + 56 <= spZ regs - STK_parse_items (1 - k) \/ ot <= v.
Hypothesis HGLOB : fs_glob tfibsegs W mem live peak cnt fail.
(* callees: skip_ws, grow, parse_string (a Theorem Labs lane's and another Theorem Labs lane's B walks) *)
Hypothesis HSW : @skip_ws_spec fx rc SK tfibsegs B.
Hypothesis HGROW : @grow_spec fx rc SK tfibsegs B.
Hypothesis HPS : @parse_string_spec fx rc SK tfibsegs B.
#[local] Abbreviation IE := (pib_IE B k ly S U W regs mem md q ot v text len tcap tb ms pr rest live peak cnt fail).
#[local] Abbreviation IH := (pib_IH B k ly S U W regs mem md q ot v text len tcap tb ms pr rest live peak cnt fail).
#[local] Abbreviation Q := (pib_Q B k ly S U W regs mem md q ot v text len p tcap tb ms pr live peak cnt fail).
(* the segment 0x85048 .. 0x851d0 (a Theorem Labs lane's piv_val): from the resume after parse_string to the resume after
   parse_value; the continuation keeps the member, kids, keys, cap, Di and the key block a *)
Hypothesis HVAL : forall dn kk x rm T lyc Sc Uc (W1 : world tfibsegs) memC mdC regsC chq pc kids keys cap Di Da peak1 a
    ly' S' (W' : world tfibsegs) regs' mem' md' (Qc : world tfibsegs -> config -> Prop),
  IE dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 a ly' S' W' regs' mem' md' ->
  (forall T2 lyc2 Sc2 Uc2 (W2 : world tfibsegs) mem2 md2 regs2 chq2 pc2 Da2 peak2 D Dx ly3 S3 (W3 : world tfibsegs) regs3
     mem3 md3,
     IH dn kk x rm T2 lyc2 Sc2 Uc2 W2 mem2 md2 regs2 chq2 pc2 kids keys cap Di Da2 peak2 a D Dx ly3 S3 W3 regs3 mem3 md3 ->
     SRr tfibsegs W3 (mkCfg (mkst regs3 (Z_to_bv 64 0x851d0) mem3 (seg_rom tfibsegs)) md3) Qc) ->
  SRr tfibsegs W' (mkCfg (mkst regs' (Z_to_bv 64 0x85048) mem' (seg_rom tfibsegs)) md') Qc.

(* ================= the members left, by induction ================= *)
Lemma pi_members : forall rm dn kk x T lyc Sc Uc (W1 : world tfibsegs) memC mdC regsC chq pc kids keys cap Di Da peak1,
  IG dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 ->
  SRr tfibsegs W1 (YG0d.cfg_at tfibsegs A_grow regsC memC mdC) Q.
Proof.
induction rm as [|[kk' x'] rm IHrm];
  intros dn kk x T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 HIG;
  (apply (pi_step_G B k ly S U W regs mem md q ot v text len p tcap tb ms pr rest live peak cnt fail ch Hk HSS HPRE HHEADS
     HWIN HQ16 HTX HIN0 HVTX HPO0 HQT HSZ HLIVE HEV HBB HDEP HVSP HGLOB HSW HGROW dn kk x _ T lyc Sc Uc W1 memC mdC regsC
     chq pc kids keys cap Di Da peak1 Q HIG));
  intros T1 lyc1 Sc1 Uc1 W2 mem2 md2 regs2 chq2 pc2 kids2 keys2 cap2 Da2 peak2 HIP;
  apply (pi_step_P B k ly S U W regs mem md q ot v text len p tcap tb ms pr rest live peak cnt fail ch Hk HSS HPRE HWIN
    HQ16 HTX HIN0 HVTX HPO0 HQT HSZ HLIVE HEV HBB HDV HDS HWF HDEP HVSP HPS dn kk x _ T1 lyc1 Sc1 Uc1 W2 mem2 md2 regs2
    chq2 pc2 kids2 keys2 cap2 Di Da2 peak2 Q HIP);
  intros a ly3 S3 W3 regs3 mem3 md3 HIE;
  apply (HVAL dn kk x _ T1 lyc1 Sc1 Uc1 W2 mem2 md2 regs2 chq2 pc2 kids2 keys2 cap2 Di Da2 peak2 a ly3 S3 W3 regs3 mem3 md3
    Q HIE);
  intros T4 lyc4 Sc4 Uc4 W4 mem4 md4 regs4 chq4 pc4 Da4 peak4 D Dx ly5 S5 W5 regs5 mem5 md5 HIH;
  apply (pi_step_H1 B k ly S U W regs mem md q ot v text len p tcap tb ms pr rest live peak cnt fail ch Hk HPRE HWIN HQ16
    HTX HIN0 HVTX HPO0 HDEP HVSP dn kk x _ T4 lyc4 Sc4 Uc4 W4 mem4 md4 regs4 chq4 pc4 kids2 keys2 cap2 Di Da4 peak4 a D Dx
    ly5 S5 W5 regs5 mem5 md5 Q HIH);
  intros T6 ly6 S6 U6 W6 mem6 md6 regs6 pc6 Di6 Da6 peak6 HIW.
- exact (pi_step_Ie B k ly S U W regs mem md q ot v text len p tcap tb ms pr rest live peak cnt fail ch Hk HSS HPRE HWIN
    HQ16 HTX HIN0 HVTX HPO0 HREST HDEP HVSP HSW (dn ++ [(kk, x)]) T6 ly6 S6 U6 W6 mem6 md6 regs6 chq4 pc6 kids2 keys2 cap2
    Di6 Da6 peak6 HIW).
- apply (pi_step_Ic B k ly S U W regs mem md q ot v text len p tcap tb ms pr rest live peak cnt fail ch Hk HSS HPRE HWIN
    HQ16 HTX HIN0 HVTX HPO0 HDEP HVSP HSW (dn ++ [(kk, x)]) kk' x' rm T6 ly6 S6 U6 W6 mem6 md6 regs6 chq4 pc6 kids2 keys2
    cap2 Di6 Da6 peak6 Q HIW).
  intros T7 ly7 S7 U7 W7 mem7 md7 regs7 chq7 pc7 Di7 Da7 peak7 HIG7.
  exact (IHrm (dn ++ [(kk, x)]) kk' x' T7 ly7 S7 U7 W7 mem7 md7 regs7 chq7 pc7 kids2 keys2 cap2 Di7 Da7 peak7 HIG7).
Qed.
(* ================= the object with members: from the entry (pi_init's shape) to the post ================= *)
(* stage A, skip_ws #1 and stage B's member arm, from parse_items' entry to the first grow call with the invariant
   pib_IG [] (a Theorem Labs lane's FSW_parse_items_init.v pi_init in the shape agreed through a Theorem Labs lane (13:4xZ); a Section
   hypothesis HERE, discharged in FSW_parse_items_holds.v) *)
Hypothesis HINIT : forall kk x rm (Qc : world tfibsegs -> config -> Prop), ms = (kk, x) :: rm ->
  (forall T lyc Sc Uc (W1 : world tfibsegs) memC mdC regsC chq pc kids keys cap Di Da peak1,
     IG [] kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 ->
     SRr tfibsegs W1 (YG0d.cfg_at tfibsegs A_grow regsC memC mdC) Qc) ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_parse_items regs mem md) Qc.
Lemma pi_holds_cons : forall kk x rm, ms = (kk, x) :: rm ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_parse_items regs mem md) Q.
Proof.
intros kk x rm E. apply (HINIT kk x rm Q E).
intros T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 HIG.
exact (pi_members rm [] kk x T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 HIG).
Qed.
End ML.
