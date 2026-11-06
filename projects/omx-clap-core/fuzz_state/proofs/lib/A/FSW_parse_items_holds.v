(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* fs program part, READER lane (a Theorem Labs lane): parse_items (A 0x84a04) against parse_items_spec k
   (lib/A/FSH_Fn_reader.v:389-427), k = 0..1.
   ms = []      : FSW_pitems_dev.pitems_spec_nil (the empty object, a Theorem Labs lane).
   ms = m :: rm : FSW_parse_items_entry.pi_entry (the prologue, `{`, the white space, to grow #1), then pi_loop: by
                  induction over the members still to read, one member is pi_step_G (grow, the white space, to the key's
                  parse_string), pi_step_P (the key, `:`, to __asan_memset), pi_step_M (the kid zeroed, to parse_value),
                  and pi_step_Vc (`,`: v->n + 1, to the next grow) or pi_step_Ve (`}`: v->n + 1, in->depth - 1, the
                  ret, the post). The call-site invariants are FSW_parse_items_loop.v's pi_IG / pi_IP / pi_IM / pi_IV.
   Callees: grow_spec (S0 lib/A/Prog/FSW_grow_holds.v grow_holds), parse_string_spec (S0 lib/A/FSW_parse_string.v
   parse_string_proof), parse_value_spec (S k) (open: the mutual recursion is closed at the reader's top), the
   __asan_memset contract FSupoisonU.aintrin_realizesU OSet PC_memset (S0's FsRt field fr_memset; only that field is
   taken, so the top need not build the rest of FsRt); FsShadowSyms B (the two shadow-base cells; discharged at the
   reader's entry).
   Rule 24: proves function parse_items (lookup: proof-index by name, 03:15Z, exit 0, full output
   (internal path); a Theorem Labs lane's CONFIRM, no ASan donor,
   (internal path)). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.omx_clap_core.fuzz_state.images Require Import Asan.
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
AB1v AB1w FSupoison FSupoisonU FSupoisonStack FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_ret FSW_rd
FSW_pj FSH_Fn_reader
FSW_parse_items_tbl FSW_parse_items FSW_parse_items_grow FSW_parse_items_calls FSW_parse_items_kit
FSW_parse_items_seg FSW_parse_items_mem FSW_parse_items_mdl FSW_parse_items_loop
FSW_pitems_dev FSW_parse_items_entry FSW_parse_items_stG FSW_parse_items_stP FSW_parse_items_stM
FSW_parse_items_stVc FSW_parse_items_stVe.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjIn PjStruct ReaderRes WriterValue WriterSpec
  parse_items_shape.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Prog Require FSDocStrs FSW_grow_holds FSW_pj_set_heads.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (S0): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section X. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
(* ---- parse_items_spec k's entry (the same Section variables and hypotheses as FSW_parse_items_loop.v's Section M) ---- *)
Variables (k : nat) (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (q ot v text len p tcap : Z) (tb : list byte)
  (ms : list (list Z * PjTree.jv)) (pr : bool) (rest : list Z) (live peak cnt fail : Z).
Let sp0 : Z := spZ regs.
Let dd : Z := Z.of_nat k.
Let xr : list word := map (YK11.getr regs) pi_saved.
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
#[local] Abbreviation IG := (pi_IG B k ly S U W regs mem md q ot v text len tcap tb ms pr rest live peak cnt fail).
#[local] Abbreviation IP := (pi_IP B k ly S U W regs mem md q ot v text len tcap tb ms pr rest live peak cnt fail).
#[local] Abbreviation IK := (pi_IK B k ly S U W regs mem md q ot v text len tcap tb ms pr rest live peak cnt fail).
#[local] Abbreviation IM := (pi_IM B k ly S U W regs mem md q ot v text len tcap tb ms pr rest live peak cnt fail).
#[local] Abbreviation IV := (pi_IV B k ly S U W regs mem md q ot v text len tcap tb ms pr rest live peak cnt fail).
#[local] Abbreviation Q := (pi_Q B k ly S U W regs mem md q ot v text len p tcap tb ms pr live peak cnt fail).
Hypothesis HGROW : @grow_spec fx rc SK tfibsegs B.
Hypothesis HPS : @parse_string_spec fx rc SK tfibsegs B.
Hypothesis MS : FSupoisonU.aintrin_realizesU tfibsegs B OSet PC_memset.
Hypothesis HPV : @parse_value_spec fx rc SK tfibsegs B (Datatypes.S k).

(* the member loop: from any grow call site with members rm still to read, to the spec's post *)
Lemma pi_loop : forall rm dn kk x T lyc Sc Uc (W1 : world tfibsegs) memC mdC regsC chq pc kids keys cap Di Da peak1,
  IG dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 ->
  SRr tfibsegs W1 (YG0d.cfg_at tfibsegs A_grow regsC memC mdC) Q.
Proof.
induction rm as [|[kk' x'] rm' IH];
  intros dn kk x T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 HG.
- eapply pi_step_G; try eassumption.
  intros T2 lyc2 Sc2 Uc2 W2 mem2 md2 regs2 chq2 pc2 kids2 keys2 cap2 Da2 peak2 HP.
  eapply pi_step_P; try eassumption.
  intros T3 lyc3 Sc3 Uc3 W3 mem3 md3 regs3 chq3 pc3 Da3 peak3 a HM.
  eapply pi_step_M; try eassumption.
  intros mem4 md4 regs4 chq4 HV.
  eapply pi_step_Ve; eassumption.
- eapply pi_step_G; try eassumption.
  intros T2 lyc2 Sc2 Uc2 W2 mem2 md2 regs2 chq2 pc2 kids2 keys2 cap2 Da2 peak2 HP.
  eapply pi_step_P; try eassumption.
  intros T3 lyc3 Sc3 Uc3 W3 mem3 md3 regs3 chq3 pc3 Da3 peak3 a HM.
  eapply pi_step_M; try eassumption.
  intros mem4 md4 regs4 chq4 HV.
  eapply pi_step_Vc; try eassumption.
  intros T5 lyc5 Sc5 Uc5 W5 mem5 md5 regs5 chq5 pc5 Di5 Da5 peak5 HG5.
  exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HG5).
Qed.

(* ms = (kk, x) :: rm: the entry to grow #1, then the loop *)
Lemma pi_items_cons : forall kk x rm, ms = (kk, x) :: rm ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_parse_items regs mem md) Q.
Proof.
intros kk x rm Ems. eapply pi_entry; try eassumption.
intros T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 HG.
exact (pi_loop rm [] kk x T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 HG).
Qed.

End X.

(* ================= parse_items_spec k ================= *)
Theorem parse_items_holds : forall {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} (B : asyms) (k : nat),
  (k <= 1)%nat -> FsShadowSyms B -> @grow_spec fx rc SK tfibsegs B -> @parse_string_spec fx rc SK tfibsegs B ->
  @parse_value_spec fx rc SK tfibsegs B (Datatypes.S k) -> FSupoisonU.aintrin_realizesU tfibsegs B OSet PC_memset ->
  @parse_items_spec fx rc SK tfibsegs B k.
Proof.
intros fx rc SK B k Hk0 HSS HGROW HPS HPV MS.
unfold parse_items_spec.
intros ly S U W regs mem md ch q ot v text len p tb tcap ms pr rest live peak cnt fail.
cbv zeta.
intros Hk HPRE HHEADS HFRL H10 H11 H12 HIN HWIN HQ16 HCH HTX HREST HDV HDS HWF HDEP HPO HZERO HVSP HVTX HGLOB
  HQT HSZ HLIVE HEV HBB.
destruct ms as [|[kk x] rm].
- exact (pitems_spec_nil B (proj1 HSS) (proj2 HSS) k ly S U W regs mem md ch q ot v text len p tb tcap pr rest
           live peak cnt fail Hk HPRE HHEADS HFRL H10 H11 H12 HIN HWIN HQ16 HCH HTX HREST HDV HDS HWF HDEP HPO HZERO
           HVSP HVTX HGLOB HQT HSZ HLIVE HEV HBB).
- eapply pi_items_cons;
    try eassumption; reflexivity.
Qed.
