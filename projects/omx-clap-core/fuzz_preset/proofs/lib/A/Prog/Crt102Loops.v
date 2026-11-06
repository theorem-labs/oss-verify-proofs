(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumA.v, with its module paths and module names changed; 4902 of its 4996 lines of code are new or changed and 684 lines of the source are left out. *)
(* On the Step-1 contract texts (the re-hiding move): every journal of this slice is at
   R := YA0nH.wle' SEGS YGcfRehidePost.RZ_cf (the wle' contract, Crt102Glue / Crt102Kit), every stretch statement
   concludes YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf. The calls: same's text is plain (Crt102Kit.crt102rw_lift_x),
   fuzz_free's (fpostbm) and pj_free's (fpostWmR) are at wle'; strcmp's rule over R is the engine's
   YGcallMxmn.aj_strcmp_at_xromR.
   The two free calls' hull budgets are paid from the run position under HOS4 (Crt102HullPos / PresetHullPay). *)
(* base: commit 2fdcfd7be069 (post-landing line). kb round (brief
   the internal file wild-budget-kb-reshape.md): every state of this slice carries crt_live at
   kb = prh_wk F_check_round_trip (the notation livea) and its journal at a budget WS with wbudget [] (prh_wk
   F_check_round_trip) WS; the runs keep WS (Crt102Kit's AJW runners), strcmp keeps it (rebase / unbase around its
   empty-budget rule), and the calls through the kit (same, fuzz_free, pj_free) hand it on packaged. *)
(* fuzz_preset, image A' (asan pin 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4): the TAIL of
   the inlined round_trip_rewrite in check_round_trip (fuzz_preset.c new:740-768), cuts L0 (+0x470) -> L1 (+0x4e0) ->
   L2 (+0x528) -> L3 (+0x590) -> C (+0x634) and the exit (+0x6cc .. +0x6dc),
   closing ARM C4-full into crt_at_X (+0x304).

   THE RESULT. crt102_loops (Qed): from every crt_at_L0 state, SRr' .. (crt_cfg fxk CRT_L0_OFF rg memc mdc) QF, given the
   X seam KX (from every crt_at_X state, QF: Crt102Top.v's crt102_top_X, by Crt102Kit.crt102rw_at_X of the J seam).

   INPUTS OF RECORD (taken by path):
   - base commit 6bb495fd9c56 (the glue Records, every walk file re-pointed; lib/A/Prog/Crt102Glue.v,
     Crt102Kit.v, Crt102Model.v, Crt102Img.v, S10Env.v, S1Ledger.v
     consumed unchanged).
   - the contract texts at the base: PRH_FnCheck.v (tcheck_round_trip_specX's premises), PRH_FnEx.v (tsame_specX),
     PRH_FnAlloc.v (tfuzz_free_specX), PRH_FnPj.v (tpj_free_specX), PRH_Base.v, PRH_Reader.v, PRH_PjOrder.v.
   - cut table: DESIGN.md (sha256 d05697dd088c; internal record); listing, the internal file crt.A.s (A').
   - source: src-102/new/fuzz_preset.c (sha256 c7b4007bba7bab3e), new:740-768.
   - build route pins102: the internal file zfb-targets.dc6f8f60073340be.sh, FACTS 8f3e7e1a07f1,
     PAU pau-preset-102.
   - rule 24: no function proved (proof-index check_round_trip, exit 0,
     an internal record of that lookup): only plain and ubsan proofs, concluding in SR. Written new.

   THE L0 BOUNDARY (the glue's crt_at_L0) was agreed with Crt102Rewrite.v (2026-10-29): it FORWARDS the two
   callee outcomes as pj_write's and parse_noting's posts give them, and this file does the deduction that kills the
   property abort of new:740 (cl_L0_saved).

   THE TWO LOOPS, each closed by the MEASURE length ms - i (S10TxString.v's ts_loop pattern; the continuation is owed only
   below a bound mb, and the closure is an induction on mb):
   - the at-search (new:742-744), cl_L1_loop: at L1 iteration i, s6 = i < n = length ms and the invariant
     cm_at_inv ms i a2 (Crt102Model.v): a2 = n while no key below i is MOD_AT, else a2 = cm_at ms, the first match.
   - the member loop (new:750-755), cl_L3_loop: at L3 iteration i < n, the counter s6 = n - i counts down, the keys
     compared so far are equal and every member other than `at` is the same tree (cm_set_member).

   PROPERTY ABORTS SHOWN UNREACHABLE (all branch to +0x6f8, __asan_handle_no_return; abort):
   - new:740 `!saved || rc != 0` (L0's `bnez s6`): cl_L0_saved, under the request bound RQA_crt t <= most.
   - new:748 `back.n != doc->n + (at == doc->n)` (L2's `bne a1, a0`): cl_L2, back holds the rewritten tree
     (cm_set_len: its member count is n + (at == n)).
   - new:754 `strcmp (back.keys[i], doc->keys[i]) != 0` (L3r's `bnez a0`): cl_L3_head, cm_set_member keeps every key.
   - new:754 `i != at && !same (..)` (`beqz a0` after +0x5f0): cl_L3r, the two kids are one tree (cm_set_member).
   - new:759 first half `strcmp (back.keys[at], MOD_AT) != 0` (`bnez a0` at +0x66c): cl_C_head, cm_set_at.
   - new:759 second half `back.kids[at].type != PJ_STRING` (`bne a1, a2` at +0x680): cl_C1r, cm_set_at (JStr STAMP).
   - new:764 `strcmp (back.kids[at].str, STAMP) != 0` (`bnez a0` at +0x6c8): cl_C2r, cm_set_at.

   NUMERALS. LENGTH: 56 (struct pj), 8 (a key slot), 24 / 32 / 40 / 16 (kids / keys / n / str inside struct pj),
   0x20 / 0x80 / 0xe0 (the frame's locals, via the glue), 64 (a frame's shadow bytes), 512 (the class-3 frame).
   DERIVED: the cut offsets (4 * the slot inside the function), 69824 / 70528 (the auipc / addi offsets of the MOD_AT /
   STAMP literals from the run's atom 243), 27632 (STKC by computation). WORD: 4 (PJ_STRING), 1 / 0 (the flag),
   2 ^ 64 - 1 (the -1 of `sub`), 2 ^ 46 / 2 ^ 47 / 2 ^ 54 / 2 ^ 61 / 2 ^ 64 (range bounds of the symbolic facts). No
   ADDRESS literal.

   SECTION HYPOTHESES (each with its owner):
   - LAWS (AR_laws_x at cf_head): engine fold YCbqG; at ARcf YGcallcf.AR_laws_x_cf.
   - STRCMP (YGcallMxmn.astrcmp_realizes_xrom at __wrap_strcmp): the libc strcmp row (FuzzStrdup.v carries
     its strlen row the same way).
   - zs_aligned, img_shadow_vis_x: MARKED STAND-INS of Crt102Kit.v (owners: the contract texts / the image row),
     verbatim S10TxState.v, consumed only through Crt102Kit.v's crt_cstr_modat_A / crt_cstr_stamp_A.
   - SAME (tsame_specX at DOC_D), FFREE (tfuzz_free_specX), PJFREE (tpj_free_specX at DOC_D): the callee contract texts.
   - the text's own premises (tcheck_round_trip_specX's, PRH_FnCheck.v): HREAD HXLEN HWL0 HWL1 HLED HCNT HRAN HRQA HKM
     HKS HPRE HTREE HMN HCL HCTX HOS4 (the run's call-tuple bound, `(length rp_os <= 4)%nat`).
   - KX (the X seam): given by Crt102Top.crt102_top_X. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGcallW YGcallMx YGcallMxmn YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue PjWriteHyp WriterApp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnEx PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetCfnA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Img CfImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1ImgA S1Ledger Crt102Glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Crt102Img Crt102Model Crt102Kit.
(* the re-hiding move (wle' / SRr' and its bind, qualified, as Crt102Kit.v takes them) and the
   hull payers of the two free calls' budgets (pj_free's: PresetHullPay; fuzz_free's: Crt102HullPos) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YSRrG YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget PresetSecTotal.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetHullPay.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Crt102HullPos.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
(* a register a run did not write keeps its start value (Crt102Kit.v's crt102rw_keep, section-local there) *)
Ltac clkeep HS := lazymatch goal with |- getr _ ?rr = _ =>
  let H := fresh in prreg HS rr H; rewrite H; repeat rewrite ew_ewset_other by lia; te_close end.
(* a spill word of a run's final state: region i (based at atom k, Xk its value) holds chunk (o, e); the goal left is
   e's denotation *)
Ltac clsp HS i k Xk :=
  unfold crt_spill;
  lazymatch goal with |- val_mem _ (mrestrict _ (ms_mem ?msx)) (?b + ?o) _ ?v =>
  lazymatch type of HS with st_ok_pi _ _ ?E ?ss _ =>
  let r := eval vm_compute in (nth i (ss_mem ss) (YP09.mkRegion None 0 0 0 0 [])) in
  let e := eval vm_compute in (match find (fun c => (YP09.c_off c =? o)%Z) (YP09.r_chunks r) with
                                | Some {| YP09.c_val := CVal _ e |} => e | _ => SLit 0 end) in
  refine (crt102rw_chunk_vm E ss _ msx i r k b o 8%N e v HS ltac:(vm_compute; reflexivity) eq_refl Xk
    ltac:(vm_compute; repeat (first [left; reflexivity | right])) _ _ ltac:(cbn; lia));
  [| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold CRT_OFF_BACK, PJ_OFF_KEYS in *]
  end end.
(* `sv_denot E (SOff k c) = Z_to_bv 64 v` from W : ew E k = w64 b *)
Ltac clden W := rewrite denot_lit_U;
  lazymatch goal with |- Z_to_bv 64 (U ?E (SOff ?k ?c)) = _ =>
    rewrite (U_atom_off E k _ c W) by lia; f_equal; lia end.

(* ======================================================================================================== *)
(* PART 2, image A'. The cut offsets and literals are Crt102Img.v's. *)
Definition CL_SPAN : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition CL_Bx : sv := SOff (xr 26) 0.
(* the shadow address of `x` as the inline checks compute it, `(x >> 3) + s10` *)
Definition cl_sh (x : sv) : sv := SAlu ALU_ADD (SAlu ALU_SRL x (SLit 3)) (SOff (xr 26) 0).

(* ---- L0 (+0x470): s6 pinned to 0 (the new:740 deduction is made before the run); s5 = doc (atom xr 21),
   s8 = saved, s10 = the shadow base, s11 = F. Regions: the spill words at s1 + 0x18 .. + 0x60 (0x38 = &back = F + 0x20,
   0x48 = shadow (&doc->n), 0x50 = &doc->n, 0x58 = doc->n; the run writes 0x18 .. 0x58), doc's keys / n words
   (read-only). Atom 64 = n, 65 = doc->keys. `cs` is the empty-object test the walk splits on before the run
   (`beqz a1` at +0x4a4), so one run reaches the cut it leads to. ---- *)
Definition ss_L0 (cs : list acond) : sstate := mkSS (CRT_PC_A + CRT_L0_OFF) (sr_set cur_atoms 22%bv (SLit 0))
  [ YP09.mkRegion (Some (xr 9)) 24 96 24 88
      [YP09.mkChunk 56 (CVal 8 (SOff (xr 27) 32));
       YP09.mkChunk 72 (CVal 8 (cl_sh (SOff (xr 21) 40))); YP09.mkChunk 80 (CVal 8 (SOff (xr 21) 40));
       YP09.mkChunk 88 (CVal 8 (SOff 64 0))];
    YP09.mkRegion (Some (xr 21)) 32 48 0 0 [YP09.mkChunk 32 (CVal 8 (SOff 65 0)); YP09.mkChunk 40 (CVal 8 (SOff 64 0))] ]
  None
  (mkFacts [(xr 9, mkAF (2 ^ 46) (2 ^ 47) 5); (xr 21, mkAF 4096 (2 ^ 47 - 64) 3); (xr 26, mkAF SHADOW_OFF SHADOW_OFF 0);
            (64%nat, mkAF 0 (2 ^ 54) 0); (65%nat, mkAF 0 (2 ^ 47) 0)] cs []).
Definition cl_K (ss : sstate) : nat := run_K A_LIM CL_Bx [] ss.
Definition ss_addc (ss : sstate) (c : acond) : sstate :=
  mkSS (ss_pc ss) (ss_regs ss) (ss_mem ss) (ss_resv ss)
    (mkFacts (f_atoms (ss_facts ss)) (c :: f_conds (ss_facts ss)) (f_alias (ss_facts ss))).
Definition cl_probe (ss : sstate) (stop : Z) :=
  sym_run_toN_pi_tok (@pl_tpi _ PL_prog_A) (@pl_tw _ PL_prog_A) (cl_K ss) CL_Bx CL_SPAN [] FUEL stop ss.

(* ---- L1 (+0x4e0), one iteration of the at-search: s6 = i (atom xr 22), s9 = s8 = &doc->keys[i] (atom xr 25,
   with the key slot as a read-only 8-byte region holding atom 67 = doc->keys[i]), 0x48(s1) = shadow (doc->keys)
   (atom 68), 0x40(s1) = MOD_AT, 0x58(s1) = 0x50(s1) = n (atom 64). The alias names the inline check's pointer
   `0x48(s1) + s6` as the shadow of the key slot, `((s9 >> 3) + s10)`, which is what it is: 8-aligned slot,
   shadow (keys + 8 i) = shadow (keys) + i. ---- *)
Definition ss_L1 : sstate := mkSS (CRT_PC_A + CRT_L1_OFF) cur_atoms
  [ YP09.mkRegion (Some (xr 9)) 24 96 0 0
      [YP09.mkChunk 24 (CVal 8 (SOff 66 0)); YP09.mkChunk 48 (CVal 8 (SOff (xr 21) 32));
       YP09.mkChunk 56 (CVal 8 (SOff (xr 27) 32)); YP09.mkChunk 64 (CVal 8 (SOff 243 69824));
       YP09.mkChunk 72 (CVal 8 (SOff 68 0)); YP09.mkChunk 80 (CVal 8 (SOff 64 0));
       YP09.mkChunk 88 (CVal 8 (SOff 64 0))];
    YP09.mkRegion (Some (xr 25)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 67 0))] ]
  None
  (mkFacts [(xr 9, mkAF (2 ^ 46) (2 ^ 47) 5); (xr 25, mkAF 4096 (2 ^ 47 - 8) 3); (xr 26, mkAF SHADOW_OFF SHADOW_OFF 0);
            (xr 22, mkAF 0 (2 ^ 54) 0); (64%nat, mkAF 1 (2 ^ 54) 0)] []
    [(SAlu ALU_ADD (SOff 68 0) (SOff (xr 22) 0), SAlu ALU_ADD (SAlu ALU_SRL (SOff (xr 25) 0) (SLit 3)) (SOff (xr 26) 0))]).

(* ---- L1r (+0x4fc), after the at-search's strcmp: a0 (atom xr 10) its answer, s6 = i, s8 = s9 = &doc->keys[i];
   cs: the answer's test and the loop's two exits, split before the run ---- *)
Definition ss_L1r (cs : list acond) : sstate := mkSS (CRT_PC_A + (CRT_CMP1_CALL + 4)) cur_atoms
  [ YP09.mkRegion (Some (xr 9)) 24 96 0 0
      [YP09.mkChunk 24 (CVal 8 (SOff 66 0)); YP09.mkChunk 48 (CVal 8 (SOff (xr 21) 32));
       YP09.mkChunk 56 (CVal 8 (SOff (xr 27) 32)); YP09.mkChunk 64 (CVal 8 (SOff 243 69824));
       YP09.mkChunk 72 (CVal 8 (SOff 68 0)); YP09.mkChunk 80 (CVal 8 (SOff 64 0));
       YP09.mkChunk 88 (CVal 8 (SOff 64 0))] ]
  None
  (mkFacts [(xr 9, mkAF (2 ^ 46) (2 ^ 47) 5); (xr 25, mkAF 4096 (2 ^ 47 - 8) 3); (xr 26, mkAF SHADOW_OFF SHADOW_OFF 0);
            (xr 22, mkAF 0 (2 ^ 54) 0); (64%nat, mkAF 1 (2 ^ 54) 0)] cs []).
Definition cl_cA1 := [mkAC BC_EQ (SOff (xr 10) 0) (SLit 0); mkAC BC_LTU (SOff (xr 22) 1) (SOff 64 0);
  mkAC BC_NE (SOff (xr 22) 0) (SOff 64 0)].
Definition cl_cA2 := [mkAC BC_EQ (SOff (xr 10) 0) (SLit 0); mkAC BC_GEU (SOff (xr 22) 1) (SOff 64 0)].
Definition cl_cB1 := [mkAC BC_NE (SOff (xr 10) 0) (SLit 0); mkAC BC_LTU (SOff (xr 22) 1) (SOff 64 0)].
Definition cl_cB2 := [mkAC BC_NE (SOff (xr 10) 0) (SLit 0); mkAC BC_GEU (SOff (xr 22) 1) (SOff 64 0)].

(* ---- L2 (+0x528): a2 = at (x12), a3 = (at == n) (x13); spills 0x18 saved (66), 0x30 doc + 32, 0x38 F + 32, 0x50 = 0x58 = n
   (64); back's header words at F + 0x38 / 0x40 / 0x48 (kids 68, keys 69, n 70), doc's at doc + 0x18 / 0x20 / 0x28 (kids 67,
   keys 65, n 64). The run writes 0x20 .. 0x58. `cs`: back.n's test and the empty-object test, split before the run. ---- *)
Definition ss_L2 (cs : list acond) : sstate := mkSS (CRT_PC_A + CRT_L2_OFF) cur_atoms
  [ YP09.mkRegion (Some (xr 9)) 24 96 32 96
      [YP09.mkChunk 24 (CVal 8 (SOff 66 0)); YP09.mkChunk 48 (CVal 8 (SOff (xr 21) 32));
       YP09.mkChunk 56 (CVal 8 (SOff (xr 27) 32)); YP09.mkChunk 80 (CVal 8 (SOff 64 0));
       YP09.mkChunk 88 (CVal 8 (SOff 64 0))];
    YP09.mkRegion (Some (xr 27)) 56 80 0 0
      [YP09.mkChunk 56 (CVal 8 (SOff 68 0)); YP09.mkChunk 64 (CVal 8 (SOff 69 0)); YP09.mkChunk 72 (CVal 8 (SOff 70 0))];
    YP09.mkRegion (Some (xr 21)) 24 48 0 0
      [YP09.mkChunk 24 (CVal 8 (SOff 67 0)); YP09.mkChunk 32 (CVal 8 (SOff 65 0)); YP09.mkChunk 40 (CVal 8 (SOff 64 0))] ]
  None
  (mkFacts [(xr 9, mkAF (2 ^ 46) (2 ^ 47) 5); (xr 21, mkAF 4096 (2 ^ 47 - 64) 3); (xr 26, mkAF SHADOW_OFF SHADOW_OFF 0);
            (xr 27, mkAF 4096 (2 ^ 47 - 512) 5); (xr 12, mkAF 0 (2 ^ 54) 0); (xr 13, mkAF 0 1 0);
            (64%nat, mkAF 0 (2 ^ 54) 0); (70%nat, mkAF 0 (2 ^ 54) 0)] cs []).
Definition cl_cBN : acond := mkAC BC_EQ (SOff 70 0) (SAlu ALU_ADD (SOff (xr 13) 0) (SOff 64 0)).
Definition cl_cL2C := [cl_cBN; mkAC BC_EQ (SOff 64 0) (SLit 0)].
Definition cl_cL2L3 := [cl_cBN; mkAC BC_NE (SOff 64 0) (SLit 0)].


(* ---- the model's names for the rewritten tree and pj_write's last capacity ---- *)
Lemma cl_last_cons : forall l (a d : Z), last (a :: l) d = last l a.
Proof.
induction l as [|b l IH]; intros a d; [reflexivity|].
change (last (a :: b :: l) d) with (last (b :: l) d). rewrite !IH. reflexivity.
Qed.
(* the writer's last realloc capacity is the capacity it ends with *)
Lemma cl_last_grow : forall ls x c, last (WriterSpec.grow_calls x c ls) c = WriterSpec.grow_cap x c ls.
Proof.
induction ls as [|l ls IH]; intros x c; cbn [WriterSpec.grow_calls WriterSpec.grow_cap]; [reflexivity|].
destruct (c <? x + l + 1); [rewrite cl_last_cons|]; apply IH.
Qed.

(* ---- THE WRITER'S REQUESTS ARE BELOW RQW: every fuzz_realloc request of pj_write's run is a newcap from 4096 by
   doublings, so the smallest power-of-two multiple of 4096 above its need, and its need is at most the whole text
   and its NUL (`newcap 0 (|wdoc| + 1)` = RQW). This is the bound the new:740 deduction uses: a refused grow of
   pj_write would have set g_ran_out (its request is at most g_most). ---- *)
Lemma cl_dbl_mono : forall f c n1 n2, 0 <= c -> n1 <= n2 -> WriterSpec.dbl f c n1 <= WriterSpec.dbl f c n2.
Proof.
induction f as [|f IH]; intros c n1 n2 Hc Hn; cbn [WriterSpec.dbl]; [lia|].
destruct (Z.leb_spec n2 c) as [H2|H2].
- rewrite (proj2 (Z.leb_le n1 c)) by lia. lia.
- destruct (Z.leb_spec n1 c) as [H1|H1].
  + pose proof (cm_dbl_ge f (2 * c) n2 ltac:(lia)). lia.
  + apply IH; lia.
Qed.
Lemma cl_dbl_fuel : forall f d c n, n <= WriterSpec.dbl f c n -> WriterSpec.dbl (f + d) c n = WriterSpec.dbl f c n.
Proof.
induction f as [|f IH]; intros d c n H.
- cbn [WriterSpec.dbl] in H. cbn [Nat.add]. destruct d as [|d]; cbn [WriterSpec.dbl]; [reflexivity|].
  rewrite (proj2 (Z.leb_le n c) H). reflexivity.
- cbn [Nat.add WriterSpec.dbl] in H |- *. destruct (n <=? c); [reflexivity|]. apply IH. exact H.
Qed.
Lemma cl_dbl_unroll : forall j f c n, (forall i, (i < j)%nat -> c * 2 ^ Z.of_nat i < n) ->
  WriterSpec.dbl (j + f) c n = WriterSpec.dbl f (c * 2 ^ Z.of_nat j) n.
Proof.
induction j as [|j IH]; intros f c n H.
- cbn [Nat.add Z.of_nat]. rewrite Z.pow_0_r, Z.mul_1_r. reflexivity.
- cbn [Nat.add WriterSpec.dbl]. specialize (H 0%nat ltac:(lia)) as H0'. cbn [Z.of_nat] in H0'.
  rewrite Z.pow_0_r, Z.mul_1_r in H0'. rewrite (proj2 (Z.leb_gt n c) H0').
  rewrite IH.
  + f_equal. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
  + intros i Hi. specialize (H (Datatypes.S i) ltac:(lia)). rewrite Nat2Z.inj_succ, Z.pow_succ_r in H by lia. lia.
Qed.
Definition cl_pw (c : Z) : Prop := exists j : nat, c = 4096 * 2 ^ Z.of_nat j.
Lemma cl_dbl_pw : forall f c n, cl_pw c -> cl_pw (WriterSpec.dbl f c n).
Proof.
induction f as [|f IH]; intros c n Hc; cbn [WriterSpec.dbl]; [exact Hc|].
destruct (n <=? c); [exact Hc|]. apply IH. destruct Hc as [j ->]. exists (Datatypes.S j).
rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.
(* doubling on from a power below the need meets the doubling from 4096 *)
Lemma cl_newcap_pw : forall c n, cl_pw c -> c < n -> n <= 2 ^ 62 -> WriterSpec.newcap c n = WriterSpec.newcap 0 n.
Proof.
intros c n [j Ej] Hlt Hn. unfold WriterSpec.newcap. rewrite Z.eqb_refl.
assert (Hc0 : (c =? 0) = false) by (apply Z.eqb_neq; subst c; pose proof (Z.pow_pos_nonneg 2 (Z.of_nat j)); lia).
rewrite Hc0.
assert (Hj : (j < 50)%nat).
{ destruct (Nat.lt_ge_cases j 50) as [H|H]; [exact H|]. exfalso.
  assert (2 ^ 50 <= 2 ^ Z.of_nat j) by (apply Z.pow_le_mono_r; lia). lia. }
replace 64%nat with (j + (64 - j))%nat by lia.
rewrite (cl_dbl_unroll j (64 - j) 4096 n).
- rewrite <- Ej. replace (j + (64 - j))%nat with ((64 - j) + j)%nat by lia.
  apply cl_dbl_fuel. apply cm_dbl_reach; [subst c; pose proof (Z.pow_pos_nonneg 2 (Z.of_nat j)); lia|].
  subst c. rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia. replace (Z.of_nat j + Z.of_nat (64 - j)) with 64 by lia. lia.
- intros i Hi. assert (2 ^ Z.of_nat i < 2 ^ Z.of_nat j) by (apply Z.pow_lt_mono_r; lia). lia.
Qed.
(* the run of puts: every request it appends is at most newcap 0 N *)
Lemma cl_reqs_le : forall P ok st N, (WriterApp.w_cap st = 0 \/ cl_pw (WriterApp.w_cap st)) ->
  Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length (concat P)) + 1 <= N -> N <= 2 ^ 62 ->
  exists l, WriterApp.w_calls (PRH_FnWriter.prhWriter_putN ok st P) = WriterApp.w_calls st ++ l /\
    Forall (fun c => c <= WriterSpec.newcap 0 N) l.
Proof.
induction P as [|b P IH]; intros ok st N Hcap HN HN62.
- exists []. rewrite app_nil_r. split; [reflexivity | constructor].
- cbn [PRH_FnWriter.prhWriter_putN]. rewrite concat_cons, length_app in HN.
  destruct (PRH_FnWriter.prhWriter_grows st b) eqn:Eg.
  + unfold PRH_FnWriter.prhWriter_grows in Eg. apply andb_true_iff in Eg as [Ef Ec].
    apply Z.eqb_eq in Ef. apply Z.ltb_lt in Ec. unfold PRH_FnWriter.prhWriter_need in Ec.
    set (need := Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length b) + 1) in *.
    assert (Ec' : WriterSpec.newcap (WriterApp.w_cap st) need = WriterSpec.newcap 0 need).
    { destruct Hcap as [-> | Hp]; [reflexivity|]. apply cl_newcap_pw; [exact Hp | exact Ec | lia]. }
    assert (Hle : WriterSpec.newcap 0 need <= WriterSpec.newcap 0 N).
    { unfold WriterSpec.newcap. rewrite Z.eqb_refl. apply cl_dbl_mono; lia. }
    assert (Hpw : cl_pw (WriterSpec.newcap 0 need)).
    { unfold WriterSpec.newcap. rewrite Z.eqb_refl. apply cl_dbl_pw. exists 0%nat. reflexivity. }
    unfold PRH_FnWriter.prhWriter_put1. unfold PRH_FnWriter.prhWriter_grows, PRH_FnWriter.prhWriter_need.
    fold need. rewrite (proj2 (Z.eqb_eq _ 0) Ef), (proj2 (Z.ltb_lt _ _) Ec). cbn [andb]. rewrite Ec'.
    destruct (WriterApp.w_cnt st =? WriterApp.w_fail st); [|destruct (hd true ok)].
    * destruct (IH (tl ok) (WriterApp.mkW 1 (WriterApp.w_text st) (WriterApp.w_cap st)
        ((WriterApp.w_cnt st + 1) mod 2 ^ 64) (2 ^ 64 - 1) (WriterApp.w_calls st ++ [WriterSpec.newcap 0 need])) N)
        as (l & El & Fl); cbn [WriterApp.w_cap WriterApp.w_text WriterApp.w_calls]; [exact Hcap | lia | lia |].
      exists (WriterSpec.newcap 0 need :: l). rewrite El. cbn [WriterApp.w_calls]. rewrite <- app_assoc.
      split; [reflexivity | constructor; [lia | exact Fl]].
    * destruct (IH (tl ok) (WriterApp.mkW 0 (WriterApp.w_text st ++ b) (WriterSpec.newcap 0 need)
        ((WriterApp.w_cnt st + 1) mod 2 ^ 64) (WriterApp.w_fail st) (WriterApp.w_calls st ++ [WriterSpec.newcap 0 need])) N)
        as (l & El & Fl); cbn [WriterApp.w_cap WriterApp.w_text WriterApp.w_calls]; [right; exact Hpw | rewrite length_app; lia | lia |].
      exists (WriterSpec.newcap 0 need :: l). rewrite El. cbn [WriterApp.w_calls]. rewrite <- app_assoc.
      split; [reflexivity | constructor; [lia | exact Fl]].
    * destruct (IH (tl ok) (WriterApp.mkW 1 (WriterApp.w_text st) (WriterApp.w_cap st)
        ((WriterApp.w_cnt st + 1) mod 2 ^ 64) (WriterApp.w_fail st) (WriterApp.w_calls st ++ [WriterSpec.newcap 0 need])) N)
        as (l & El & Fl); cbn [WriterApp.w_cap WriterApp.w_text WriterApp.w_calls]; [exact Hcap | lia | lia |].
      exists (WriterSpec.newcap 0 need :: l). rewrite El. cbn [WriterApp.w_calls]. rewrite <- app_assoc.
      split; [reflexivity | constructor; [lia | exact Fl]].
  + unfold WriterApp.put1. destruct (negb (WriterApp.w_failed st =? 0)) eqn:Ef.
    * apply (IH ok st N Hcap); lia.
    * unfold PRH_FnWriter.prhWriter_grows, PRH_FnWriter.prhWriter_need in Eg.
      apply negb_false_iff in Ef. rewrite Ef in Eg. cbn [andb] in Eg. apply Z.ltb_ge in Eg.
      rewrite (proj2 (Z.leb_le _ _) Eg).
      destruct (IH ok (WriterApp.mkW 0 (WriterApp.w_text st ++ b) (WriterApp.w_cap st) (WriterApp.w_cnt st)
        (WriterApp.w_fail st) (WriterApp.w_calls st)) N) as (l & El & Fl);
        cbn [WriterApp.w_cap WriterApp.w_text WriterApp.w_calls]; [exact Hcap | rewrite length_app; lia | lia |].
      exists l. split; [exact El | exact Fl].
Qed.
(* in prh_oks' indexing *)
Lemma cl_writer_req : forall ok cnt fail P i, Z.of_nat (length (concat P)) + 1 <= 2 ^ 62 ->
  nth i (PRH_FnWriter.prhWriter_reqs ok (WriterApp.w0 cnt fail) P) 0 <=
    WriterSpec.newcap 0 (Z.of_nat (length (concat P)) + 1).
Proof.
intros ok cnt fail P i Hs.
destruct (cl_reqs_le P ok (WriterApp.w0 cnt fail) (Z.of_nat (length (concat P)) + 1) ltac:(left; reflexivity)
  ltac:(cbn [WriterApp.w_text WriterApp.w0 length Z.of_nat]; lia) Hs) as (l & El & Fl).
unfold PRH_FnWriter.prhWriter_reqs. rewrite El. unfold WriterApp.w0. cbn [WriterApp.w_calls app length skipn].
destruct (Nat.lt_ge_cases i (length l)) as [Hi|Hi].
- exact (proj1 (Forall_forall _ _) Fl _ (nth_In l 0 Hi)).
- change (skipn 0 l) with l. rewrite nth_overflow by lia. unfold WriterSpec.newcap. rewrite Z.eqb_refl.
  pose proof (cm_dbl_ge 64 4096 (Z.of_nat (length (concat P)) + 1) ltac:(lia)). lia.
Qed.


(* ---- L3 (+0x590), iteration i of the member loop: a0 = a1 = &back.keys[i] (x10, x11), a2 = s9 = &doc->keys[i] (x12,
   x25), s5 = shadow (&back.keys[i]) (x21; the alias names it so for the inline check), s6 = at - i (x22); spills
   0x18 saved (66), 0x20 at (67), 0x28 shadow (doc + 0x18) and 0x30 doc + 0x18 over doc (68), 0x38 F + 32, 0x50 n - i (64),
   0x58 56 i (65); the two key slots hold back.keys[i] (69) and doc->keys[i] (70). The run writes 0x40 .. 0x50. ---- *)
Definition ss_L3 : sstate := mkSS (CRT_PC_A + CRT_L3_OFF) cur_atoms
  [ YP09.mkRegion (Some (xr 9)) 24 96 64 80
      [YP09.mkChunk 24 (CVal 8 (SOff 66 0)); YP09.mkChunk 32 (CVal 8 (SOff 67 0));
       YP09.mkChunk 40 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 68 24) (SLit 3)) (SOff (xr 26) 0)));
       YP09.mkChunk 48 (CVal 8 (SOff 68 24)); YP09.mkChunk 56 (CVal 8 (SOff (xr 27) 32));
       YP09.mkChunk 80 (CVal 8 (SOff 64 0)); YP09.mkChunk 88 (CVal 8 (SOff 65 0))];
    YP09.mkRegion (Some (xr 11)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 69 0))];
    YP09.mkRegion (Some (xr 12)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 70 0))] ]
  None
  (mkFacts [(xr 9, mkAF (2 ^ 46) (2 ^ 47) 5); (xr 11, mkAF 4096 (2 ^ 47 - 8) 3); (xr 12, mkAF 4096 (2 ^ 47 - 8) 3);
            (xr 26, mkAF SHADOW_OFF SHADOW_OFF 0); (xr 27, mkAF 4096 (2 ^ 47 - 512) 5);
            (64%nat, mkAF 1 (2 ^ 54) 0)] []
    [(SOff (xr 21) 0, SAlu ALU_ADD (SAlu ALU_SRL (SOff (xr 11) 0) (SLit 3)) (SOff (xr 26) 0));
     (SAlu ALU_ADD (SAlu ALU_SRL (SOff (xr 25) 0) (SLit 3)) (SOff (xr 26) 0),
      SAlu ALU_ADD (SAlu ALU_SRL (SOff (xr 12) 0) (SLit 3)) (SOff (xr 26) 0))]).

Lemma cl_pairwise_in : forall {A : Type} (R : A -> A -> Prop) l x y, pairwise R l -> In x l -> In y l ->
  x = y \/ R x y \/ R y x.
Proof.
intros A R l. induction l as [|z l IH]; intros x y P Hx Hy; [destruct Hx|]. cbn in P. destruct P as [F P].
destruct Hx as [<-|Hx], Hy as [<-|Hy].
- left. reflexivity.
- right. left. exact (proj1 (Forall_forall _ _) F y Hy).
- right. right. exact (proj1 (Forall_forall _ _) F x Hx).
- exact (IH x y P Hx Hy).
Qed.
Lemma cl_in_fst_elem : forall (l : list (Z * Z)) a k, In (a, k) l -> a ∈ map fst l.
Proof.
induction l as [|[b j] l IH]; intros a k H; [destruct H|].
destruct H as [E|H].
- inversion E; subst. cbn [map fst]. constructor.
- cbn [map fst]. constructor 2. exact (IH a k H).
Qed.
Lemma cl_nodup_fst : forall (l : list (Z * Z)) a k1 k2, NoDup (map fst l) -> In (a, k1) l -> In (a, k2) l -> k1 = k2.
Proof.
induction l as [|[a0 k0] l IH]; intros a k1 k2 Hnd H1 H2; [destruct H1|].
cbn [map fst] in Hnd. inversion Hnd as [|? ? Hn Hnd0]; subst. clear Hnd. rename Hnd0 into Hnd.
destruct H1 as [E1|H1], H2 as [E2|H2].
- inversion E1; inversion E2; subst. reflexivity.
- inversion E1; subst. exfalso. exact (Hn (cl_in_fst_elem l a k2 H2)).
- inversion E2; subst. exfalso. exact (Hn (cl_in_fst_elem l a k1 H1)).
- exact (IH a k1 k2 Hnd H1 H2).
Qed.

(* ---- L3r (+0x5c0), after the member compare: a0 (x10) the answer; s5 (x21) = shadow (&back.keys[i]), s6 (x22) = at - i,
   s8 = s9 = &doc->keys[i] (x24, x25); spills as at L3 plus 0x40 / 0x48 = &back.keys[i] (71); back's kids word at
   F + 0x38 (69) and doc's at doc + 0x18 (70, the region based at atom 68 = doc). `cs`: the answer's test, i == at, and
   the counter's test, split before the run. L3s (+0x5f4) is the same state after `same` returned (x10 its answer). ---- *)
Definition cl_ss3 (pc : Z) (cs : list acond) : sstate := mkSS pc cur_atoms
  [ YP09.mkRegion (Some (xr 9)) 24 96 80 96
      [YP09.mkChunk 24 (CVal 8 (SOff 66 0)); YP09.mkChunk 32 (CVal 8 (SOff 67 0));
       YP09.mkChunk 40 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 68 24) (SLit 3)) (SOff (xr 26) 0)));
       YP09.mkChunk 48 (CVal 8 (SOff 68 24)); YP09.mkChunk 56 (CVal 8 (SOff (xr 27) 32));
       YP09.mkChunk 64 (CVal 8 (SOff 71 0)); YP09.mkChunk 72 (CVal 8 (SOff 71 0));
       YP09.mkChunk 80 (CVal 8 (SOff 64 0)); YP09.mkChunk 88 (CVal 8 (SOff 65 0))];
    YP09.mkRegion (Some (xr 27)) 56 64 0 0 [YP09.mkChunk 56 (CVal 8 (SOff 69 0))];
    YP09.mkRegion (Some 68%nat) 24 32 0 0 [YP09.mkChunk 24 (CVal 8 (SOff 70 0))] ]
  None
  (mkFacts [(xr 9, mkAF (2 ^ 46) (2 ^ 47) 5); (xr 26, mkAF SHADOW_OFF SHADOW_OFF 0); (xr 27, mkAF 4096 (2 ^ 47 - 512) 5);
            (68%nat, mkAF 4096 (2 ^ 47 - 64) 3); (64%nat, mkAF 1 (2 ^ 54) 0); (65%nat, mkAF 0 (2 ^ 60) 0)] cs []).
Definition cl_cR_eq : acond := mkAC BC_EQ (SOff (xr 10) 0) (SLit 0).
Definition cl_cR_at : acond := mkAC BC_EQ (SOff (xr 22) 0) (SLit 0).
Definition cl_cR_nat : acond := mkAC BC_NE (SOff (xr 22) 0) (SLit 0).
Definition cl_cR_more : acond := mkAC BC_NE (SOff 64 (-1)) (SLit 0).
Definition cl_cR_last : acond := mkAC BC_EQ (SOff 64 (-1)) (SLit 0).
Definition cl_cS_ok : acond := mkAC BC_NE (SOff (xr 10) 0) (SLit 0).

Lemma cl_zbv_mod : forall a b, a mod 2 ^ 64 = b mod 2 ^ 64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). exact H. Qed.

Section piok. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance CfImg_A.
#[local] Existing Instance CfParams_preset.
#[local] Notation PA := (PI_prog_A).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
(* a run stopped at a call: its state as a position-independent one (the chunk readers take that form) *)
Lemma cl_pi_of_ok : forall (E : env) ss pc m, st_ok SEGS E (setpc ss pc) m ->
  st_ok_pi SEGS VAL E (setpc ss (pc - BASE)) m.
Proof.
intros E ss pc m H. unfold st_ok_pi, abs_ss. destruct ss. unfold setpc in *. cbn.
replace (BASE + (pc - BASE)) with pc by lia. exact H.
Qed.
End piok.

Section A. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance CfImg_A.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_A.
Context {SK : YI16.sink_head} {RL : PrhRoomLive}.
#[local] Notation PA := (PI_prog_A).
#[local] Notation PL := (PL_prog_A).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ A_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ A_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_A)).
#[local] Notation STKC := (@STK_check_round_trip prh_img_A).


Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* THE LIBC ROW for __wrap_strcmp, as a Section hypothesis (FuzzStrdup.v carries its strlen row
   the same way): YGcallMxmn.v's astrcmp_realizes_xrom, the arodata_okP text WITH the memnorm keep - the keep is what
   crt_live's last conjunct needs after each of this slice's four strcmp calls (+0x4f8, +0x5bc, +0x664, +0x6c4). *)
Hypothesis STRCMP : forall fxq : YK11.FPState,
  @YGcallMxmn.astrcmp_realizes_xrom fxq SEGS B ARx RLO RHI (SIGMA AS___wrap_strcmp).
(* MARKED STAND-IN (the unit's image binding of B; owner: the contract texts; ARcf gives it by amc_syms / aso_zshadow,
   YG0f.v:191). Verbatim S10TxState.v:141, as at Crt102Kit.v:583; consumed only through Crt102Kit.v's crt_cstr_modat_A. *)
Hypothesis zs_aligned : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow B).
(* MARKED STAND-IN (owner: the image row; FuzzStrdup.v's img_shadow_vis_cf restated over ARx). Verbatim
   S10TxState.v:143, as Crt102Kit.v:586 takes it; consumed only through Crt102Kit.v's crt_cstr_modat_A. *)
Hypothesis img_shadow_vis_x : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> IMG_LO <= a < IMG_TOP ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
(* THE CALLEES' CONTRACT TEXTS, at every float state (their walks are generic in fx; Crt102Rewrite.v takes FFREE the
   same way): same (+0x5f0) at n = DOC_D *)
Hypothesis SAME : forall fxq : YK11.FPState, PRH_FnEx.tsame_specX (fx := fxq) B ARx SK DOC_D.
(* fuzz_free (+0x6d0) *)
Hypothesis FFREE : forall fxq : YK11.FPState, PRH_FnAlloc.tfuzz_free_specX (fx := fxq) B ARx SK.

(* ---- memory agreement: a view that agrees on a byte set and keeps every present byte present keeps a tree, a word,
   a shadow fact ---- *)
Lemma cl_writable_mono : forall (H : word -> bool) m m' a,
  (forall z, apresent H m z -> apresent H m' z) ->
  writable_at SEGS (mrestrict H m) a -> writable_at SEGS (mrestrict H m') a.
Proof.
intros H m m' a Hp Hw. unfold writable_at, wview, mrestrict in *.
destruct (H (Z_to_bv 64 a)) eqn:EH; [exact Hw|].
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
- assert (Hpa : apresent H m a).
  { split; [exact EH|]. exists b. exact Em. }
  destruct (Hp a Hpa) as [_ [b' Hb']]. rewrite Hb'. discriminate.
- destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
Lemma cl_agree : forall (H : word -> bool) m m' (X : Z -> Prop),
  (forall z, X z -> aview SEGS H m' z = aview SEGS H m z) ->
  (forall z, apresent H m z -> apresent H m' z) ->
  pj_agreeR SEGS (mrestrict H m) (mrestrict H m') X.
Proof.
intros H m m' X Hv Hp z Hz. split.
- exact (mbyte_of_aview SEGS H H m m' z (Hv z Hz)).
- apply cl_writable_mono. exact Hp.
Qed.
Lemma cl_ra_keep : forall (rd rd' : reader) p n,
  (forall z, SHADOW_OFF <= z < kHighMemBeg -> rd' z = rd z) -> 0 <= p -> p + n <= 2 ^ 47 ->
  range_addressable rd SHADOW_OFF p n -> range_addressable rd' SHADOW_OFF p n.
Proof.
intros rd rd' p n Hk H0 H1 Hr z Hz. destruct (Hr z Hz) as (s & Hs & Hok). exists s. split; [|exact Hok].
rewrite Hk; [exact Hs|]. unfold shadow_of_addr, SHADOW_OFF, kHighMemBeg in *.
assert (0 <= z / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia). lia.
Qed.
Lemma cl_hull_keep : forall (rd rd' : reader) p n,
  (forall z, SHADOW_OFF <= z < kHighMemBeg -> rd' z = rd z) -> 0 <= p -> p + n <= 2 ^ 47 -> 0 < n ->
  shadow_hull_vis rd p n -> shadow_hull_vis rd' p n.
Proof.
intros rd rd' p n Hk H0 H1 H2 Hh z Hz. rewrite Hk; [exact (Hh z Hz)|].
unfold shadow_addr, SHADOW_OFF, kHighMemBeg in *.
assert (0 <= p / 8) by (apply Z.div_pos; lia).
assert ((p + n - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
assert (Hlo : 0x7fff8000 / 8 <= (0x7fff8000 + p / 8) / 8) by (apply Z.div_le_mono; lia).
assert ((0x7fff8000 + (p + n - 1) / 8) / 8 * 8 <= 0x7fff8000 + (p + n - 1) / 8).
{ pose proof (Z.mul_div_le (0x7fff8000 + (p + n - 1) / 8) 8 ltac:(lia)). lia. }
change (0x7fff8000 / 8) with 268431360 in Hlo. lia.
Qed.

(* ---- a word read twice is one value (rdword is a function) ---- *)
Lemma cl_vm_det : forall (H : word -> bool) m a v v', val_mem SEGS (mrestrict H m) a 8 v -> val_mem SEGS (mrestrict H m) a 8 v' ->
  0 <= v < 2 ^ 64 -> 0 <= v' < 2 ^ 64 -> v = v'.
Proof.
intros H m a v v' H1 H2 R1 R2.
pose proof (crt102rw_rdword_of_vm SEGS H m a v H1 R1) as E1. pose proof (crt102rw_rdword_of_vm SEGS H m a v' H2 R2) as E2.
rewrite E1 in E2. congruence.
Qed.
(* ---- member i of an object: its key slot, its key string's block, its value's node ---- *)
Lemma cl_mems_nth : forall m lblk (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a ka D i nm u,
  pj_memsR SEGS m lblk P a ka l D -> nth_error l i = Some (nm, u) ->
  exists px k D1, rd_u64 SEGS m (ka + 8 * Z.of_nat i) px /\ pj_cstrR SEGS m lblk px k nm /\ In (px, k) D /\
    incl D1 D /\ P (a + 56 * Z.of_nat i) u D1.
Proof.
intros m lblk P l. induction l as [|[nm0 u0] r IH]; intros a ka D i nm u H Hi; [destruct i; discriminate|].
cbn [pj_memsR] in H. destruct H as (px & k & D1 & D2 & -> & Hx & Hc & H1 & H2).
destruct i as [|i]; cbn [nth_error] in Hi.
- injection Hi as <- <-. exists px, k, D1. rewrite Z.add_0_r, Z.add_0_r.
  split; [exact Hx|]. split; [exact Hc|]. split; [left; reflexivity|]. split; [|exact H1].
  intros b Hb. right. apply in_or_app. left. exact Hb.
- destruct (IH (a + 56) (ka + 8) D2 i nm u H2 Hi) as (px' & k' & D1' & Hx' & Hc' & Hin' & Hinc & HP).
  exists px', k', D1'. replace (ka + 8 * Z.of_nat (S i)) with (ka + 8 + 8 * Z.of_nat i) by lia.
  replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) by lia.
  split; [exact Hx'|]. split; [exact Hc'|]. split; [right; apply in_or_app; right; exact Hin'|]. split; [|exact HP].
  intros b Hb. right. apply in_or_app. right. exact (Hinc b Hb).
Qed.

(* ======================================================================================================== *)
(* THE STRINGS A strcmp OF THIS WALK IS HANDED: what the libc row asks of one argument (YGcallMxmn.v
   astrcmp_realizes_xrom), from a harness heap block (a key of doc or of back, back's STAMP string) or from a C
   string of the image (the two literals, Crt102Kit.v's crt_cstr_modat_A / crt_cstr_stamp_A) *)
Definition cl_sarg (Wc : world SEGS) (m : word -> option byte) (p k : Z) : Prop :=
  4096 <= p /\ 0 <= k /\ k + 1 < 2 ^ 32 /\ p + k + 1 <= YM05.alloc_ceiling /\
  first_byte SEGS Wc m p (k + 1) 0 k /\
  (forall a, p <= a < p + k + 1 -> aview SEGS (w_H Wc) m a <> None) /\
  (p + (k + 1) + 8 <= kLowMemEnd - 1 \/ (kHighMemBeg + 15 <= p /\ p + (k + 1) + 8 <= kHighMemEnd - 1)) /\
  range_addressable (aview SEGS (w_H Wc) m) SHADOW_OFF p (k + 1) /\ shadow_hull_vis (aview SEGS (w_H Wc) m) p (k + 1) /\
  (forall a, p + k < a < p + k - (p + k) mod 8 + 8 -> aview SEGS (w_H Wc) m a <> None).

Lemma cl_hull_sub : forall (rd : reader) x n x' n', shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> 0 < n' ->
  0 <= x' -> shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H1 H2 H3 H4 s Hs. apply H. unfold shadow_addr in *.
assert (A0 : x / 8 <= x' / 8) by (apply Z.div_le_mono; lia).
assert (A1 : (x / 8 + SHADOW_OFF) / 8 <= (x' / 8 + SHADOW_OFF) / 8) by (apply Z.div_le_mono; lia).
assert (A2 : (x' + n' - 1) / 8 <= (x + n - 1) / 8) by (apply Z.div_le_mono; lia).
assert (A3 : ((x' + n' - 1) / 8 + SHADOW_OFF) / 8 <= ((x + n - 1) / 8 + SHADOW_OFF) / 8) by (apply Z.div_le_mono; lia).
lia.
Qed.

(* a garr8 byte, read through the view *)
Lemma cl_garr8_av : forall (H : word -> bool) m p l j, garr8 SEGS (mrestrict H m) p l -> (j < length l)%nat ->
  aview SEGS H m (p + Z.of_nat j) = Some (nth j l 0).
Proof. intros H m p l j Hg Hj. destruct (Hg j Hj) as [Hv Hr]. exact (ts_aview_of_vm1 H m _ _ Hv Hr). Qed.

(* the bytes of a C string, as strcmp's first_byte reads them *)
Lemma cl_first_byte : forall (Wc : world SEGS) m p s, garr8 SEGS (mrestrict (w_H Wc) m) p (s ++ [0]) ->
  Forall (fun c => c <> 0) s -> first_byte SEGS Wc m p (Z.of_nat (length s) + 1) 0 (Z.of_nat (length s)).
Proof.
intros Wc m p s Hg Hnz. split; [lia|]. split.
- intros i Hi. exists (nth (Z.to_nat i) s 0). split.
  + replace (p + i) with (p + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (cl_garr8_av _ _ _ _ _ Hg) by (rewrite length_app; cbn; lia).
    rewrite app_nth1 by lia. reflexivity.
  + apply (proj1 (Forall_forall _ _) Hnz). apply nth_In. lia.
- intros _. rewrite <- (Nat2Z.id (length s)) at 1. rewrite Z2Nat.id by lia.
  rewrite (cl_garr8_av _ _ _ _ _ Hg) by (rewrite length_app; cbn; lia).
  rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.

(* a C string of the image (cstr_ok, PRH_Base.v) *)
Lemma cl_sarg_cstr : forall (Wc : world SEGS) m p l, cstr_ok (PA := PA) Wc m p l -> cl_sarg Wc m p (Z.of_nat (length l)).
Proof.
intros Wc m p l ((Hg & Hnz) & H4 & Hc & H32 & Ham & Hra & Hhv & Htl). unfold cl_sarg.
split; [exact H4|]. split; [lia|]. split; [exact H32|]. split; [lia|].
split; [exact (cl_first_byte _ _ _ _ Hg Hnz)|]. split.
- intros a Ha. replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia.
  rewrite (cl_garr8_av _ _ _ _ _ Hg) by (rewrite length_app; cbn; lia). discriminate.
- split; [unfold YGcfStr.amem_range8 in Ham; exact Ham|]. split; [exact Hra|]. split; [exact Hhv | exact Htl].
Qed.

(* a harness heap block of the ledger: its user bytes' shadow, hull, presence and tail granule (the head-shadow law
   alx_hshadow at cf_head, the blocks law, the tail law) *)
Lemma cl_hblk : forall lyc Sc Hpc (Wc : world SEGS) memc mdc Lamc peakc cntc failc ranc mostc ownc a k,
  ARx lyc Sc Hpc Wc memc mdc -> prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc -> In (a, k) Lamc ->
  0 <= k /\ a mod 16 = 0 /\ in_app (a - 16) (k + 16) /\ a + k <= YM05.alloc_ceiling /\ 4096 + 16 <= a /\
  block_shadow (aview SEGS (w_H Wc) memc) SHADOW_OFF a k /\
  (0 < k -> shadow_hull_vis (aview SEGS (w_H Wc) memc) a k) /\
  (forall z, a <= z < a + k -> apresent (w_H Wc) memc z) /\
  (forall z, a + k <= z < (a + k + 7) / 8 * 8 -> aview SEGS (w_H Wc) memc z <> None).
Proof.
intros lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc mostc ownc a k HAR HL Hin.
destruct (prh_ledger_hblock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL Hin) as (Hk & Hb & Hhp & Ha16 & _).
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HAR Hb) as (B16 & B1 & B2 & Bapp & Bpres & _).
destruct (alx_hshadow _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HAR Hb Hhp) as (Hbs & Hhull).
pose proof (fun z => alx_blocks_tail _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ z HAR Hb) as Htail.
change (@cf_head CfParams_preset) with 16 in *.
assert (Er : req_size (k + 16) = k + 16) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
rewrite Er in *. replace (a - 16 + 16) with a in Hbs, Hhull by lia. replace (k + 16 - 16) with k in Hbs, Hhull by lia.
split; [exact Hk|]. split; [exact Ha16|]. split; [exact Bapp|]. split; [lia|]. split; [lia|].
split; [exact Hbs|]. split; [|split].
- intros Hk0. apply Hhull. lia.
- intros z Hz. apply (proj1 (Bpres z ltac:(lia))).
- intros z Hz. apply (Htail z). lia.
Qed.

(* a key or a string of a tree in the walk's blocks, as a strcmp argument *)
Lemma cl_sarg_heap : forall lyc Sc Hpc (Wc : world SEGS) memc mdc Lamc peakc cntc failc ranc mostc ownc p kb s,
  ARx lyc Sc Hpc Wc memc mdc -> prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc -> In (p, kb) Lamc ->
  pj_cbytesR SEGS (mrestrict (w_H Wc) memc) p s -> Z.of_nat (length s) + 1 <= kb -> Z.of_nat (length s) + 1 < 2 ^ 32 ->
  cl_sarg Wc memc p (Z.of_nat (length s)).
Proof.
intros lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc mostc ownc p kb s HAR HL Hin (Hf & Hg) Hk Hk32.
destruct (cl_hblk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HL Hin) as (Hk0 & H16 & Happ & Hce & H4 & Hbs & Hhv & Hpr & Htl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hnz : Forall (fun c => c <> 0) s) by (eapply Forall_impl; [|exact Hf]; cbv beta; intros c Hc; lia).
set (k := Z.of_nat (length s)) in *. unfold cl_sarg.
assert (Hvis : forall z, p <= z < p + kb -> aview SEGS (w_H Wc) memc z <> None).
{ intros z Hz. destruct (Hpr z Hz) as [Hh [bb Hbb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hbb. discriminate. }
split; [lia|]. split; [lia|]. split; [exact Hk32|]. split; [lia|].
split; [exact (cl_first_byte _ _ _ _ Hg Hnz)|]. split; [|split; [|split; [|split]]].
- intros a Ha. apply Hvis. lia.
- unfold in_app, kLowShadowBeg, ASAN_CEIL in Happ. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
- exact (block_shadow_range _ SHADOW_OFF p kb p (k + 1) Hbs ltac:(lia) ltac:(lia)).
- apply (cl_hull_sub _ p kb p (k + 1)); [apply Hhv; lia | lia | lia | lia | lia].
- intros a Ha. destruct (Z_lt_le_dec a (p + kb)) as [Hlt | Hge]; [apply Hvis; lia|].
  apply Htl. split; [lia|].
  pose proof (Z.mod_pos_bound (p + k) 8 ltac:(lia)). pose proof (Z.div_mod (p + k) 8 ltac:(lia)).
  assert (E1 : p + k - (p + k) mod 8 = 8 * ((p + k) / 8)) by lia.
  assert ((p + k) / 8 + 1 <= (p + kb + 7) / 8).
  { replace ((p + k) / 8 + 1) with ((p + k + 1 * 8) / 8) by (rewrite Z.div_add by lia; lia).
    apply Z.div_le_mono; lia. }
  nia.
Qed.

(* strcmp's answer read as list equality: two C strings agree byte for byte up to equal lengths iff they are equal *)
Lemma cl_str_eq : forall (H : word -> bool) m x y s1 s2,
  garr8 SEGS (mrestrict H m) x (s1 ++ [0]) -> garr8 SEGS (mrestrict H m) y (s2 ++ [0]) ->
  (Z.of_nat (length s1) = Z.of_nat (length s2) /\
   forall i, 0 <= i < Z.of_nat (length s1) -> aview SEGS H m (x + i) = aview SEGS H m (y + i)) <-> s1 = s2.
Proof.
intros H m x y s1 s2 G1 G2. split.
- intros (El & Eb). apply Nat2Z.inj in El. apply (nth_ext s1 s2 0 0 El). intros j Hj.
  specialize (Eb (Z.of_nat j) ltac:(lia)).
  rewrite (cl_garr8_av _ _ _ _ _ G1) in Eb by (rewrite length_app; cbn; lia).
  rewrite (cl_garr8_av _ _ _ _ _ G2) in Eb by (rewrite length_app; cbn; lia).
  rewrite !app_nth1 in Eb by lia. congruence.
- intros <-. split; [reflexivity|]. intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia.
  rewrite (cl_garr8_av _ _ _ _ _ G1), (cl_garr8_av _ _ _ _ _ G2) by (rewrite length_app; cbn; lia). reflexivity.
Qed.

Section g.
(* ---- tcheck_round_trip_specX's binders (PRH_FnCheck.v 1b4213c5f76f), as the glue's Section g names them ---- *)
Variables (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
  (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk).
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z))
  (doc : Z) (t : PjTree.jv) (D : list (Z * Z)) (x : list Z)
  (Lam : list (Z * Z)) (peak cnt ran most : Z) (CTX0 : list (list Z)).
#[local] Notation sp0 := (spZ regs).
(* the text's premises this slice reads (PRH_FnCheck.v tcheck_round_trip_specX) *)
Hypothesis HREAD : ck_read x = Some t.
Hypothesis HXLEN : Z.of_nat (length x) <= 3 * 2 ^ 20.
Hypothesis HWL0 : PjWriteHyp.wlen t false <= 3 * Z.of_nat (length x).
Hypothesis HWL1 : PjWriteHyp.wlen t true <= 56 * Z.of_nat (length x) - 54.
Hypothesis HLED : prh_ledger B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran most 0.
Hypothesis HCNT : cnt < 2 ^ 62 - 2 ^ 30.
Hypothesis HRAN : ran = 0.
Hypothesis HRQA : RQA_crt t <= most.
Hypothesis HKM : kept_img B CRT_MOD_AT_A (Z.of_nat (length ck_MOD_AT) + 1).
Hypothesis HKS : kept_img B CRT_STAMP_A (Z.of_nat (length ck_STAMP) + 1).
(* the run's call-tuple bound, the callee texts' new premise (PRH_FnCheck.v's own text premise;
   Crt102Top passes it): the hull budget of pj_free (&back) is paid from the run position with it
   (PresetHullPay.hull_budget_of_room_pos) *)
Hypothesis HOS4 : (length rp_os <= 4)%nat.

(* the glue's predicates at this Section's binders, every implicit argument BY NAME (the unit owner's rule: a
   positional application re-binds silently after a signature change) *)
#[local] Notation QFa := (QF (fx := fx) (rc := rc) (PI := prh_img_A) (RL := RL) (SK := SK) (L := A_prog_listing)
  (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)).
#[local] Notation L0a := (crt_at_L0 (fx := fx) (rc := rc) (PI := prh_img_A) (RL := RL) (SK := SK) (L := A_prog_listing)
  (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (most := most)).
(* kb round: every boundary of this slice (L0, L3, C, X, J) is at kb = prh_wk F_check_round_trip (the brief's table:
   pj_write / parse_noting are behind; strcmp, same, fuzz_free and pj_free store no fresh wild trace) *)
#[local] Notation livea := (crt_live (rc := rc) (PI := prh_img_A) (RL := RL) (SK := SK) (L := A_prog_listing)
  (PA := PA) (B := B) (ARx := ARx) (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md)
  (doc := doc) (t := t) (D := D) (Lam := Lam) (peak := peak) (most := most) (prh_wk F_check_round_trip)).
(* the re-hiding move (the wle' contract): the world relation of every journal of this slice *)
#[local] Notation RZW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
(* the journal at a wild-trace budget WS (YCbqG.v ajournal_xwR at RZW) *)
#[local] Notation AJW := (ajournal_xwR (SK := SK) SEGS B PST ARx RZW).
#[local] Notation posa := (crt_pos (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (t := t)).
#[local] Notation cfga := (crt_cfg (rc := rc) (L := A_prog_listing) (PA := PA) (CRT_PC := CRT_PC_A)).
#[local] Notation tc := (crt_tc (t := t)).
#[local] Notation tb := (crt_tb (t := t)).

Lemma cl_in : cm_in x t.
Proof. exact (cm_in_intro x t HREAD HXLEN HWL0 HWL1). Qed.
Lemma cl_cnt_nn : 0 <= cnt.
Proof. pose proof HLED as H0. apply prh_ledger_bounds in H0. destruct H0 as (_ & _ & H & _). lia. Qed.

(* ---- THE DEDUCTION THAT KILLS THE PROPERTY ABORT OF new:740 (`!saved || rc != 0`, L0's `bnez s6`): under the
   request bound every refused allocation of pj_write / parse_noting would have set g_ran_out (prh_oks' third
   conjunct, the citation the bound makes legitimate), O2 read it back as 0, and g_fail_at = SIZE_MAX names no call
   below the top; so pj_write's run made every call it asked, did not fail, and returned its text (saved <> 0), and
   the read-back, granted every call, is the grammar's reading of the pretty text, the rewritten tree (rc = 0). ---- *)
Lemma cl_L0_saved : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dx Lamc peakc cntc rg ms cset saved rcd,
  L0a fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dx Lamc peakc cntc rg ms cset saved rcd ->
  saved <> 0 /\ rcd = 0 /\ cntc = cnt + ck_crt_count t cset /\ posa Sc (crt_evs_L0 ms) /\
  exists cap Dback, Dx = Dback ++ (saved, cap) :: Dc /\
    pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) tc Dback /\
    Permutation (map (fun b => snd b + cf_head) Dback) (PresetReqAtNoMiss.tblk tc) /\
    (exists Fb, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D
       (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) Dback Fb /\
     map (fun b => snd b + cf_head) Fb = PresetReqAt.fo tc) /\
    cap = last (PresetReqAt.wcaps (PresetReqAt.copy_set ms) true) 0.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dx Lamc peakc cntc rg ms cset saved rcd HL0.
pose proof (crt_at_L0_obj HL0) as Et.
pose proof (crt_at_L0_cset_range HL0) as Hcs.
destruct (crt_at_L0_outcome HL0) as (ok & HOK & Hout).
pose proof cl_in as Hin. pose proof cl_cnt_nn as Hc0.
destruct (cm_cnt_write x t ms cset cnt Hin Et Hcs ltac:(lia)) as (Hw0 & Hw1).
pose proof (cm_cnt_total x t cset cnt Hin Hcs ltac:(lia)) as Htot.
assert (Ecw : crt_cw (t := t) (cnt := cnt) cset = ck_cnt2 cnt t + 1 + cset) by (unfold crt_cw; rewrite cm_cnt2_eq; lia).
unfold crt_wP, crt_tb in *. unfold crt_tc in *. rewrite Ecw in HOK, Hout.
set (cw := ck_cnt2 cnt t + 1 + cset) in *.
pose proof HOK as (_ & _ & HOK3).
pose proof (cm_wcalls_nonneg (ck_crt_tree t) true) as Hwn.
assert (Hcw : 0 <= cw < 2 ^ 64) by (unfold cw in *; split; lia).
destruct Hout as [(Hs0 & Hfl & _) | (Hs0 & Hfl & okr & res & tr & Hrun & HOKr & Hcnt & Hread & Hres)].
- (* pj_write returned NULL: some call of its run failed; it is not g_fail_at's (SIZE_MAX is above every count),
     so it was refused, and prh_oks sets g_ran_out = 1 - but O2 read 0 *)
  exfalso.
  destruct (cm_pjw_fail ok cw SIZE_MAXZ (ck_crt_tree t) true ltac:(lia) Hw1 Hfl) as (i & Hi & [Hf | Hf]).
  + pose proof (cm_pjw_k_le ok cw SIZE_MAXZ (ck_crt_tree t) true Hcw) as Hk.
    unfold SIZE_MAXZ in Hf. lia.
  + (* a REFUSAL: its request is pj_write's, at most RQW (ck_crt_tree t) true (cl_writer_req), at most g_most
       (RQA_crt t <= most, the text's request bound; cm_rqa_write), so #102's refused () set g_ran_out *)
    pose proof (cm_pjw_k_le ok cw SIZE_MAXZ (ck_crt_tree t) true Hcw) as Hk.
    assert (Href : prh_refused ok cw SIZE_MAXZ i = true).
    { unfold prh_refused. rewrite Hf. cbn [negb andb]. apply negb_true_iff, Z.eqb_neq. unfold SIZE_MAXZ. lia. }
    pose proof (cm_in_wlen_crt x t Hin) as (_ & _ & Hlen).
    assert (Hreq : nth i (PRH_FnWriter.prhWriter_reqs ok (WriterApp.w0 cw SIZE_MAXZ)
      (WriterValue.wdpieces (ck_crt_tree t) true)) 0 <= most).
    { pose proof (cl_writer_req ok cw SIZE_MAXZ (WriterValue.wdpieces (ck_crt_tree t) true) i
        ltac:(change (concat (WriterValue.wdpieces (ck_crt_tree t) true)) with (WriterValue.wdoc (ck_crt_tree t) true); lia))
        as Hr.
      pose proof (cm_rqa_write t most HRQA) as Hm. unfold RQW in Hm.
      change (concat (WriterValue.wdpieces (ck_crt_tree t) true)) with (WriterValue.wdoc (ck_crt_tree t) true) in Hr.
      lia. }
    specialize (HOK3 i Hi Href Hreq). lia.
- destruct (cm_pjw_succ ok cw SIZE_MAXZ (ck_crt_tree t) true ltac:(lia) Hw1 Hfl) as (_ & Ewc).
  idtac.
  rewrite Ewc in Hread, Hcnt.
  rewrite (cm_ncalls_crt x t true Hin) in Hread.
  destruct (Hread ltac:(right; unfold SIZE_MAXZ; rewrite (cm_cnt_obj cnt t ms cset Et) in Htot; lia)) as (Er & Ec).
  rewrite (cm_read_crt x t true Hin) in Er. subst res.
  destruct Hres as (Erc & Hpos & Dback & EDx & Hback & Htb & Hfo).
  split; [exact Hs0|]. split; [exact Erc|]. split; [|split; [exact Hpos|]].
  + rewrite Hcnt, Ec, (cm_cnt_obj cnt t ms cset Et). unfold cw. lia.
  + exists (WriterApp.w_cap (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 cw SIZE_MAXZ)
      (WriterValue.wdpieces (ck_crt_tree t) true))), Dback. split; [exact EDx|]. split; [exact Hback|].
    split; [exact Htb|]. split; [exact Hfo|].
    (* pj_write's buffer: an unfailed run ends at grow_cap, the last of its realloc capacities *)
    rewrite (cm_wput_cap _ ok (WriterApp.w0 cw SIZE_MAXZ) eq_refl Hfl).
    unfold PresetReqAt.wcaps. rewrite <- (cm_crt_tree_copy_set ms), <- Et. symmetry. apply cl_last_grow.
Qed.

(* ---- image A': the two #102 cells and the read-only bytes lie in the low image ---- *)
Lemma cl_own_cell : 0 <= @pi_g_own_ran_out prh_img_A /\
  @pi_g_own_ran_out prh_img_A + Z.of_nat (@pi_gz_own_ran_out prh_img_A) <= kLowMemEnd.
Proof. split; vm_compute; discriminate. Qed.
Lemma cl_most_cell : 0 <= @pi_g_most prh_img_A /\ @pi_g_most prh_img_A + Z.of_nat (@pi_gz_most prh_img_A) <= kLowMemEnd.
Proof. split; vm_compute; discriminate. Qed.
Lemma cl_ro_low : forall a, in_roP SEGS RLO RHI a -> 0 <= a < kLowMemEnd.
Proof.
intros a Hro. apply pa_segs_low.
destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.

(* ---- more of the text's premises: the entry pre, the document's home, the entry memory's normal form ---- *)
Hypothesis HPRE : fpre B ARx STKC ly S Hp W regs mem md ch.
Hypothesis HTREE : ck_tree_ok ly S Lam W mem doc t D.
Hypothesis HMN : YAkMemnorm.memnorm SEGS mem.
(* the universe closure and the observed context (the text's), for the free calls' traces and pj_free's text *)
Hypothesis HCL : prh_univ_closure B CTX0.
Hypothesis HCTX : prh_ctx CTX0 F_check_round_trip (raZ regs :: spine ch).
(* THE CALLEE'S CONTRACT TEXT, at every float state (its walk is generic in fx; Crt102Tail.v takes it the same way):
   pj_free (+0x6d8) at n = DOC_D and the text's universe closure *)
Hypothesis PJFREE : forall fxq : YK11.FPState, PRH_FnPj.tpj_free_specX (fx := fxq) B ARx SK CTX0 DOC_D.

Lemma cl_stk : astk_ok STKC ly sp0.
Proof. destruct HPRE as ((_ & _ & _ & _ & _ & H & _) & _). exact H. Qed.
Lemma cl_sp0 : sp0 mod 16 = 0 /\ YM05.alloc_ceiling + STKC <= sp0 /\ sp0 <= 2 ^ 47.
Proof. pose proof cl_stk as (H1 & _ & H3 & H4 & H5 & H6 & _). lia. Qed.
(* s1, the realigned sp: 224 or 240 below sp0 *)
Lemma cl_sp1 : CRT_sp1 (regs := regs) mod 32 = 0 /\ sp0 - 240 <= CRT_sp1 (regs := regs) <= sp0 - 224.
Proof.
pose proof cl_sp0 as (H16 & _ & _). unfold CRT_sp1, CRT_FRAME, CRT_ALIGN.
pose proof (Z.mod_pos_bound (sp0 - 224) 32 ltac:(lia)). pose proof (Z.div_mod (sp0 - 224) 32 ltac:(lia)).
pose proof (Z.div_mod sp0 16 ltac:(lia)).
split; [rewrite Z_mod_mult; reflexivity | lia].
Qed.
(* the document's node lies in a live fake frame of the entry, below the ceiling *)
Lemma cl_doc_low : 4096 <= doc /\ doc + 56 <= YM05.alloc_ceiling.
Proof.
destruct HTREE as (_ & _ & _ & (_ & (cid & pos' & Hin & Hlo & Hhi) & _)).
destruct HPRE as ((HAR & _) & _).
destruct (frames_bounds_x _ _ _ LAWS ly S Hp W mem md cid pos' HAR Hin) as (F1 & F2 & _). lia.
Qed.
(* a harness block lies below the ceiling *)
Lemma cl_blk_low : forall lyc Sc Hpc (Wc : world SEGS) memc mdc Lamc peakc cntc failc ranc mostc ownc a k,
  ARx lyc Sc Hpc Wc memc mdc -> prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc -> In (a, k) Lamc ->
  0 <= k /\ 4096 + cf_head <= a /\ a + k <= YM05.alloc_ceiling.
Proof.
intros lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc mostc ownc a k HAR HL Hin.
destruct (prh_ledger_hblock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL Hin) as (Hk & Hb & _).
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HAR Hb) as (_ & B1 & B2 & _).
change (@cf_head CfParams_preset) with 16 in *.
assert (k + 16 <= req_size (k + 16)) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia). lia.
Qed.

(* ---- the document's node and the frame F are apart: doc lies in a fake frame of the entry, F is the frame the walk
   pushed on top (ajournal_x's frames Sc = (CRT_CID, pos) :: frames S), and the sep law keeps live frames apart ---- *)
Lemma cl_doc_F : forall lyc Sc Hpc (Wc : world SEGS) memc mdc kj pos {WS : list (list Z)},
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc memc mdc kj WS ->
  doc + 56 <= frame_addr lyc CRT_CID pos \/ frame_addr lyc CRT_CID pos + 512 <= doc.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos WS HJ.
pose proof HPRE as ((HAR & _) & _).
pose proof HTREE as (_ & _ & _ & (_ & (cid & pos' & Hfin & Hfa1 & Hfa2) & _)).
pose proof HJ as (HARc & Hly & _ & _ & _ & Hfrs & _).
destruct (alx_layout SEGS B ARx LAWS ly S Hp W mem md lyc HAR Hly) as (_ & Efa & _).
destruct (alx_sep SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc HARc) as (Hpw & _).
rewrite Hfrs in Hpw. cbn [app map] in Hpw.
apply pairwise_app_l in Hpw as (_ & (Hfa & _)).
assert (Hin' : In (frame_addr lyc cid pos', fs_frame_bytes cid)
  (map (fun f => (frame_addr lyc (fst f) (snd f), fs_frame_bytes (fst f))) (frames S))).
{ apply (in_map (fun f => (frame_addr lyc (fst f) (snd f), fs_frame_bytes (fst f))) _ (cid, pos')). exact Hfin. }
pose proof (proj1 (Forall_forall _ _) Hfa _ Hin') as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
rewrite (Efa cid pos'), (Efa CRT_CID pos) in Hd. rewrite (Efa CRT_CID pos).
change (fs_frame_bytes CRT_CID) with 512 in Hd. lia.
Qed.

(* ---- two different harness blocks of the ledger are apart (the ledger's NoDup heads, the blocks law, the sep law) ---- *)
Lemma cl_lam_apart : forall lyc Sc Hpc (Wc : world SEGS) memc mdc Lamc peakc cntc failc ranc mostc ownc a1 k1 a2 k2,
  ARx lyc Sc Hpc Wc memc mdc -> prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc ->
  In (a1, k1) Lamc -> In (a2, k2) Lamc -> (a1, k1) <> (a2, k2) -> a1 + k1 <= a2 \/ a2 + k2 <= a1.
Proof.
intros lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc mostc ownc a1 k1 a2 k2 HAR HL H1 H2 Hne.
pose proof HL as HL'. apply prh_ledger_nodup in HL'.
assert (Ha : a1 <> a2) by (intros ->; apply Hne; f_equal; exact (cl_nodup_fst _ _ _ _ HL' H1 H2)).
destruct (prh_ledger_hblock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL H1) as (Hk1 & Hb1 & _).
destruct (prh_ledger_hblock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL H2) as (Hk2 & Hb2 & _).
destruct (alx_sep SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc HAR) as (Hpw & _).
apply pairwise_app_l in Hpw as (Hpw & _).
pose proof (in_map (fun b => (fst b, req_size (snd b))) _ _ Hb1) as M1.
pose proof (in_map (fun b => (fst b, req_size (snd b))) _ _ Hb2) as M2. cbn [fst snd] in M1, M2.
change (@cf_head CfParams_preset) with 16 in *.
assert (R1 : k1 + 16 <= req_size (k1 + 16)) by (unfold req_size; destruct (Z.eqb_spec (k1 + 16) 0); lia).
assert (R2 : k2 + 16 <= req_size (k2 + 16)) by (unfold req_size; destruct (Z.eqb_spec (k2 + 16) 0); lia).
destruct (cl_pairwise_in _ _ _ _ Hpw M1 M2) as [E | [D12 | D21]].
- injection E as E _. lia.
- unfold zdisjoint in D12. cbn [fst snd] in D12. lia.
- unfold zdisjoint in D21. cbn [fst snd] in D21. lia.
Qed.

(* ======================================================================================================== *)
(* THE WALK'S STATE ACROSS A CALL WITH AN EMPTY FOOTPRINT (same): the journal keeps frame bytes and frame shadow
   (its frames clause), live blocks (its blocks clause), the image and the stack above the callee's window *)
Lemma cl_fb8 : forall cid, 56 <= fs_frame_bytes cid -> fs_frame_bytes cid mod 8 = 0.
Proof.
intros cid H. destruct (Z_lt_le_dec cid 0) as [Hn|Hn].
- exfalso. unfold fs_frame_bytes in H. replace cid with (- (- cid)) in H by lia.
  rewrite Z.shiftl_opp_r, Z.shiftr_div_pow2 in H by lia.
  assert (2 ^ 1 <= 2 ^ (- cid)) by (apply Z.pow_le_mono_r; lia).
  assert (64 / 2 ^ (- cid) <= 64 / 2) by (apply Z.div_le_compat_l; lia). change (64 / 2) with 32 in *. lia.
- rewrite fs_frame_bytes_eq by exact Hn. replace (64 * 2 ^ cid) with ((8 * 2 ^ cid) * 8) by lia.
  apply Z_mod_mult.
Qed.
Lemma cl_ra_frame_call : forall lyc Sc Hpc (Wc : world SEGS) memc mdc STK1 ly2 S2 Hp2 W2 mem2 md2 k1 cid0 pos0 p n,
  ARx lyc Sc Hpc Wc memc mdc ->
  ajournal_xR (SK := SK) SEGS B PST ARx RZW STK1 (CRT_sp1 (regs := regs)) [] lyc Sc Hpc Wc memc mdc []
    ly2 S2 Hp2 W2 mem2 md2 k1 ->
  In (cid0, pos0) (frames Sc) -> frame_addr lyc cid0 pos0 <= p -> p + n <= frame_addr lyc cid0 pos0 + fs_frame_bytes cid0 ->
  56 <= n ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF p n ->
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF p n.
Proof.
intros lyc Sc Hpc Wc memc mdc STK1 ly2 S2 Hp2 W2 mem2 md2 k1 cid0 pos0 p n HAR HJ1 Hin H1 H2 Hn Hr z Hz.
destruct (Hr z Hz) as (sv & Hs & Hok). exists sv. split; [|exact Hok].
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G4 & _).
destruct (alx_frames SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc cid0 pos0 HAR Hin) as (F32 & _).
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc cid0 pos0 HAR Hin) as (Fb1 & Fb2 & _).
pose proof (cl_fb8 cid0 ltac:(lia)) as H8.
rewrite (G4 cid0 pos0); [exact Hs | exact Hin | right | intros Hf; exact (inFP_nil _ Hf)].
unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd].
set (F0 := frame_addr lyc cid0 pos0) in *. set (fb := fs_frame_bytes cid0) in *.
assert (EF : F0 = 8 * (F0 / 8)) by (pose proof (Z.div_mod F0 8 ltac:(lia)); pose proof (Z.mod_divide F0 32 ltac:(lia)); lia).
assert (Eb : fb = 8 * (fb / 8)) by (pose proof (Z.div_mod fb 8 ltac:(lia)); lia).
assert (A1 : F0 / 8 <= z / 8) by (apply Z.div_le_mono; lia).
assert (A2 : z / 8 < F0 / 8 + fb / 8).
{ apply Z.div_lt_upper_bound; lia. }
lia.
Qed.
(* a word inside a frame of Sc across a call with an empty footprint *)
Lemma cl_rd_frame_call : forall lyc Sc Hpc (Wc : world SEGS) memc mdc STK1 ly2 S2 Hp2 W2 mem2 md2 k1 cid0 pos0 a v,
  ajournal_xR (SK := SK) SEGS B PST ARx RZW STK1 (CRT_sp1 (regs := regs)) [] lyc Sc Hpc Wc memc mdc []
    ly2 S2 Hp2 W2 mem2 md2 k1 ->
  In (cid0, pos0) (frames Sc) -> frame_addr lyc cid0 pos0 <= a -> a + 8 <= frame_addr lyc cid0 pos0 + fs_frame_bytes cid0 ->
  rd_u64 SEGS (mrestrict (w_H Wc) memc) a v -> rd_u64 SEGS (mrestrict (w_H W2) mem2) a v.
Proof.
intros lyc Sc Hpc Wc memc mdc STK1 ly2 S2 Hp2 W2 mem2 md2 k1 cid0 pos0 a v HJ1 Hin H1 H2 [Rv Vv].
split; [exact Rv|].
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G4 & _).
apply (ts_vm_av (w_H Wc) (w_H W2) memc mem2); [|exact Vv].
intros j Hj. apply (G4 cid0 pos0); [exact Hin | left; unfold in_zr, frame_rng; cbn [fst snd]; lia | intros Hf; exact (inFP_nil _ Hf)].
Qed.
Lemma cl_fo_call : forall lyc Sc Hpc Wc memc mdc (kj : Z) STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1
    Lamc peakc cntc ranc Lam2 peak2 cnt2 ran2 p d Dt Ft,
  ARx lyc Sc Hpc Wc memc mdc ->
  ajournal_xR (SK := SK) SEGS B PST ARx RZW STK1 (CRT_sp1 (regs := regs)) FP1 lyc Sc Hpc Wc memc mdc []
    ly2 S2 Hp2 W2 mem2 md2 k1 ->
  forall {mo1 ow1 mo2 ow2 : Z},
  prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc mo1 ow1 ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 SIZE_MAXZ ran2 mo2 ow2 ->
  (exists cid0 pos0, In (cid0, pos0) (frames Sc) /\ frame_addr lyc cid0 pos0 <= p /\
     p + 56 <= frame_addr lyc cid0 pos0 + fs_frame_bytes cid0) ->
  (forall bk, In bk Dt -> In bk Lamc) -> (forall bk, In bk Dt -> In bk Lam2) ->
  (forall a, inFP FP1 a -> ~ pj_footR p Dt a) ->
  PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) d p Dt Ft ->
  PRH_PjOrder.pj_foR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam2) d p Dt Ft.
Proof.
intros lyc Sc Hpc Wc memc mdc kj STK1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 Lamc peakc cntc ranc Lam2 peak2 cnt2 ran2 p d Dt Ft
  HARc HJ1 mo1 ow1 mo2 ow2 HLc HLED2 (cid & pos' & Hfin' & Hfa1 & Hfa2) HDL HDL2 HFPd HND.
pose proof HJ1 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & G2 & G3 & G4 & _).
apply (PRH_PjOrder.pj_foR_frame SEGS d (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) (prh_lin Lamc) (prh_lin Lam2)
  p Dt Ft HND); [intros x0 k0 H0; exact (HDL2 _ H0)|].
apply crt102rw_agree_of_aview. intros y Hy.
assert (HnFP : ~ inFP FP1 y) by (intros Hf; exact (HFPd y Hf Hy)).
assert (Hyc : (exists cid0 pos0, In (cid0, pos0) (frames Sc) /\
                 frame_addr lyc cid0 pos0 <= y < frame_addr lyc cid0 pos0 + fs_frame_bytes cid0) \/
              (exists p0 n0, In (p0, n0) (ablocks B lyc Sc) /\ In (p0, n0) (ablocks B ly2 S2) /\
                 p0 <= y < p0 + req_size n0)).
{ destruct Hy as [Hy | ((b & kb) & Hb & Hy)].
  - left. exists cid, pos'. split; [exact Hfin'|]. lia.
  - right. unfold pj_holdsR in Hy. cbn [fst snd] in Hy.
    destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc b kb _ _ HLc (HDL _ Hb)) as (Hk0 & Hab & _).
    destruct (prh_ledger_hblock B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 SIZE_MAXZ ran2 b kb _ _ HLED2 (HDL2 _ Hb)) as (_ & Hab2 & _).
    exists (b - cf_head), (kb + cf_head). split; [exact Hab|]. split; [exact Hab2|].
    change (@cf_head CfParams_preset) with 16 in *. pose proof (req_size_pos (kb + 16) ltac:(lia)). lia. }
assert (Himg : ~ in_img SEGS y).
{ destruct Hyc as [(cid0 & pos0 & Hin0 & Hy0) | (p0 & n0 & Hab & _ & Hy0)].
  - exact (proj2 (alx_client_img SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc y HARc
      (or_intror (or_introl (ex_intro _ cid0 (ex_intro _ pos0 (conj Hin0 Hy0))))))).
  - exact (proj2 (alx_client_img SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc y HARc
      (or_introl (ex_intro _ p0 (ex_intro _ n0 (conj Hab Hy0)))))). }
assert (Hyr : 0 <= y < 2 ^ 64).
{ destruct Hyc as [(cid0 & pos0 & Hin0 & Hy0) | (p0 & n0 & Hab & _ & Hy0)].
  - destruct (frames_bounds_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc cid0 pos0 HARc Hin0) as (? & ? & _).
    pose proof (YM05.alloc_ceiling_val). lia.
  - destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hab) as (_ & ? & ? & _).
    pose proof (YM05.alloc_ceiling_val). lia. }
split; [exact Hyr|]. split; [exact Himg|].
destruct Hyc as [(cid0 & pos0 & Hin0 & Hy0) | (p0 & n0 & Hab & Hab2 & Hy0)].
- apply (G4 cid0 pos0 y Hin0); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact HnFP].
- replace y with (p0 + (y - p0)) by lia. apply (G2 p0 n0 (y - p0) Hab Hab2); [lia|]. replace (p0 + (y - p0)) with y by lia.
  exact HnFP.
Qed.

(* ---- THE LIVE STATE ACROSS A CHANGE CONFINED TO A WINDOW OF THE REAL STACK below s1 + 0x70 (the walk's own spill
   stores, a runtime row's 2 * ESTACK window): everything crt_live reads lies below the ceiling (the statics, the
   blocks, the fake frames and their shadow), in the thirteen saved words [sp0 - 104, sp0), or at s1 + 0x70 ---- *)
Lemma cl_live_keep : forall lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' pos Dx Lamc peakc cntc ownc ranc lo hi
    {WS : list (list Z)},
  livea lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc memc' mdc' kj' WS ->
  YCbqGwild.wbudget [] (prh_wk F_check_round_trip) WS ->
  YM05.alloc_ceiling <= lo -> hi <= CRT_sp1 (regs := regs) + CRT_SP_F ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a) ->
  (forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS memc') ->
  livea lyc Sc Hpc Wc memc' mdc' kj' pos Dx Lamc peakc cntc ownc ranc.
Proof.
intros lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' pos Dx Lamc peakc cntc ownc ranc lo hi WS HL HJ' HB_HJ' Hlo Hhi Hav Hpr
  Hmn.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cl_sp0 as (H16 & Hsp0 & H47). pose proof cl_sp1 as (Hs32 & Hs1). unfold CRT_SP_F in Hhi.
assert (HSTKC : STKC = 27632) by (vm_compute; reflexivity).
assert (Hlow : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. apply Hav; lia. }
assert (Hhigh : forall a, CRT_sp1 (regs := regs) + 112 <= a < 2 ^ 64 ->
  aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. apply Hav; lia. }
assert (Hsh : forall z, SHADOW_OFF <= z < kHighMemBeg -> aview SEGS (w_H Wc) memc' z = aview SEGS (w_H Wc) memc z).
{ intros z Hz. apply Hlow. unfold SHADOW_OFF in Hz. lia. }
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ).
pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPl.
pose proof (crt_live_blocks_perm HL) as HPb.
pose proof (crt_live_dx_apart HL) as HDx.
pose proof (crt_live_saved HL) as HSV.
pose proof (crt_live_frame HL) as HFR.
pose proof (crt_live_fspill HL) as HSF.
pose proof (crt_live_copy_open HL) as HRC.
pose proof (crt_live_copy_hull HL) as HHC.
pose proof (crt_live_memnorm HL) as HMN0.
pose proof (crt_side_ledger HSD) as HLD.
pose proof (crt_side_peak HSD) as Hpk.
pose proof (crt_side_room HSD) as HRL.
pose proof (crt_side_arodata HSD) as HRO.
pose proof (crt_side_doc HSD) as HDOC.
pose proof (crt_side_doc_blocks HSD) as HDL.
pose proof HJ as (HARc & _).
refine {| crt_live_journal := ex_intro _ WS (conj HJ' HB_HJ'); crt_live_side := _; crt_live_lam_perm := HPl;
  crt_live_blocks_perm := HPb;
  crt_live_dx_apart := HDx; crt_live_saved := _; crt_live_frame := _; crt_live_fspill := _; crt_live_copy_open := _;
  crt_live_copy_hull := _; crt_live_memnorm := Hmn |}.
- (* crt_side *)
  refine {| crt_side_ledger := _; crt_side_peak := Hpk; crt_side_room := HRL; crt_side_arodata := _; crt_side_doc := _;
    crt_side_doc_blocks := HDL |}.
  + apply (prh_ledger_kept_aview B lyc Sc Hpc Wc memc); [exact HLD | | | auto | apply Permutation_refl].
    * intros a Ha. apply Hlow. pose proof (pst_in_img_A a Ha) as Hi. pose proof (pa_segs_low a Hi). lia.
    * intros a k i Hin Hi. destruct (cl_blk_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLD Hin) as (Hk & Ha & Hb).
      apply Hlow. change (@cf_head CfParams_preset) with 16 in *. lia.
  + intros a Hro Ho He. rewrite Hlow; [exact (HRO a Hro Ho He)|].
    pose proof (cl_ro_low a Hro). lia.
  + apply (pj_nodeR_frame SEGS t _ _ (prh_lin Lamc) doc D HDOC). apply cl_agree; [|exact Hpr].
    intros z [Hz | (b & Hb & Hz)]; apply Hlow.
    * pose proof cl_doc_low. lia.
    * destruct b as [a k]. unfold pj_holdsR in Hz. cbn [fst snd] in Hz.
      destruct (cl_blk_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLD (HDL _ Hb)) as (_ & Ha & Hk).
      change (@cf_head CfParams_preset) with 16 in *. lia.
- (* the saved words *)
  intros j Hj. apply (ts_vm_av (w_H Wc) (w_H Wc) memc memc'); [|exact (HSV j Hj)].
  intros i Hi. apply Hhigh. lia.
- (* the frame *)
  pose proof (crt_frame_listed HFR) as Hin.
  pose proof (crt_frame_flag_word HFR) as Hrd.
  pose proof (crt_frame_present HFR) as Hfp.
  refine {| crt_frame_listed := Hin; crt_frame_flag_word := _; crt_frame_present := _ |}.
  + destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hin) as (F1 & F2 & _).
    rewrite <- Hrd. apply ts_rdword_keep. intros j Hj. apply Hlow. change (fs_frame_bytes CRT_CID) with 512 in *. lia.
  + intros a Ha. apply Hpr. exact (Hfp a Ha).
- (* the frame's spill at s1 + 0x70 *)
  apply (ts_vm_av (w_H Wc) (w_H Wc) memc memc'); [|exact HSF].
  intros i Hi. apply Hhigh. unfold CRT_SP_F. lia.
- (* copy's open shadow *)
  destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc (crt_frame_listed HFR))
    as (F1 & F2 & _).
  change (fs_frame_bytes CRT_CID) with 512 in F2.
  apply (cl_ra_keep (aview SEGS (w_H Wc) memc)); [exact Hsh | unfold CRT_OFF_COPY; lia | unfold CRT_OFF_COPY; lia | exact HRC].
- destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc (crt_frame_listed HFR))
    as (F1 & F2 & _).
  change (fs_frame_bytes CRT_CID) with 512 in F2.
  apply (cl_hull_keep (aview SEGS (w_H Wc) memc)); [exact Hsh | unfold CRT_OFF_COPY; lia | unfold CRT_OFF_COPY; lia | lia | exact HHC].
Qed.

(* ---- the inline checks' shadow pointer `(k >> 3) + s10`, in both operand orders the compiler emits ---- *)
Lemma cl_sh_U : forall E nB nk k, bv_unsigned (ew E nB) = SHADOW_OFF -> bv_unsigned (ew E nk) = k -> 0 <= k < 2 ^ 47 ->
  U E (SAlu ALU_ADD (SOff nB 0) (SAlu ALU_SRL (SOff nk 0) (SLit 3))) = shadow_addr k /\
  U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff nk 0) (SLit 3)) (SOff nB 0)) = shadow_addr k.
Proof.
intros E nB nk k HB Hk Hr. rewrite !U_SAlu, !U_SOff, U_SLit, HB, Hk. rewrite !Z.add_0_r.
unfold zcanon, M64, zalu_raw, shadow_addr, SHADOW_OFF.
change (Z.land (3 mod 2 ^ 64) 63) with 3. rewrite !(Z.mod_small k) by lia. rewrite Z.shiftr_div_pow2 by lia.
change (2 ^ 3) with 8. assert (0 <= k / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
rewrite !(Z.mod_small (k / 8)) by lia. rewrite (Z.mod_small 2147450880) by lia.
split; rewrite Z.mod_small by lia; lia.
Qed.
(* the compiler's `xor` / `seqz` pair: 1 exactly when the two operands are equal *)
Lemma cl_eqflag : forall E a b, U E (SAlu ALU_SLTU (SAlu ALU_XOR a b) (SLit 1)) = (if U E a =? U E b then 1 else 0).
Proof.
intros E a b. pose proof (U_range E a) as Ra. pose proof (U_range E b) as Rb. unfold M64 in *.
rewrite !U_SAlu, !U_SLit. cbn [zalu_raw].
rewrite (zcanon_id 1) by (unfold M64; lia).
pose proof (Z_lxor_range (U E a) (U E b) Ra Rb) as Hx.
rewrite (zcanon_id (Z.lxor (U E a) (U E b))) by (unfold M64; exact Hx).
destruct (Z.eqb_spec (U E a) (U E b)) as [Eab|Nab].
- rewrite Eab, Z.lxor_nilpotent. cbn. reflexivity.
- assert (Z.lxor (U E a) (U E b) <> 0) by (intros H0; apply Z.lxor_eq in H0; contradiction).
  replace (Z.lxor (U E a) (U E b) <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn. reflexivity.
Qed.
(* the same, in the form prreg leaves (alu64 over the operand words) *)
Lemma cl_eqflag_w : forall (w1 w2 : word) a b, bv_unsigned w1 = a -> bv_unsigned w2 = b ->
  alu64 ALU_SLTU (alu64 ALU_XOR w1 w2) (Z_to_bv 64 1) = w64 (if a =? b then 1 else 0).
Proof.
intros w1 w2 a b H1 H2.
pose proof (bv_unsigned_in_range 64 w1) as R1. pose proof (bv_unsigned_in_range 64 w2) as R2.
change (bv_modulus 64) with (2 ^ 64) in R1, R2. rewrite H1 in R1. rewrite H2 in R2.
rewrite (ts_alu_w64 ALU_XOR w1 w2 a b H1 H2).
assert (Hr : 0 <= Z.lxor a b < 2 ^ 64) by (apply Z_lxor_range; lia).
assert (Hx : zalu64 ALU_XOR a b = Z.lxor a b).
{ unfold zalu64. rewrite (YP0m.zcanon_small a), (YP0m.zcanon_small b) by lia. cbn [zalu_raw].
  apply YP0m.zcanon_small. exact Hr. }
rewrite Hx.
rewrite (ts_alu_w64 ALU_SLTU (w64 (Z.lxor a b)) (Z_to_bv 64 1) (Z.lxor a b) 1)
  by (first [unfold w64; apply unsigned_lit_small; exact Hr | apply unsigned_lit_small; lia]).
f_equal. unfold zalu64. rewrite (YP0m.zcanon_small (Z.lxor a b)) by exact Hr. rewrite (YP0m.zcanon_small 1) by lia.
cbn [zalu_raw]. destruct (Z.eqb_spec a b) as [-> | Nab].
- rewrite Z.lxor_nilpotent. reflexivity.
- assert (Z.lxor a b <> 0) by (intros H0; apply Z.lxor_eq in H0; contradiction).
  replace (Z.lxor a b <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
(* the shadow pointer of an offset address, `((x + c) >> 3) + s10` *)
Lemma cl_sh_off : forall E nB nk k c, ew E nB = w64 SHADOW_OFF -> ew E nk = w64 k -> 0 <= k -> k + c < 2 ^ 47 -> 0 <= c ->
  U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff nk c) (SLit 3)) (SOff nB 0)) = shadow_addr (k + c).
Proof.
intros E nB nk k c HB Hk H0 H1 H2.
rewrite !U_SAlu, U_SLit, (U_atom_off E nk k c Hk), (U_atom E nB SHADOW_OFF HB) by (unfold SHADOW_OFF; lia).
unfold zcanon, M64, zalu_raw, shadow_addr, SHADOW_OFF.
change (Z.land (3 mod 2 ^ 64) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (0 <= (k + c) / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
rewrite ?(Z.mod_small ((k + c) / 8)) by lia.
rewrite ?(Z.mod_small 2147450880) by lia. rewrite ?Z.mod_small by lia. lia.
Qed.
(* the same in the form prreg leaves: alu64 over the words *)
Lemma cl_sh_w : forall (wb wk : word) k, bv_unsigned wb = SHADOW_OFF -> bv_unsigned wk = k -> 0 <= k < 2 ^ 47 ->
  alu64 ALU_ADD wb (alu64 ALU_SRL wk (Z_to_bv 64 3)) = w64 (shadow_addr k).
Proof.
intros wb wk k Hb Hk Hr.
rewrite (ts_alu_w64 ALU_SRL wk (Z_to_bv 64 3) k 3 Hk) by (apply unsigned_lit_small; lia).
assert (Hs : zalu64 ALU_SRL k 3 = k / 8).
{ unfold zalu64. rewrite (YP0m.zcanon_small k), (YP0m.zcanon_small 3) by lia. cbn [zalu_raw].
  change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  apply YP0m.zcanon_small. split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. }
rewrite Hs.
assert (0 <= k / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
rewrite (ts_alu_w64 ALU_ADD wb (w64 (k / 8)) SHADOW_OFF (k / 8) Hb) by (unfold w64; apply unsigned_lit_small; lia).
f_equal. unfold zalu64. rewrite (YP0m.zcanon_small SHADOW_OFF), (YP0m.zcanon_small (k / 8)) by (unfold SHADOW_OFF; lia).
cbn [zalu_raw]. unfold shadow_addr, SHADOW_OFF. apply YP0m.zcanon_small. lia.
Qed.
Lemma cl_add_w : forall (w1 w2 : word) a b, bv_unsigned w1 = a -> bv_unsigned w2 = b -> 0 <= a -> 0 <= b -> a + b < 2 ^ 64 ->
  alu64 ALU_ADD w1 w2 = w64 (a + b).
Proof.
intros w1 w2 a b H1 H2 Ha Hb Hab. rewrite (ts_alu_w64 ALU_ADD w1 w2 a b H1 H2). f_equal.
unfold zalu64. rewrite (YP0m.zcanon_small a), (YP0m.zcanon_small b) by lia. cbn [zalu_raw].
apply YP0m.zcanon_small. lia.
Qed.
(* the MOD_AT literal, as the run leaves it (auipc / addi: A_OBJ 2 plus its offset) *)
Lemma cl_modat_den : forall E, ew E 243 = Z_to_bv 64 (VAL 243) ->
  sv_denot E (SOff 243 69824) = Z_to_bv 64 CRT_MOD_AT_A.
Proof. intros E HE. apply bv_eq. rewrite denot_SOff, HE. vm_compute. reflexivity. Qed.
Lemma cl_lit_rng : 4096 <= CRT_MOD_AT_A /\ CRT_MOD_AT_A + 11 <= 2 ^ 31 /\ 4096 <= CRT_STAMP_A /\ CRT_STAMP_A + 21 <= 2 ^ 31.
Proof. repeat split; vm_compute; first [discriminate | reflexivity]. Qed.

(* ---- A strcmp FROM check_round_trip AT THE REALIGNED sp: YGcallMxmn.v's aj_strcmp_at_xrom over the libc row
   STRCMP. The live state's journal is the call's; the continuation receives the callee's journal (the same
   allocator state), the kept registers, the result and its meaning, and the memory kept outside strcmp's
   2 * ESTACK window below s1. ---- *)
Lemma cl_strcmp_call : forall (fxk : YK11.FPState) Wc E ss ms mdc lyc Sc Hpc kj pos Dx Lamc peakc cntc ownc ranc
    (off px py kx ky : Z),
  @st_ok SEGS fxk E ss (restrict (w_H Wc) ms) -> ss_resv ss = None -> ss_pc ss = SIGMA AS___wrap_strcmp ->
  livea lyc Sc Hpc Wc (ms_mem ms) mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  crt_bregs (regs := regs) (ms_regs ms) (frame_addr lyc CRT_CID pos) ->
  getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRT_PC_A + off)) -> 0 <= off < 2048 -> off mod 2 = 0 ->
  getr (ms_regs ms) 10 = w64 px -> getr (ms_regs ms) 11 = w64 py ->
  cl_sarg Wc (ms_mem ms) px kx -> cl_sarg Wc (ms_mem ms) py ky ->
  (forall regs2 mem2 md2 (v : word) WS2,
     AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc mem2 md2 kj WS2 ->
     YCbqGwild.wbudget [] (prh_wk F_check_round_trip) WS2 ->
     aregs_preserved (ms_regs ms) regs2 -> getr regs2 10 = v ->
     (v = w64 0 <-> kx = ky /\ forall i, 0 <= i < kx ->
        aview SEGS (w_H Wc) (ms_mem ms) (px + i) = aview SEGS (w_H Wc) (ms_mem ms) (py + i)) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (CRT_sp1 (regs := regs) - 2 * ESTACK <= a < CRT_sp1 (regs := regs)) ->
        aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) (ms_mem ms) a) ->
     (forall a, apresent (w_H Wc) (ms_mem ms) a -> apresent (w_H Wc) mem2 a) ->
     (YAkMemnorm.memnorm SEGS (ms_mem ms) -> YAkMemnorm.memnorm SEGS mem2) ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc
       (mkCfg (@YK11.mkst fxk regs2 (Z_to_bv 64 (BASE + (CRT_PC_A + off))) mem2 (YK11.seg_rom SEGS)) md2)
       QFa) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg ms mdc) QFa.
Proof.
intros fxk Wc E ss ms mdc lyc Sc Hpc kj pos Dx Lamc peakc cntc ownc ranc off px py kx ky HS Hrv Hpcs HL HBR Hra Hoff
  Hoff2 X10 X11 SX SY HK.
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_side HL) as HSD.
pose proof (crt_side_arodata HSD) as HRO.
pose proof (crt_bregs_sp HBR) as R2.
pose proof (crt_bregs_gp HBR) as R3.
pose proof (crt_bregs_tp HBR) as R4.
pose proof (crt_bregs_s0 HBR) as R8.
pose proof (crt_bregs_s1 HBR) as R9.
pose proof (crt_bregs_s2 HBR) as R18.
pose proof (crt_bregs_s4 HBR) as R20.
pose proof (crt_bregs_s3 HBR) as R19.
pose proof (crt_bregs_s7 HBR) as R23.
pose proof (crt_bregs_s10 HBR) as R26.
pose proof (crt_bregs_s11 HBR) as R27.
pose proof HPRE as ((HAR & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & HRO0 & Hhi & Hrac).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof YM05.alloc_ceiling_lt as Hc47.
pose proof cl_sp0 as (Hs16 & Hsc & Hs47). pose proof cl_sp1 as (Hs32 & Hs1).
assert (HSTKC : STKC = 27632) by (vm_compute; reflexivity).
destruct (crt102rw_ret off Hoff Hoff2) as (Hr1 & Hr2 & Hr3).
set (sp1 := CRT_sp1 (regs := regs)) in *.
set (o := sp1 - sp0).
assert (Hsp1 : spZ (ms_regs ms) = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hspz : spZ (ms_regs ms) = sp0 + o) by (unfold o; lia).
assert (Hes : ESTACK = 4096) by reflexivity.
destruct SX as (X4 & Xk0 & Xk32 & Xce & Xfb & Xvis & Xam & Xra & Xhv & Xtl).
destruct SY as (Y4 & Yk0 & Yk32 & Yce & Yfb & Yvis & Yam & Yra & Yhv & Ytl).
rewrite (st_ok_restrict_mkst SEGS _ _ _ _ HS Hrv). cbn [ss_pc setpc]. rewrite Hpcs.
(* strcmp's rule (the engine's R form YGcallMxmn.aj_strcmp_at_xromR at RZW) is over ajournal_xR: the journal rebased to the current depot
   (YCbqGwild.ajournal_xw_rebaseR) and stepped back to its budget after it (YCbqGwild.ajournal_xw_unbase0R); the libc
   row's plain SRr lifted to the walk's SRr' (YA0nH.SRr_SRr') *)
pose proof (crt_jw_wild B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Hinc.
pose proof HJ as HJr. apply YCbqGwild.ajournal_xw_rebaseR in HJr.
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ apply YA0nH.SRr_SRr'.
  refine (@YGcallMxmn.aj_strcmp_at_xromR fxk rc SK SEGS B PST ARx RLO RHI cf_head LAWS (@pa_segs_low rc A_prog_listing PA)
    RZW (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)
    (SIGMA AS___wrap_strcmp) (STRCMP fxk) Wc (ms_regs ms) (ms_mem ms) STKC sp0 [] ly (set_depot (st_depot Sc) S) Hp W
    mem md [(CRT_CID, pos)]
    lyc Sc Hpc mdc kj px py kx ky o (getr (ms_regs ms) 1) HJr X10 X11 _ _ Xk0 Xk32 _ Yk0 Yk32
    _ Hspz _ _ _ _ _ eq_refl _ Xfb Yfb _ _ _ _ _ _ Xra Xhv Yra Yhv Xtl Ytl HRO).
  all: try (unfold o in *; lia).
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - rewrite Hra. apply (ret_ok_codeptr_v (PI := PA)); [exact Hr3 | exact Hr2].
  - intros a Ha. split; [apply Xvis; lia | rewrite Hspz; unfold o; lia].
  - intros a Ha. split; [apply Yvis; lia | rewrite Hspz; unfold o; lia].
  - first [unfold YGcallMx.amem_range8 | unfold YGcfStr.amem_range8]. exact Xam.
  - first [unfold YGcallMx.amem_range8 | unfold YGcfStr.amem_range8]. exact Yam. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP & Hv & Hcmp & Hfr & Hpr2 & Hmn).
eapply YCbqGwild.ajournal_xw_unbase0R in HJ2; [|exact Hinc].
replace (sp0 + o) with sp1 in Hfr by (unfold o; lia).
rewrite Hra. exact (HK regs2 mem2 md2 v WS_HJ HJ2 HB_HJ HP Hv Hcmp Hfr Hpr2 Hmn).
Qed.

(* ---- an object node, unfolded: its header words and its members over the kids / keys arrays ---- *)
Lemma cl_node_obj : forall (m : word -> option byte) lblk p ms D',
  pj_nodeR SEGS m lblk p (PjTree.JObj ms) D' ->
  exists num kids keys cap Di,
    NoDup D' /\ pj_apartR D' p /\
    pj_hdrR SEGS m p 6 num 0 kids keys (Z.of_nat (length ms)) cap /\ Z.of_nat (length ms) <= cap /\
    (cap = 0 /\ kids = 0 /\ keys = 0 \/ 0 < cap /\ lblk kids (56 * cap) /\ lblk keys (8 * cap)) /\
    D' = (if cap =? 0 then [] else [(kids, 56 * cap); (keys, 8 * cap)]) ++ Di /\
    pj_memsR SEGS m lblk (pj_nodeR SEGS m lblk) kids keys ms Di.
Proof.
intros m lblk p ms D' (Hnd & Hap & num & str & kids & keys & n & cap & Hh & -> & -> & Hnc & Hcap & Di & ED & Hm).
exists num, kids, keys, cap, Di. auto 10.
Qed.

(* ---- member i of an object node in the walk's blocks: its key slot (addressable), its key string (a strcmp
   argument) in a block of Lamc, and the key array's bounds ---- *)
Lemma cl_obj_key : forall lyc Sc Hpc (Wc : world SEGS) memc mdc Lamc peakc cntc failc ranc mostc ownc dp ms0 Dd keys i nm u,
  ARx lyc Sc Hpc Wc memc mdc -> prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc ->
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) dp (PjTree.JObj ms0) Dd -> (forall bk, In bk Dd -> In bk Lamc) ->
  rd_u64 SEGS (mrestrict (w_H Wc) memc) (dp + 32) keys -> nth_error ms0 i = Some (nm, u) ->
  exists kp kb, rd_u64 SEGS (mrestrict (w_H Wc) memc) (keys + 8 * Z.of_nat i) kp /\
    pj_cstrR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) kp kb nm /\ In (kp, kb) Lamc /\
    cl_sarg Wc memc kp (Z.of_nat (length nm)) /\
    range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (keys + 8 * Z.of_nat i) 8 /\
    4096 <= keys /\ keys mod 8 = 0 /\ keys + 8 * Z.of_nat (length ms0) <= YM05.alloc_ceiling /\
    exists kc, In (keys, kc) Dd /\ In (keys, kc) Lamc /\ 8 * Z.of_nat (length ms0) <= kc.
Proof.
intros lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc mostc ownc dp ms0 Dd keys i nm u HAR HL HN HDL Hk Hi.
destruct (cl_node_obj _ _ _ _ _ HN) as (num & kids & keys' & dcap & Di & _ & _ & Hhdr & Hncap & Hcap & EDi & Hmem).
pose proof Hhdr as (_ & _ & _ & _ & _ & Hk' & _).
assert (Ek : keys' = keys) by (destruct Hk as [R1 V1]; destruct Hk' as [R2 V2]; exact (cl_vm_det _ _ _ _ _ V2 V1 R2 R1)).
subst keys'.
assert (Hlt : (i < length ms0)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
destruct Hcap as [(-> & _ & _) | (Hc0 & _ & Hky)]; [lia|].
assert (HDi : forall bk, In bk Di -> In bk Lamc).
{ intros bk Hb. apply HDL. rewrite EDi. apply in_or_app. right. exact Hb. }
destruct (cl_mems_nth _ _ _ _ _ _ _ _ _ _ Hmem Hi) as (kp & kb & D1 & Hkp & Hcs & Hin & _ & _).
pose proof Hcs as (_ & Hkb & Hk32 & Hby).
destruct (cl_hblk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HL Hky) as (_ & H16 & _ & Hce & H4 & Hbs & _).
exists kp, kb. split; [exact Hkp|]. split; [exact Hcs|]. split; [exact (HDi _ Hin)|].
split; [exact (cl_sarg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HL (HDi _ Hin) Hby Hkb Hk32)|].
split; [exact (block_shadow_range _ SHADOW_OFF keys (8 * dcap) (keys + 8 * Z.of_nat i) 8 Hbs ltac:(lia) ltac:(lia))|].
split; [lia|]. split; [lia|]. split; [lia|].
exists (8 * dcap). split; [|split; [exact Hky | lia]].
rewrite EDi. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq dcap 0)) by lia. right. left. reflexivity.
Qed.

(* ---- L0's entry state (the run starts after the deduction: s6 = 0) ---- *)
Lemma cl_L0_entry : forall (fxk : YK11.FPState) (Wc : world SEGS) memc rg n keys F cs,
  conds_ok (TE regs rg [w64 n; w64 keys]) cs ->
  getr rg 9 = w64 (CRT_sp1 (regs := regs)) -> getr rg 21 = w64 doc -> getr rg 26 = w64 SHADOW_OFF ->
  getr rg 22 = w64 0 -> getr rg 27 = w64 F -> 0 <= F -> F + 512 <= 2 ^ 47 ->
  crt_spill (regs := regs) Wc memc CRT_SP_BACK (F + CRT_OFF_BACK) ->
  2 ^ 46 <= CRT_sp1 (regs := regs) -> CRT_sp1 (regs := regs) + 96 <= 2 ^ 47 -> CRT_sp1 (regs := regs) mod 32 = 0 ->
  4096 <= doc /\ doc + 64 <= CRT_sp1 (regs := regs) -> doc mod 8 = 0 -> 0 <= n <= 2 ^ 54 -> 0 <= keys <= 2 ^ 47 ->
  (forall a, CRT_sp1 (regs := regs) + 24 <= a < CRT_sp1 (regs := regs) + 88 -> apresent (w_H Wc) memc a) ->
  crt_spill (regs := regs) Wc memc CRT_SP_SHN (shadow_addr (doc + PJ_OFF_N)) ->
  crt_spill (regs := regs) Wc memc CRT_SP_PN (doc + PJ_OFF_N) ->
  crt_spill (regs := regs) Wc memc CRT_SP_N n ->
  rd_u64 SEGS (mrestrict (w_H Wc) memc) (doc + 32) keys -> rd_u64 SEGS (mrestrict (w_H Wc) memc) (doc + 40) n ->
  st_ok_pi SEGS VAL (TE regs rg [w64 n; w64 keys]) (ss_L0 cs)
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_A + CRT_L0_OFF))) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS CL_Bx [] (TE regs rg [w64 n; w64 keys]) (mrestrict (w_H Wc) memc).
Proof.
intros fxk Wc memc rg n keys F cs Hcs R9 R21 R26 R22 R27 HF0 HF1 VBK H1 H2 H3 H4 H5 H6 H7 HP VSH VPN VN [_ VK] [_ VNN].
unfold crt_spill, CRT_SP_SHN, CRT_SP_PN, CRT_SP_N, CRT_SP_BACK, CRT_OFF_BACK, PJ_OFF_N in *.
unfold crt_spill, CRT_SP_SHN, CRT_SP_PN, CRT_SP_N, PJ_OFF_N in *.
set (sp1 := CRT_sp1 (regs := regs)) in *.
set (E := TE regs rg [w64 n; w64 keys]).
assert (X9 : bv_unsigned (ew E (xr 9)) = sp1).
{ unfold E, xr. rewrite (te_cur regs rg _ 9%bv 9) by reflexivity. rewrite R9. apply unsigned_lit_small. lia. }
assert (X21 : bv_unsigned (ew E (xr 21)) = doc).
{ unfold E, xr. rewrite (te_cur regs rg _ 21%bv 21) by reflexivity. rewrite R21. apply unsigned_lit_small. lia. }
assert (X26 : bv_unsigned (ew E (xr 26)) = SHADOW_OFF).
{ unfold E, xr. rewrite (te_cur regs rg _ 26%bv 26) by reflexivity. rewrite R26. apply unsigned_lit_small.
  unfold SHADOW_OFF. lia. }
assert (E64 : ew E 64 = w64 n) by exact (te_more_lt regs rg [w64 n; w64 keys] 0 ltac:(lia)).
assert (E65 : ew E 65 = w64 keys) by exact (te_more_lt regs rg [w64 n; w64 keys] 1 ltac:(lia)).
assert (W21 : ew E (xr 21) = w64 doc).
{ unfold E, xr. rewrite (te_cur regs rg _ 21%bv 21) by reflexivity. exact R21. }
assert (W26 : ew E (xr 26) = w64 SHADOW_OFF).
{ unfold E, xr. rewrite (te_cur regs rg _ 26%bv 26) by reflexivity. exact R26. }
assert (W27 : ew E (xr 27) = w64 F).
{ unfold E, xr. rewrite (te_cur regs rg _ 27%bv 27) by reflexivity. exact R27. }
split; [|unfold sh_ok; apply Forall_nil].
apply ts_st_ok.
all: try change (TE regs rg [w64 n; w64 keys]) with E.
- apply YI04.regs_ok_pin; [apply te_regs_ok | intros X; discriminate X | rewrite R22; reflexivity].
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
  + apply (ts_rok E _ (xr 9) sp1); [exact X9 | lia | lia | |].
    { intros o Ho. apply (apresent_writable SEGS). apply HP. lia. }
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (ts_chunk E _ _ 56 8 (SOff (xr 27) 32) (F + 32)); [| cbn; lia | cbn; lia | exact VBK].
      rewrite denot_lit_U, (U_atom_off E (xr 27) F 32 W27) by lia. reflexivity.
    * apply (ts_chunk E _ _ 72 8 (cl_sh (SOff (xr 21) 40)) (shadow_addr (doc + 40)));
        [| unfold shadow_addr, SHADOW_OFF; cbn; lia | cbn; lia | exact VSH].
      rewrite denot_lit_U. f_equal. unfold cl_sh.
      rewrite U_SAlu, U_srl3, (U_atom_off E (xr 21) doc 40 W21) by lia.
      rewrite (U_atom_off E (xr 26) SHADOW_OFF 0 W26) by (unfold SHADOW_OFF; lia).
      cbn [zalu_raw]. unfold zcanon, M64, shadow_addr, SHADOW_OFF. rewrite Z.add_0_r.
      assert (0 <= (doc + 40) / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
      rewrite Z.add_comm. apply Z.mod_small. lia.
    * apply (ts_chunk E _ _ 80 8 (SOff (xr 21) 40) (doc + 40)); [| cbn; lia | cbn; lia | exact VPN].
      rewrite denot_lit_U, (U_atom_off E (xr 21) doc 40 W21) by lia. reflexivity.
    * apply (ts_chunk E _ _ 88 8 (SOff 64 0) n); [| cbn; lia | cbn; lia | exact VN].
      rewrite denot_lit_U, (U_atom_off E 64 n 0 E64) by lia. rewrite Z.add_0_r. reflexivity.
  + apply (ts_rok E _ (xr 21) doc); [exact X21 | lia | lia | intros o Ho; lia |].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (ts_chunk E _ _ 32 8 (SOff 65 0) keys); [| cbn; lia | cbn; lia | exact VK].
      rewrite denot_lit_U, (U_atom_off E 65 keys 0 E65) by lia. rewrite Z.add_0_r. reflexivity.
    * apply (ts_chunk E _ _ 40 8 (SOff 64 0) n); [| cbn; lia | cbn; lia | exact VNN].
      rewrite denot_lit_U, (U_atom_off E 64 n 0 E64) by lia. rewrite Z.add_0_r. reflexivity.
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !ts_bv_some. rewrite X9, X21.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact Hcs | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X9, X21, X26.
  rewrite E64, E65. unfold w64. rewrite !unsigned_lit_small by lia.
  change (2 ^ 5) with 32. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
  unfold SHADOW_OFF. repeat split; lia.
Qed.

(* ======================================================================================================== *)
(* THE STATE OF THE REWRITE'S TAIL, from L0 on (after the new:740 deduction): the live state holds copy's blocks Dc,
   the text block (saved, cap) and the read-back's blocks Dback; copy holds the rewritten tree, back its read-back;
   the count is the whole function's; the two locals' windows and doc's root are addressable. *)
Definition CL_SP_KSH : Z := 40.     (* 0x28(s1): the shadow pointer of &doc->kids (L2 on) *)
Definition CL_SP_P : Z := 48.       (* 0x30(s1): &doc->keys (L0 .. L2), &doc->kids (L2 on) *)
Definition CL_SP_LIT : Z := 64.     (* 0x40(s1): the MOD_AT literal (L1), back.keys + 8 i (L3) *)
Definition cl_rw (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Dc Lamc : list (Z * Z)) (peakc cset saved cap : Z)
  (Dback : list (Z * Z)) (ms : list (list Z * PjTree.jv)) : Prop :=
  t = PjTree.JObj ms /\ frm_zero (@YK11.fp_csr fxk) /\ fregs_kept_x fx fxk /\
  livea lyc Sc Hpc Wc memc mdc kj pos (Dback ++ (saved, cap) :: Dc) Lamc peakc (cnt + ck_crt_count t cset) 0 0 /\
  0 <= cset <= 3 /\ (In ck_MOD_AT (map fst ms) -> cset = 0) /\ saved <> 0 /\
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) tc Dc /\
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) tc Dback /\
  doc mod 8 = 0 /\ range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF doc 56 /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) 56 /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (frame_addr lyc CRT_CID pos + CRT_OFF_V) 56 /\
  (* the room position: the loops make no allocator event, so L0's suffix stands up to the exit *)
  posa Sc (crt_evs_L0 ms) /\
  (* the J field's copy facts and the two frees' event keys, carried from L0 unchanged *)
  pj_fdR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc /\
  Permutation (map (fun b => snd b + cf_head) Dc) (PresetReqAtNoMiss.tblk (crt_tree_J (t := t))) /\
  (exists Fc, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D
     (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc Fc /\
   map (fun b => snd b + cf_head) Fc = PresetReqAt.fo (crt_tree_J (t := t))) /\
  (PjTree.depth (crt_tree_J (t := t)) <= DOC_D)%nat /\
  Permutation (map (fun b => snd b + cf_head) Dback) (PresetReqAtNoMiss.tblk tc) /\
  (* back's free order (the loops touch neither back nor the allocator; the exit's pj_free (&back) reads it) *)
  (exists Fb, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D
     (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) Dback Fb /\
   map (fun b => snd b + cf_head) Fb = PresetReqAt.fo tc) /\
  cap = last (PresetReqAt.wcaps (PresetReqAt.copy_set ms) true) 0.
(* the two spills every boundary from L1 on reads: &back at 0x38(s1), saved at 0x18(s1) *)
Definition cl_sp2 (Wc : world SEGS) (memc : word -> option byte) (F saved : Z) : Prop :=
  crt_spill (regs := regs) Wc memc CRT_SP_BACK (F + CRT_OFF_BACK) /\ crt_spill (regs := regs) Wc memc CRT_SP_SAVED saved.

(* a footprint of the walk's trees lies below the ceiling: the node in the fake frame, the blocks in Lamc *)
Lemma cl_foot_low : forall lyc Sc Hpc (Wc : world SEGS) memc mdc Lamc peakc cntc failc ranc mostc ownc p D' z,
  ARx lyc Sc Hpc Wc memc mdc -> prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc ->
  (forall b, In b D' -> In b Lamc) -> 0 <= p -> p + 56 <= YM05.alloc_ceiling ->
  pj_footR p D' z -> 0 <= z < YM05.alloc_ceiling.
Proof.
intros lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc mostc ownc p D' z HAR HL HD Hp0 Hp1 [Hz | (b & Hb & Hz)]; [lia|].
destruct b as [a k]. unfold pj_holdsR in Hz. cbn [fst snd] in Hz.
destruct (cl_blk_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HL (HD _ Hb)) as (_ & Ha & Hk).
change (@cf_head CfParams_preset) with 16 in *. lia.
Qed.
Lemma cl_node_keep : forall lyc Sc Hpc (Wc : world SEGS) memc memc' mdc Lamc peakc cntc failc ranc mostc ownc p tt D',
  ARx lyc Sc Hpc Wc memc mdc -> prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc ->
  (forall b, In b D' -> In b Lamc) -> 0 <= p -> p + 56 <= YM05.alloc_ceiling ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a) ->
  (forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) p tt D' ->
  pj_nodeR SEGS (mrestrict (w_H Wc) memc') (prh_lin Lamc) p tt D'.
Proof.
intros lyc Sc Hpc Wc memc memc' mdc Lamc peakc cntc failc ranc mostc ownc p tt D' HAR HL HD Hp0 Hp1 Hlow Hpr HN.
apply (pj_nodeR_frame SEGS tt _ _ (prh_lin Lamc) p D' HN). apply cl_agree; [|exact Hpr].
intros z Hz. apply Hlow. exact (cl_foot_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HL HD Hp0 Hp1 Hz).
Qed.

(* ---- cl_rw across a change confined to a window of the real stack below s1 + 0x70 ---- *)
Lemma cl_rw_keep : forall fxk lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' pos Dc Lamc peakc cset saved cap Dback ms lo hi
    {WS : list (list Z)},
  cl_rw fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms ->
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc memc' mdc' kj' WS ->
  YCbqGwild.wbudget [] (prh_wk F_check_round_trip) WS ->
  YM05.alloc_ceiling <= lo -> hi <= CRT_sp1 (regs := regs) + CRT_SP_F ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a) ->
  (forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS memc') ->
  cl_rw fxk lyc Sc Hpc Wc memc' mdc' kj' pos Dc Lamc peakc cset saved cap Dback ms.
Proof.
intros fxk lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' pos Dc Lamc peakc cset saved cap Dback ms lo hi WS HR HJ' HB_HJ' Hlo
  Hhi Hav Hpr Hmn.
destruct HR as (Et & HFZ & HFK & HL & Hcs & Hcin & Hsv & Hcopy & Hback & Hd8 & Hrad & Hrab & Hrav & Hpos & Hfd & HPcp
  & (Fc & Hfoc & Efoc) & Hdep & Hpb & (Fb & Hfob & Efob) & Ecap).
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ).
pose proof (crt_live_side HL) as Hrec1.
pose proof (crt_side_ledger Hrec1) as HLD.
pose proof (crt_live_lam_perm HL) as HPl.
pose proof (crt_live_frame HL) as HFRM.
pose proof HJ as (HARc & _).
pose proof (cl_live_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL HJ' HB_HJ' Hlo Hhi Hav Hpr Hmn) as HL'.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hlow : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. apply Hav; lia. }
assert (Hsh : forall z, SHADOW_OFF <= z < kHighMemBeg -> aview SEGS (w_H Wc) memc' z = aview SEGS (w_H Wc) memc z).
{ intros z Hz. apply Hlow. unfold SHADOW_OFF in Hz. lia. }
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc (crt_frame_listed HFRM))
  as (Fb1 & Fb2 & _).
change (fs_frame_bytes CRT_CID) with 512 in Fb2.
assert (HinL : forall b, In b (Dback ++ (saved, cap) :: Dc) -> In b Lamc).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym HPl)). apply in_or_app. left. exact Hb. }
pose proof cl_doc_low as (Hdl0 & Hdl1).
refine (conj Et (conj HFZ (conj HFK (conj HL' (conj Hcs (conj Hcin (conj Hsv (conj _ (conj _ (conj Hd8 (conj _ (conj _ (conj _ (conj Hpos (conj _ (conj HPcp (conj (ex_intro _ Fc (conj _ Efoc)) (conj Hdep (conj Hpb (conj (ex_intro _ Fb (conj _ Efob)) Ecap)))))))))))))))))))).
- apply (cl_node_keep _ _ _ _ memc memc' _ _ _ _ _ _ _ _ _ _ _ HARc HLD); [| unfold CRT_OFF_COPY; lia | unfold CRT_OFF_COPY; lia
    | exact Hlow | exact Hpr | exact Hcopy].
  intros b Hb. apply HinL. apply in_or_app. right. right. exact Hb.
- apply (cl_node_keep _ _ _ _ memc memc' _ _ _ _ _ _ _ _ _ _ _ HARc HLD); [| unfold CRT_OFF_BACK; lia | unfold CRT_OFF_BACK; lia
    | exact Hlow | exact Hpr | exact Hback].
  intros b Hb. apply HinL. apply in_or_app. left. exact Hb.
- apply (cl_ra_keep (aview SEGS (w_H Wc) memc)); [exact Hsh | lia | lia | exact Hrad].
- apply (cl_ra_keep (aview SEGS (w_H Wc) memc)); [exact Hsh | unfold CRT_OFF_BACK; lia | unfold CRT_OFF_BACK; lia | exact Hrab].
- apply (cl_ra_keep (aview SEGS (w_H Wc) memc)); [exact Hsh | unfold CRT_OFF_V; lia | unfold CRT_OFF_V; lia | exact Hrav].
- (* copy's freeable shape, framed over its footprint below the ceiling *)
  apply (crt102rw_fdR_frame SEGS DOC_D _ _ (prh_lin Lamc) _ Dc Hfd). apply cl_agree; [|exact Hpr].
  intros z Hz. apply Hlow.
  apply (cl_foot_low _ _ _ _ _ _ _ _ _ _ _ _ _ (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc z HARc HLD);
    [| unfold CRT_OFF_COPY; lia | unfold CRT_OFF_COPY; lia | exact Hz].
  intros b Hb. apply HinL. apply in_or_app. right. right. exact Hb.
- (* copy's free order, framed likewise *)
  apply (PRH_PjOrder.pj_foR_frame SEGS DOC_D _ _ (prh_lin Lamc) (prh_lin Lamc) _ Dc Fc Hfoc
    (PRH_PjOrder.pj_foR_lblk SEGS _ _ _ _ _ _ Hfoc)).
  apply cl_agree; [|exact Hpr].
  intros z Hz. apply Hlow.
  apply (cl_foot_low _ _ _ _ _ _ _ _ _ _ _ _ _ (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc z HARc HLD);
    [| unfold CRT_OFF_COPY; lia | unfold CRT_OFF_COPY; lia | exact Hz].
  intros b Hb. apply HinL. apply in_or_app. right. right. exact Hb.
- (* back's free order, framed over its footprint below the ceiling *)
  apply (PRH_PjOrder.pj_foR_frame SEGS DOC_D _ _ (prh_lin Lamc) (prh_lin Lamc) _ Dback Fb Hfob
    (PRH_PjOrder.pj_foR_lblk SEGS _ _ _ _ _ _ Hfob)).
  apply cl_agree; [|exact Hpr].
  intros z Hz. apply Hlow.
  apply (cl_foot_low _ _ _ _ _ _ _ _ _ _ _ _ _ (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) Dback z HARc HLD);
    [| unfold CRT_OFF_BACK; lia | unfold CRT_OFF_BACK; lia | exact Hz].
  intros b Hb. apply HinL. apply in_or_app. left. exact Hb.
Qed.

(* ---- the register snapshot across a run that keeps its registers ---- *)
Lemma cl_dregs_eq : forall rg rg' F, crt_dregs (regs := regs) (doc := doc) rg F ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 26; 27]%bv -> getr rg' r = getr rg r) ->
  crt_dregs (regs := regs) (doc := doc) rg' F.
Proof.
intros rg rg' F HD K.
refine {| crt_dregs_bregs := {| crt_bregs_sp := _; crt_bregs_gp := _; crt_bregs_tp := _; crt_bregs_s0 := _;
  crt_bregs_s1 := _; crt_bregs_s2 := _; crt_bregs_s4 := _; crt_bregs_s3 := _; crt_bregs_s7 := _; crt_bregs_s10 := _;
  crt_bregs_s11 := _ |}; crt_dregs_s5 := _ |}.
all: rewrite K by (cbv; tauto).
- exact (crt_bregs_sp (crt_dregs_bregs HD)).
- exact (crt_bregs_gp (crt_dregs_bregs HD)).
- exact (crt_bregs_tp (crt_dregs_bregs HD)).
- exact (crt_bregs_s0 (crt_dregs_bregs HD)).
- exact (crt_bregs_s1 (crt_dregs_bregs HD)).
- exact (crt_bregs_s2 (crt_dregs_bregs HD)).
- exact (crt_bregs_s4 (crt_dregs_bregs HD)).
- exact (crt_bregs_s3 (crt_dregs_bregs HD)).
- exact (crt_bregs_s7 (crt_dregs_bregs HD)).
- exact (crt_bregs_s10 (crt_dregs_bregs HD)).
- exact (crt_bregs_s11 (crt_dregs_bregs HD)).
- exact (crt_dregs_s5 HD).
Qed.
Lemma cl_bregs_eq : forall rg rg' F, crt_bregs (regs := regs) rg F ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 23; 26; 27]%bv -> getr rg' r = getr rg r) ->
  crt_bregs (regs := regs) rg' F.
Proof.
intros rg rg' F HB K.
refine {| crt_bregs_sp := _; crt_bregs_gp := _; crt_bregs_tp := _; crt_bregs_s0 := _; crt_bregs_s1 := _; crt_bregs_s2 := _;
  crt_bregs_s4 := _; crt_bregs_s3 := _; crt_bregs_s7 := _; crt_bregs_s10 := _; crt_bregs_s11 := _ |}.
all: rewrite K by (cbv; tauto).
- exact (crt_bregs_sp HB).
- exact (crt_bregs_gp HB).
- exact (crt_bregs_tp HB).
- exact (crt_bregs_s0 HB).
- exact (crt_bregs_s1 HB).
- exact (crt_bregs_s2 HB).
- exact (crt_bregs_s4 HB).
- exact (crt_bregs_s3 HB).
- exact (crt_bregs_s7 HB).
- exact (crt_bregs_s10 HB).
- exact (crt_bregs_s11 HB).
Qed.

(* L1 (+0x4e0), iteration i of the at-search loop: no key before i is MOD_AT (cm_at_inv at a = n); s6 = i,
   s8 = s9 = &doc->keys[i]; 0x30 = &doc->keys, 0x40 = MOD_AT, 0x48 = shadow (doc->keys), 0x50 = 0x58 = n *)
Definition cl_at_L1 (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Dc Lamc : list (Z * Z)) (peakc cset saved cap : Z)
  (Dback : list (Z * Z)) (ms : list (list Z * PjTree.jv)) (rg : bvmap 5 word) (i : nat) (keys : Z) : Prop :=
  cl_rw fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms /\
  cl_sp2 Wc memc (frame_addr lyc CRT_CID pos) saved /\
  crt_dregs (regs := regs) (doc := doc) rg (frame_addr lyc CRT_CID pos) /\
  (i < length ms)%nat /\ cm_at_inv ms i (length ms) /\
  getr rg 22 = w64 (Z.of_nat i) /\ getr rg 24 = w64 (keys + 8 * Z.of_nat i) /\
  getr rg 25 = w64 (keys + 8 * Z.of_nat i) /\
  rd_u64 SEGS (mrestrict (w_H Wc) memc) (doc + PJ_OFF_KEYS) keys /\
  crt_spill (regs := regs) Wc memc CL_SP_P (doc + PJ_OFF_KEYS) /\
  crt_spill (regs := regs) Wc memc CL_SP_LIT CRT_MOD_AT_A /\
  crt_spill (regs := regs) Wc memc CRT_SP_SHN (shadow_addr keys) /\
  crt_spill (regs := regs) Wc memc CRT_SP_PN (Z.of_nat (length ms)) /\
  crt_spill (regs := regs) Wc memc CRT_SP_N (Z.of_nat (length ms)).

(* L2 (+0x528): the search found at = cm_at ms; a2 = at, a3 = (at == n) *)
Definition cl_at_L2 (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Dc Lamc : list (Z * Z)) (peakc cset saved cap : Z)
  (Dback : list (Z * Z)) (ms : list (list Z * PjTree.jv)) (rg : bvmap 5 word) : Prop :=
  cl_rw fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms /\
  cl_sp2 Wc memc (frame_addr lyc CRT_CID pos) saved /\
  crt_dregs (regs := regs) (doc := doc) rg (frame_addr lyc CRT_CID pos) /\
  getr rg 12 = w64 (Z.of_nat (cm_at ms)) /\
  getr rg 13 = w64 (if Nat.eqb (cm_at ms) (length ms) then 1 else 0) /\
  crt_spill (regs := regs) Wc memc CL_SP_P (doc + PJ_OFF_KEYS) /\
  crt_spill (regs := regs) Wc memc CRT_SP_PN (Z.of_nat (length ms)) /\
  crt_spill (regs := regs) Wc memc CRT_SP_N (Z.of_nat (length ms)).

(* L1r (+0x4fc), the return of the at-search's strcmp (doc->keys[i], MOD_AT): the iteration's state with key i's
   name nm and what strcmp said about it, a0 = 0 exactly when nm is MOD_AT *)
Definition cl_at_L1r (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Dc Lamc : list (Z * Z)) (peakc cset saved cap : Z)
  (Dback : list (Z * Z)) (ms : list (list Z * PjTree.jv)) (rg : bvmap 5 word) (i : nat) (keys : Z) (nm : list Z) : Prop :=
  cl_rw fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms /\
  cl_sp2 Wc memc (frame_addr lyc CRT_CID pos) saved /\
  crt_dregs (regs := regs) (doc := doc) rg (frame_addr lyc CRT_CID pos) /\
  (i < length ms)%nat /\ cm_at_inv ms i (length ms) /\ (exists u, nth_error ms i = Some (nm, u)) /\
  getr rg 22 = w64 (Z.of_nat i) /\ getr rg 24 = w64 (keys + 8 * Z.of_nat i) /\
  getr rg 25 = w64 (keys + 8 * Z.of_nat i) /\
  rd_u64 SEGS (mrestrict (w_H Wc) memc) (doc + PJ_OFF_KEYS) keys /\
  crt_spill (regs := regs) Wc memc CL_SP_P (doc + PJ_OFF_KEYS) /\
  crt_spill (regs := regs) Wc memc CL_SP_LIT CRT_MOD_AT_A /\
  crt_spill (regs := regs) Wc memc CRT_SP_SHN (shadow_addr keys) /\
  crt_spill (regs := regs) Wc memc CRT_SP_PN (Z.of_nat (length ms)) /\
  crt_spill (regs := regs) Wc memc CRT_SP_N (Z.of_nat (length ms)) /\
  (getr rg 10 = w64 0 <-> nm = ck_MOD_AT).

(* C (+0x634), the three final checks: the member loop is done (or doc->n = 0); at is spilled at 0x20 *)
Definition cl_at_C (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Dc Lamc : list (Z * Z)) (peakc cset saved cap : Z)
  (Dback : list (Z * Z)) (ms : list (list Z * PjTree.jv)) (rg : bvmap 5 word) : Prop :=
  cl_rw fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms /\
  cl_sp2 Wc memc (frame_addr lyc CRT_CID pos) saved /\
  crt_bregs (regs := regs) rg (frame_addr lyc CRT_CID pos) /\
  crt_spill (regs := regs) Wc memc CRT_SP_AT (Z.of_nat (cm_at ms)).

(* L3 (+0x590), iteration i of the member loop: a0 = a1 = &back.keys[i], a2 = s9 = &doc->keys[i],
   s5 = shadow (&back.keys[i]), s6 = at - i (mod 2 ^ 64); 0x28 = shadow (&doc->kids), 0x30 = &doc->kids,
   0x50 = n - i (the counter), 0x58 = 56 i (the kid offset) *)
Definition cl_at_L3 (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Dc Lamc : list (Z * Z)) (peakc cset saved cap : Z)
  (Dback : list (Z * Z)) (ms : list (list Z * PjTree.jv)) (rg : bvmap 5 word) (i : nat) (bkeys dkeys : Z) : Prop :=
  cl_rw fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms /\
  cl_sp2 Wc memc (frame_addr lyc CRT_CID pos) saved /\
  crt_bregs (regs := regs) rg (frame_addr lyc CRT_CID pos) /\
  (i < length ms)%nat /\
  rd_u64 SEGS (mrestrict (w_H Wc) memc) (frame_addr lyc CRT_CID pos + CRT_OFF_BACK + PJ_OFF_KEYS) bkeys /\
  rd_u64 SEGS (mrestrict (w_H Wc) memc) (doc + PJ_OFF_KEYS) dkeys /\
  getr rg 10 = w64 (bkeys + 8 * Z.of_nat i) /\ getr rg 11 = w64 (bkeys + 8 * Z.of_nat i) /\
  getr rg 12 = w64 (dkeys + 8 * Z.of_nat i) /\ getr rg 25 = w64 (dkeys + 8 * Z.of_nat i) /\
  getr rg 21 = w64 (shadow_addr bkeys + Z.of_nat i) /\
  getr rg 22 = w64 ((Z.of_nat (cm_at ms) - Z.of_nat i) mod 2 ^ 64) /\
  crt_spill (regs := regs) Wc memc CRT_SP_AT (Z.of_nat (cm_at ms)) /\
  crt_spill (regs := regs) Wc memc CL_SP_KSH (shadow_addr (doc + PJ_OFF_KIDS)) /\
  crt_spill (regs := regs) Wc memc CL_SP_P (doc + PJ_OFF_KIDS) /\
  crt_spill (regs := regs) Wc memc CRT_SP_PN (Z.of_nat (length ms) - Z.of_nat i) /\
  crt_spill (regs := regs) Wc memc CRT_SP_N (56 * Z.of_nat i).

Definition CL_SP_BK : Z := 64.      (* 0x40(s1): &back.keys[i] (L3) *)
Definition CL_SP_BK2 : Z := 72.     (* 0x48(s1): &back.keys[i] again (L3) *)

(* L3r (+0x5c0), after the member compare's strcmp (back.keys[i], doc->keys[i]): it said EQUAL (a0 = 0, the two keys
   are one string, Crt102Model.cm_set_member); s8 = s9 = &doc->keys[i]; 0x40 = 0x48 = &back.keys[i] *)
Definition cl_l3core (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Dc Lamc : list (Z * Z)) (peakc cset saved cap : Z)
  (Dback : list (Z * Z)) (ms : list (list Z * PjTree.jv)) (rg : bvmap 5 word) (i : nat) (bkeys dkeys : Z) : Prop :=
  cl_rw fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms /\
  cl_sp2 Wc memc (frame_addr lyc CRT_CID pos) saved /\
  crt_bregs (regs := regs) rg (frame_addr lyc CRT_CID pos) /\
  (i < length ms)%nat /\
  rd_u64 SEGS (mrestrict (w_H Wc) memc) (frame_addr lyc CRT_CID pos + CRT_OFF_BACK + PJ_OFF_KEYS) bkeys /\
  rd_u64 SEGS (mrestrict (w_H Wc) memc) (doc + PJ_OFF_KEYS) dkeys /\
  getr rg 21 = w64 (shadow_addr bkeys + Z.of_nat i) /\
  getr rg 22 = w64 ((Z.of_nat (cm_at ms) - Z.of_nat i) mod 2 ^ 64) /\
  getr rg 24 = w64 (dkeys + 8 * Z.of_nat i) /\ getr rg 25 = w64 (dkeys + 8 * Z.of_nat i) /\
  crt_spill (regs := regs) Wc memc CRT_SP_AT (Z.of_nat (cm_at ms)) /\
  crt_spill (regs := regs) Wc memc CL_SP_KSH (shadow_addr (doc + PJ_OFF_KIDS)) /\
  crt_spill (regs := regs) Wc memc CL_SP_P (doc + PJ_OFF_KIDS) /\
  crt_spill (regs := regs) Wc memc CRT_SP_PN (Z.of_nat (length ms) - Z.of_nat i) /\
  crt_spill (regs := regs) Wc memc CRT_SP_N (56 * Z.of_nat i) /\
  crt_spill (regs := regs) Wc memc CL_SP_BK (bkeys + 8 * Z.of_nat i) /\
  crt_spill (regs := regs) Wc memc CL_SP_BK2 (bkeys + 8 * Z.of_nat i).
Definition cl_at_L3r fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i bkeys dkeys : Prop :=
  cl_l3core fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i bkeys dkeys /\
  getr rg 10 = w64 0.
(* L3s (+0x5f4), after `same (&back.kids[i], &doc->kids[i])` returned TRUE (a0 = 1) at an index other than at *)
Definition cl_at_L3s fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i bkeys dkeys : Prop :=
  cl_l3core fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i bkeys dkeys /\
  getr rg 10 = w64 1.

Section L0.
Hypothesis KL1 : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg keys,
  cl_at_L1 fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg 0 keys ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk CRT_L1_OFF rg memc mdc) QFa.
Hypothesis KL2 : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg,
  cl_at_L2 fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk CRT_L2_OFF rg memc mdc) QFa.

Lemma cl_at_L0 : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dx Lamc peakc cntc rg ms cset saved rcd,
  L0a fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dx Lamc peakc cntc rg ms cset saved rcd ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk CRT_L0_OFF rg memc mdc) QFa.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dx Lamc peakc cntc rg ms cset saved rcd HL0.
destruct (cl_L0_saved _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL0)
  as (Hsv & Hrc & Hcn & Hpos & cap & Dback & EDx & Hback & Hpb & Hfob & Ecap).
pose proof (crt_at_L0_obj HL0) as Et.
pose proof (crt_at_L0_frm_zero HL0) as HFZ.
pose proof (crt_at_L0_fregs HL0) as HFK.
pose proof (crt_at_L0_live HL0) as HL.
pose proof (crt_at_L0_dregs HL0) as HDR.
pose proof (crt_at_L0_saved HL0) as R24.
pose proof (crt_at_L0_flag HL0) as R22.
pose proof (crt_at_L0_sp_back HL0) as SBK.
pose proof (crt_at_L0_sp_shn HL0) as SSHN.
pose proof (crt_at_L0_sp_pn HL0) as SPN.
pose proof (crt_at_L0_sp_n HL0) as SN.
pose proof (crt_at_L0_doc_align HL0) as Hd8.
pose proof (crt_at_L0_doc_open HL0) as Hrad.
pose proof (crt_at_L0_back_open HL0) as Hrab.
pose proof (crt_at_L0_v_open HL0) as Hrav.
pose proof (crt_at_L0_cset_range HL0) as Hcs.
pose proof (crt_at_L0_cset_mod HL0) as Hcin.
pose proof (crt_at_L0_copy HL0) as Hcopy.
pose proof (crt_at_L0_copy_fd HL0) as Hfd.
pose proof (crt_at_L0_copy_tblk HL0) as HPcp.
pose proof (crt_at_L0_copy_fo HL0) as Hfoc.
pose proof (crt_at_L0_copy_depth HL0) as Hdep.
subst Dx cntc rcd. rewrite (proj2 (Z.eqb_neq saved 0) Hsv), Z.eqb_refl in R22.
assert (HRW : cl_rw fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms).
{ exact (conj Et (conj HFZ (conj HFK (conj HL (conj Hcs (conj Hcin (conj Hsv (conj Hcopy (conj Hback (conj Hd8 (conj Hrad (conj Hrab (conj Hrav (conj Hpos (conj Hfd (conj HPcp (conj Hfoc (conj Hdep (conj Hpb (conj Hfob Ecap)))))))))))))))))))). }
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_side HL) as HSD.
pose proof (crt_side_ledger HSD) as HLD.
pose proof (crt_side_doc HSD) as HDOC.
pose proof (crt_side_doc_blocks HSD) as HDL.
rewrite Et in HDOC.
destruct (cl_node_obj _ _ _ _ _ HDOC) as (num & kids & keys & dcap & Di & _ & _ & Hhdr & Hncap & Hcap & EDi & Hmem).
pose proof Hhdr as (_ & _ & _ & _ & _ & Hkeys & Hn & _).
pose proof (crt_dregs_bregs HDR) as Hrec2.
pose proof (crt_bregs_sp Hrec2) as R2.
pose proof (crt_bregs_gp Hrec2) as R3.
pose proof (crt_bregs_tp Hrec2) as R4.
pose proof (crt_bregs_s0 Hrec2) as R8.
pose proof (crt_bregs_s1 Hrec2) as R9.
pose proof (crt_bregs_s2 Hrec2) as R18.
pose proof (crt_bregs_s4 Hrec2) as R20.
pose proof (crt_bregs_s3 Hrec2) as R19.
pose proof (crt_bregs_s7 Hrec2) as R23.
pose proof (crt_bregs_s10 Hrec2) as R26.
pose proof (crt_bregs_s11 Hrec2) as R27.
pose proof (crt_dregs_s5 HDR) as R21.
pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkp & _).
pose proof (crt_live_frame HL) as HFRM. pose proof (crt_live_memnorm HL) as HPM.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cl_sp0 as (H16 & Hsp0 & H47). pose proof cl_sp1 as (Hs32 & Hs1).
assert (HSTKC : STKC = 27632) by (vm_compute; reflexivity).
pose proof cl_doc_low as (Hdl0 & Hdl1).
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc (crt_frame_listed HFRM))
  as (Fb1 & Fb2 & Fb3).
change (fs_frame_bytes CRT_CID) with 512 in Fb2.
set (F := frame_addr lyc CRT_CID pos) in *.
set (sp1 := CRT_sp1 (regs := regs)) in *.
set (n := Z.of_nat (length ms)) in *.
assert (En : n = Z.of_nat (length ms)) by reflexivity.
assert (Hn0 : 0 <= n) by (unfold n; lia).
assert (Hnr : 0 <= n <= 2 ^ 54).
{ destruct Hcap as [(-> & _ & _) | (Hc0 & Hkd & _)]; [lia|].
  destruct (cl_blk_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLD Hkd) as (_ & Hb0 & Hb).
  change (@cf_head CfParams_preset) with 16 in Hb0. lia. }
assert (Hkr : 0 <= keys < 2 ^ 47).
{ destruct Hcap as [(_ & _ & ->) | (_ & _ & Hky)]; [lia|].
  destruct (cl_blk_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLD Hky) as (Hk0 & Hb0 & Hb).
  change (@cf_head CfParams_preset) with 16 in Hb0. lia. }
assert (HEI : img_env VAL A_LIM (TE regs rg [w64 n; w64 keys])) by apply te_env.
pose (RUNTO := @crt_run_to_xw_inv fxk rc SK A_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (YSRrMemnorm.srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)) WS_HJ).
assert (W9 : ew (TE regs rg [w64 n; w64 keys]) (xr 9) = w64 sp1)
  by (unfold xr; rewrite (te_cur regs rg _ 9%bv 9) by reflexivity; exact R9).
assert (W21 : ew (TE regs rg [w64 n; w64 keys]) 53 = w64 doc)
  by (change 53%nat with (xr 21); unfold xr; rewrite (te_cur regs rg _ 21%bv 21) by reflexivity; exact R21).
assert (W26 : ew (TE regs rg [w64 n; w64 keys]) 58 = w64 SHADOW_OFF)
  by (change 58%nat with (xr 26); unfold xr; rewrite (te_cur regs rg _ 26%bv 26) by reflexivity; exact R26).
assert (W27 : ew (TE regs rg [w64 n; w64 keys]) 59 = w64 F)
  by (change 59%nat with (xr 27); unfold xr; rewrite (te_cur regs rg _ 27%bv 27) by reflexivity; exact R27).
assert (W24 : ew (TE regs rg [w64 n; w64 keys]) 56 = w64 saved)
  by (change 56%nat with (xr 24); unfold xr; rewrite (te_cur regs rg _ 24%bv 24) by reflexivity; exact R24).
assert (W64 : ew (TE regs rg [w64 n; w64 keys]) 64 = w64 n) by exact (te_more_lt regs rg [w64 n; w64 keys] 0 ltac:(lia)).
assert (W65 : ew (TE regs rg [w64 n; w64 keys]) 65 = w64 keys) by exact (te_more_lt regs rg [w64 n; w64 keys] 1 ltac:(lia)).
assert (X41 : bv_unsigned (ew (TE regs rg [w64 n; w64 keys]) 41) = sp1)
  by (change 41%nat with (xr 9); rewrite W9; apply unsigned_lit_small; lia).
assert (X64 : bv_unsigned (ew (TE regs rg [w64 n; w64 keys]) 64) = n) by (rewrite W64; apply unsigned_lit_small; lia).
assert (Hsv0 : 4096 <= saved < 2 ^ 47).
{ pose proof (crt_live_lam_perm HL) as HPl'.
  assert (Hin : In (saved, cap) Lamc).
  { apply (Permutation_in _ (Permutation_sym HPl')). apply in_or_app. left. apply in_or_app. right. left. reflexivity. }
  destruct (cl_blk_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLD Hin) as (Hk & Ha & Hb).
  pose proof YM05.alloc_ceiling_lt. change (@cf_head CfParams_preset) with 16 in Ha. lia. }
unfold crt_cfg.
destruct (Z.eq_dec n 0) as [Hn00 | Hn00].
- (* ---- the empty object: `beqz a1` to L2 (+0x528), at = n = 0 ---- *)
  destruct (cl_L0_entry fxk Wc memc rg n keys F [mkAC BC_EQ (SOff 64 0) (SLit 0)]
    (ts_conds_eq _ 64 n [0] X64 ltac:(constructor; [split; lia | constructor]))
    R9 R21 R26 R22 R27 ltac:(lia) ltac:(lia) SBK ltac:(lia) ltac:(lia) Hs32
    ltac:(lia) Hd8 Hnr ltac:(lia) ltac:(intros a Ha; apply Hstkp; lia) SSHN SPN SN Hkeys Hn) as [HS SHOK].
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM CL_SPAN (CRT_PC_A + CRT_L2_OFF).
  + cbn [ms_mem mkst restrict]. unfold CL_Bx. change (SOff (xr 26) 0) with (SOff 58 0).
    rewrite (U_atom_off (TE regs rg [w64 n; w64 keys]) 53 doc 40 W21) by lia.
    rewrite (U_atom (TE regs rg [w64 n; w64 keys]) 58 SHADOW_OFF W26) by (unfold SHADOW_OFF; lia).
    apply (range_addressable_sub _ SHADOW_OFF doc 56 (doc + 40) 8 Hrad); lia.
  + lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ (xr 9) (sp1 - sp0)); [reflexivity | change (xr 9) with 41%nat; rewrite X41; lia | cbn; lia | cbn; lia |].
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil.
  + assert (Ems : ms = []) by (apply length_zero_iff_nil; unfold n in Hn00; lia).
    assert (Hav : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 24 <= a < sp1 + 88) ->
      aview SEGS (w_H Wc) (ms_mem ms0) a = aview SEGS (w_H Wc) memc a).
    { apply (ts_keep Wc _ _ memc (ms_mem ms0) _ HFr). intros a (r & Hri & Hr). vm_compute in Hri.
      repeat (destruct Hri as [<- | Hri]; [cbn [YP09.r_wlo YP09.r_whi YP09.r_base base_val] in Hr; rewrite ?X41 in Hr; lia |]);
        destruct Hri. }
    assert (Hpr : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) (ms_mem ms0) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
    pose proof (cl_rw_keep _ _ _ _ _ memc (ms_mem ms0) _ _ _ _ _ _ _ _ _ _ _ _ _ (sp1 + 24) (sp1 + 88) HRW HJ HB_HJ
      ltac:(lia) ltac:(unfold CRT_SP_F; lia) Hav Hpr HPM) as HRW1.
    assert (K21 : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 26; 27]%bv ->
      getr (ms_regs ms0) r = getr rg r).
    { intros r Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [clkeep HS |]). destruct Hr. }
    pose proof (cl_dregs_eq rg (ms_regs ms0) F HDR K21) as HDR1.
    prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
    lazymatch type of HS with st_ok_pi _ _ ?E _ _ => set (EE := E) in * end.
    assert (WE : forall k v, ew (TE regs rg [w64 n; w64 keys]) k = w64 v -> (k < 240)%nat -> ew EE k = w64 v).
    { intros k v Hk Hlt. unfold EE. rewrite ?ew_ewset_other by lia. exact Hk. }
    assert (XE41 : bv_unsigned (ew EE 41) = sp1) by (unfold EE; rewrite ?ew_ewset_other by lia; exact X41).
    clear HF HFr HG.
    pmkst HS.
    lazymatch goal with |- context [Z_to_bv 64 (BASE + ?pc)] =>
      replace pc with (CRT_PC_A + CRT_L2_OFF) by (vm_compute; reflexivity) end.
    apply (KL2 fxk lyc Sc Hpc Wc (ms_mem ms0) _ kj pos Dc Lamc peakc cset saved cap Dback ms (ms_regs ms0)).
    refine (conj HRW1 (conj (conj _ _) (conj HDR1 (conj _ (conj _ (conj _ (conj _ _))))))).
    * clsp HS 0%nat 41%nat XE41; [clden (WE 59%nat F W27 ltac:(lia)) | lia].
    * clsp HS 0%nat 41%nat XE41; [clden (WE 56%nat saved W24 ltac:(lia)) | lia].
    * rewrite Q12, Ems, W64, Hn00. reflexivity.
    * rewrite Q13, Ems, W64, Hn00. vm_compute. reflexivity.
    * clsp HS 0%nat 41%nat XE41; [clden (WE 53%nat doc W21 ltac:(lia)) | lia].
    * clsp HS 0%nat 41%nat XE41; [clden (WE 64%nat n W64 ltac:(lia)) | lia].
    * clsp HS 0%nat 41%nat XE41; [clden (WE 64%nat n W64 ltac:(lia)) | lia].
- (* ---- a member to search: to L1 (+0x4e0), i = 0 ---- *)
  destruct (cl_L0_entry fxk Wc memc rg n keys F [mkAC BC_NE (SOff 64 0) (SLit 0)]
    (ts_conds_ne _ 64 n [0] X64 ltac:(constructor; [split; lia | constructor]))
    R9 R21 R26 R22 R27 ltac:(lia) ltac:(lia) SBK ltac:(lia) ltac:(lia) Hs32
    ltac:(lia) Hd8 Hnr ltac:(lia) ltac:(intros a Ha; apply Hstkp; lia) SSHN SPN SN Hkeys Hn) as [HS SHOK].
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM CL_SPAN (CRT_PC_A + CRT_L1_OFF).
  1,2: cbn [ms_mem mkst restrict]; unfold CL_Bx; change (SOff (xr 26) 0) with (SOff 58 0);
    lazymatch goal with |- context [U ?E (SOff 53 ?c)] => rewrite (U_atom_off E 53 doc c W21) by lia end;
    rewrite (U_atom (TE regs rg [w64 n; w64 keys]) 58 SHADOW_OFF W26) by (unfold SHADOW_OFF; lia);
    lazymatch goal with |- range_addressable _ _ (doc + ?c) 8 =>
      apply (range_addressable_sub _ SHADOW_OFF doc 56 (doc + c) 8 Hrad); lia end.
  + lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ (xr 9) (sp1 - sp0)); [reflexivity | change (xr 9) with 41%nat; rewrite X41; lia | cbn; lia | cbn; lia |].
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil.
  + assert (Hav : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 24 <= a < sp1 + 88) ->
      aview SEGS (w_H Wc) (ms_mem ms0) a = aview SEGS (w_H Wc) memc a).
    { apply (ts_keep Wc _ _ memc (ms_mem ms0) _ HFr). intros a (r & Hri & Hr). vm_compute in Hri.
      repeat (destruct Hri as [<- | Hri]; [cbn [YP09.r_wlo YP09.r_whi YP09.r_base base_val] in Hr; rewrite ?X41 in Hr; lia |]);
        destruct Hri. }
    assert (Hpr : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) (ms_mem ms0) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
    pose proof (cl_rw_keep _ _ _ _ _ memc (ms_mem ms0) _ _ _ _ _ _ _ _ _ _ _ _ _ (sp1 + 24) (sp1 + 88) HRW HJ HB_HJ
      ltac:(lia) ltac:(unfold CRT_SP_F; lia) Hav Hpr HPM) as HRW1.
    assert (K21 : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 26; 27]%bv ->
      getr (ms_regs ms0) r = getr rg r).
    { intros r Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [clkeep HS |]). destruct Hr. }
    pose proof (cl_dregs_eq rg (ms_regs ms0) F HDR K21) as HDR1.
    prreg HS (22%bv : bv 5) Q22. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
    lazymatch type of HS with st_ok_pi _ _ ?E _ _ => set (EE := E) in * end.
    assert (WE : forall k v, ew (TE regs rg [w64 n; w64 keys]) k = w64 v -> (k < 240)%nat -> ew EE k = w64 v).
    { intros k v Hk Hlt. unfold EE. rewrite ?ew_ewset_other by lia. exact Hk. }
    assert (XE41 : bv_unsigned (ew EE 41) = sp1) by (unfold EE; rewrite ?ew_ewset_other by lia; exact X41).
    assert (Hkeys1 : rd_u64 SEGS (mrestrict (w_H Wc) (ms_mem ms0)) (doc + PJ_OFF_KEYS) keys).
    { destruct Hkeys as [Hk0 Hk1]. split; [exact Hk0|].
      apply (ts_vm_av (w_H Wc) (w_H Wc) memc (ms_mem ms0)); [|exact Hk1].
      intros j Hj. apply Hav; unfold PJ_OFF_KEYS; lia. }
    clear HF HFr HG.
    pmkst HS.
    lazymatch goal with |- context [Z_to_bv 64 (BASE + ?pc)] =>
      replace pc with (CRT_PC_A + CRT_L1_OFF) by (vm_compute; reflexivity) end.
    apply (KL1 fxk lyc Sc Hpc Wc (ms_mem ms0) _ kj pos Dc Lamc peakc cset saved cap Dback ms (ms_regs ms0) keys).
    refine (conj HRW1 (conj (conj _ _) (conj HDR1 (conj _ (conj (cm_at_inv_start ms) (conj _ (conj _ (conj _ (conj Hkeys1 (conj _ (conj _ (conj _ (conj _ _))))))))))))).
    * clsp HS 0%nat 41%nat XE41; [clden (WE 59%nat F W27 ltac:(lia)) | lia].
    * clsp HS 0%nat 41%nat XE41; [clden (WE 56%nat saved W24 ltac:(lia)) | lia].
    * unfold n in Hn00. lia.
    * rewrite Q22. reflexivity.
    * rewrite Q24. unfold EE. rewrite ?ew_ewset_other by lia. rewrite W65. f_equal. lia.
    * rewrite Q25. unfold EE. rewrite ?ew_ewset_other by lia. rewrite W65. f_equal. lia.
    * clsp HS 0%nat 41%nat XE41; [clden (WE 53%nat doc W21 ltac:(lia)) | lia].
    * clsp HS 0%nat 41%nat XE41.
      -- apply cl_modat_den. unfold EE. rewrite ?ew_ewset_other by lia.
         apply te_img. unfold A_TEXT, A_LIM. lia.
      -- pose proof cl_lit_rng. lia.
    * clsp HS 0%nat 41%nat XE41.
      -- rewrite denot_lit_U. f_equal.
         assert (XB : bv_unsigned (ew EE 58) = SHADOW_OFF)
           by (rewrite (WE 58%nat SHADOW_OFF W26 ltac:(lia)); apply unsigned_lit_small; unfold SHADOW_OFF; lia).
         assert (XK : bv_unsigned (ew EE 65) = keys)
           by (rewrite (WE 65%nat keys W65 ltac:(lia)); apply unsigned_lit_small; lia).
         exact (proj1 (cl_sh_U EE 58 65 keys XB XK ltac:(lia))).
      -- unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos keys 8 ltac:(lia) ltac:(lia)).
         assert (keys / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
    * clsp HS 0%nat 41%nat XE41; [clden (WE 64%nat n W64 ltac:(lia)) | lia].
    * clsp HS 0%nat 41%nat XE41; [clden (WE 64%nat n W64 ltac:(lia)) | lia].
Qed.
End L0.

(* ======================================================================================================== *)
(* L1: THE AT-SEARCH LOOP (new:742-744). One iteration is L1 -> the strcmp at +0x4f8 -> L1r (+0x4fc) -> L1 (i + 1)
   or L2; the loop closes by the measure length ms - i. *)

(* ---- L1's entry state for iteration i (extras: 64 = n, 65 = keys, 66 = saved, 67 = keys[i], 68 = shadow (keys)) ---- *)
Lemma cl_L1_entry : forall (fxk : YK11.FPState) (Wc : world SEGS) memc rg n keys saved F kp i,
  getr rg 9 = w64 (CRT_sp1 (regs := regs)) -> getr rg 21 = w64 doc -> getr rg 22 = w64 (Z.of_nat i) ->
  getr rg 25 = w64 (keys + 8 * Z.of_nat i) -> getr rg 26 = w64 SHADOW_OFF -> getr rg 27 = w64 F ->
  2 ^ 46 <= CRT_sp1 (regs := regs) -> CRT_sp1 (regs := regs) + 96 <= 2 ^ 47 -> CRT_sp1 (regs := regs) mod 32 = 0 ->
  4096 <= doc -> doc + 56 <= CRT_sp1 (regs := regs) -> 0 <= F -> F + 512 <= CRT_sp1 (regs := regs) ->
  4096 <= keys -> keys mod 8 = 0 -> keys + 8 * Z.of_nat i + 8 <= CRT_sp1 (regs := regs) ->
  Z.of_nat i < n -> n <= 2 ^ 54 -> 0 <= saved < 2 ^ 64 -> 0 <= kp < 2 ^ 64 ->
  cl_sp2 Wc memc F saved ->
  crt_spill (regs := regs) Wc memc CL_SP_P (doc + PJ_OFF_KEYS) ->
  crt_spill (regs := regs) Wc memc CL_SP_LIT CRT_MOD_AT_A ->
  crt_spill (regs := regs) Wc memc CRT_SP_SHN (shadow_addr keys) ->
  crt_spill (regs := regs) Wc memc CRT_SP_PN n -> crt_spill (regs := regs) Wc memc CRT_SP_N n ->
  rd_u64 SEGS (mrestrict (w_H Wc) memc) (keys + 8 * Z.of_nat i) kp ->
  st_ok_pi SEGS VAL (TE regs rg [w64 n; w64 keys; w64 saved; w64 kp; w64 (shadow_addr keys)]) ss_L1
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_A + CRT_L1_OFF))) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS CL_Bx [] (TE regs rg [w64 n; w64 keys; w64 saved; w64 kp; w64 (shadow_addr keys)]) (mrestrict (w_H Wc) memc).
Proof.
intros fxk Wc memc rg n keys saved F kp i R9 R21 R22 R25 R26 R27 H1 H2 H3 H4 H5 HF0 HF1 Hk4 Hk8 Hkc Hin Hn Hsv Hkp
  (VBK & VSV) VP VLIT VSHN VPN VN [_ VKP].
unfold crt_spill, CL_SP_P, CL_SP_LIT, CRT_SP_SHN, CRT_SP_PN, CRT_SP_N, CRT_SP_BACK, CRT_SP_SAVED, CRT_OFF_BACK,
  PJ_OFF_KEYS in *.
set (sp1 := CRT_sp1 (regs := regs)) in *.
set (E := TE regs rg [w64 n; w64 keys; w64 saved; w64 kp; w64 (shadow_addr keys)]).
assert (Hsh : 0 <= shadow_addr keys < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos keys 8 ltac:(lia) ltac:(lia)).
  assert (keys / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
assert (W9 : ew E (xr 9) = w64 sp1) by (unfold E, xr; rewrite (te_cur regs rg _ 9%bv 9) by reflexivity; exact R9).
assert (W21 : ew E (xr 21) = w64 doc) by (unfold E, xr; rewrite (te_cur regs rg _ 21%bv 21) by reflexivity; exact R21).
assert (W22 : ew E (xr 22) = w64 (Z.of_nat i)) by (unfold E, xr; rewrite (te_cur regs rg _ 22%bv 22) by reflexivity; exact R22).
assert (W25 : ew E (xr 25) = w64 (keys + 8 * Z.of_nat i))
  by (unfold E, xr; rewrite (te_cur regs rg _ 25%bv 25) by reflexivity; exact R25).
assert (W26 : ew E (xr 26) = w64 SHADOW_OFF) by (unfold E, xr; rewrite (te_cur regs rg _ 26%bv 26) by reflexivity; exact R26).
assert (W27 : ew E (xr 27) = w64 F) by (unfold E, xr; rewrite (te_cur regs rg _ 27%bv 27) by reflexivity; exact R27).
assert (E64 : ew E 64 = w64 n) by exact (te_more_lt regs rg _ 0 ltac:(lia)).
assert (E66 : ew E 66 = w64 saved) by exact (te_more_lt regs rg _ 2 ltac:(lia)).
assert (E67 : ew E 67 = w64 kp) by exact (te_more_lt regs rg _ 3 ltac:(lia)).
assert (E68 : ew E 68 = w64 (shadow_addr keys)) by exact (te_more_lt regs rg _ 4 ltac:(lia)).
assert (UB : forall k v, ew E k = w64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E k) = v)
  by (intros k v Hk Hv; rewrite Hk; apply unsigned_lit_small; exact Hv).
split; [|unfold sh_ok; apply Forall_nil].
apply ts_st_ok.
all: try change (TE regs rg [w64 n; w64 keys; w64 saved; w64 kp; w64 (shadow_addr keys)]) with E.
- apply te_regs_ok.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
  + apply (ts_rok E _ (xr 9) sp1); [apply UB; [exact W9 | lia] | lia | lia | intros o Ho; lia |].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (ts_chunk E _ _ 24 8 (SOff 66 0) saved); [| cbn; lia | cbn; lia | exact VSV].
      rewrite denot_lit_U, (U_atom_off E 66 saved 0 E66) by lia. rewrite Z.add_0_r. reflexivity.
    * apply (ts_chunk E _ _ 48 8 (SOff (xr 21) 32) (doc + 32)); [| cbn; lia | cbn; lia | exact VP].
      rewrite denot_lit_U, (U_atom_off E (xr 21) doc 32 W21) by lia. reflexivity.
    * apply (ts_chunk E _ _ 56 8 (SOff (xr 27) 32) (F + 32)); [| cbn; lia | cbn; lia | exact VBK].
      rewrite denot_lit_U, (U_atom_off E (xr 27) F 32 W27) by lia. reflexivity.
    * apply (ts_chunk E _ _ 64 8 (SOff 243 69824) CRT_MOD_AT_A); [| pose proof cl_lit_rng; cbn; lia | cbn; lia | exact VLIT].
      apply cl_modat_den. unfold E. apply te_img. unfold A_TEXT, A_LIM. lia.
    * apply (ts_chunk E _ _ 72 8 (SOff 68 0) (shadow_addr keys)); [| cbn; lia | cbn; lia | exact VSHN].
      rewrite denot_lit_U, (U_atom_off E 68 (shadow_addr keys) 0 E68) by lia. rewrite Z.add_0_r. reflexivity.
    * apply (ts_chunk E _ _ 80 8 (SOff 64 0) n); [| cbn; lia | cbn; lia | exact VPN].
      rewrite denot_lit_U, (U_atom_off E 64 n 0 E64) by lia. rewrite Z.add_0_r. reflexivity.
    * apply (ts_chunk E _ _ 88 8 (SOff 64 0) n); [| cbn; lia | cbn; lia | exact VN].
      rewrite denot_lit_U, (U_atom_off E 64 n 0 E64) by lia. rewrite Z.add_0_r. reflexivity.
  + apply (ts_rok E _ (xr 25) (keys + 8 * Z.of_nat i)); [apply UB; [exact W25 | lia] | lia | lia | intros o Ho; lia |].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (ts_chunk E _ _ 0 8 (SOff 67 0) kp); [| cbn; lia | cbn; lia | rewrite Z.add_0_r; exact VKP].
    rewrite denot_lit_U, (U_atom_off E 67 kp 0 E67) by lia. rewrite Z.add_0_r. reflexivity.
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !ts_bv_some.
  rewrite (UB _ _ W9 ltac:(lia)), (UB _ _ W25 ltac:(lia)).
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | split; [|exact I]]].
  + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (UB _ _ W9 ltac:(lia)), (UB _ _ W25 ltac:(lia)), (UB _ _ W26 ltac:(unfold SHADOW_OFF; lia)),
      (UB _ _ W22 ltac:(lia)), (UB _ _ E64 ltac:(lia)).
    change (2 ^ 5) with 32. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
    unfold SHADOW_OFF. repeat split; lia.
  + apply U_inj. rewrite (proj2 (cl_sh_U E (xr 26) (xr 25) (keys + 8 * Z.of_nat i)
      (UB _ _ W26 ltac:(unfold SHADOW_OFF; lia)) (UB _ _ W25 ltac:(lia)) ltac:(lia))).
    rewrite U_SAlu, (U_atom_off E 68 (shadow_addr keys) 0 E68), (U_atom_off E (xr 22) (Z.of_nat i) 0 W22) by lia.
    cbn [zalu_raw]. unfold zcanon, M64. rewrite !Z.add_0_r.
    unfold shadow_addr. rewrite Z.mul_comm, Z.div_add by lia.
    unfold SHADOW_OFF. assert (0 <= keys / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
    rewrite !Z.mod_small by lia. lia.
Qed.

(* ---- a spill word survives a change that keeps [s1, s1 + 0x70) ---- *)
Lemma cl_spill_keep : forall (Wc : world SEGS) m m' off v,
  (forall a, CRT_sp1 (regs := regs) <= a < CRT_sp1 (regs := regs) + CRT_SP_F ->
     aview SEGS (w_H Wc) m' a = aview SEGS (w_H Wc) m a) ->
  0 <= off -> off + 8 <= CRT_SP_F -> crt_spill (regs := regs) Wc m off v -> crt_spill (regs := regs) Wc m' off v.
Proof.
intros Wc m m' off v K H0 H1 HS. unfold crt_spill in *. apply (ts_vm_av (w_H Wc) (w_H Wc) m m'); [|exact HS].
intros j Hj. apply K. lia.
Qed.
(* ---- a spill word survives a change that keeps its own eight bytes ---- *)
Lemma cl_spill_keep8 : forall (Wc : world SEGS) m m' off v,
  (forall a, CRT_sp1 (regs := regs) + off <= a < CRT_sp1 (regs := regs) + off + 8 ->
     aview SEGS (w_H Wc) m' a = aview SEGS (w_H Wc) m a) ->
  crt_spill (regs := regs) Wc m off v -> crt_spill (regs := regs) Wc m' off v.
Proof.
intros Wc m m' off v K HS. unfold crt_spill in *. apply (ts_vm_av (w_H Wc) (w_H Wc) m m'); [|exact HS].
intros j Hj. apply K. lia.
Qed.
(* ---- a callee-saved register survives a call ---- *)
Lemma cl_cs_keep : forall rg rg', aregs_preserved rg rg' ->
  forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rg' r = getr rg r.
Proof.
intros rg rg' HP r Hr. apply (ts_ap rg rg' r HP). cbv [In] in Hr.
repeat (destruct Hr as [<- | Hr]; [unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?w] => let v := eval vm_compute in (bv_unsigned w) in
    change (bv_unsigned w) with v end; lia |]). destruct Hr.
Qed.

Section L1.
(* the loop's measure bound: the continuation is owed only for states whose measure length ms - i is within it *)
Variable mb : nat.
Hypothesis KL1r : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i keys nm,
  (length ms - i <= mb)%nat ->
  cl_at_L1r fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i keys nm ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk (CRT_CMP1_CALL + 4) rg memc mdc) QFa.

(* ---- L1 -> the strcmp (doc->keys[i], MOD_AT) at +0x4f8 -> L1r: the inline check of the key slot (+0x720's report
   unreachable: the key array is a ledger block, block_shadow gives the slot), the two loads, the call ---- *)
Lemma cl_L1_head : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i keys,
  (length ms - i <= mb)%nat ->
  cl_at_L1 fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i keys ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk CRT_L1_OFF rg memc mdc) QFa.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i keys Hmb HL1.
destruct HL1 as (HRW & HSP2 & HDR & Hi & Hinv & R22 & R24 & R25 & Hkeys & SP & SLIT & SSHN & SPN & SN).
pose proof HRW as (Et & HFZ & HFK & HL & Hcs & Hcin & Hsv & Hcopy & Hback & Hd8 & Hrad & Hrab & Hrav & Hpos).
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ).
pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPl.
pose proof (crt_live_frame HL) as HFRM.
pose proof (crt_live_memnorm HL) as HPM.
pose proof (crt_side_ledger HSD) as HLD.
pose proof (crt_side_arodata HSD) as HRO.
pose proof (crt_side_doc HSD) as HDOC.
pose proof (crt_side_doc_blocks HSD) as HDL.
pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkp & _).
rewrite Et in HDOC.
destruct (nth_error ms i) as [[nm u]|] eqn:Hnth; [|apply nth_error_None in Hnth; lia].
destruct (cl_obj_key _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLD HDOC HDL Hkeys Hnth)
  as (kp & kb & Hkp & Hcstr & Hinkb & SXk & Hraslot & Hk4 & Hk8 & Hkce & _).
pose proof (crt_dregs_bregs HDR) as Hrec3.
pose proof (crt_bregs_sp Hrec3) as R2.
pose proof (crt_bregs_gp Hrec3) as R3.
pose proof (crt_bregs_tp Hrec3) as R4.
pose proof (crt_bregs_s0 Hrec3) as R8.
pose proof (crt_bregs_s1 Hrec3) as R9.
pose proof (crt_bregs_s2 Hrec3) as R18.
pose proof (crt_bregs_s4 Hrec3) as R20.
pose proof (crt_bregs_s3 Hrec3) as R19.
pose proof (crt_bregs_s7 Hrec3) as R23.
pose proof (crt_bregs_s10 Hrec3) as R26.
pose proof (crt_bregs_s11 Hrec3) as R27.
pose proof (crt_dregs_s5 HDR) as R21.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cl_sp0 as (H16 & Hsp0 & H47). pose proof cl_sp1 as (Hs32 & Hs1).
assert (HSTKC : STKC = 27632) by (vm_compute; reflexivity).
pose proof cl_doc_low as (Hdl0 & Hdl1).
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc (crt_frame_listed HFRM))
  as (Fb1 & Fb2 & Fb3).
change (fs_frame_bytes CRT_CID) with 512 in Fb2.
set (F := frame_addr lyc CRT_CID pos) in *.
set (sp1 := CRT_sp1 (regs := regs)) in *.
assert (Hsv0 : 4096 <= saved < 2 ^ 47).
{ assert (Hin : In (saved, cap) Lamc).
  { apply (Permutation_in _ (Permutation_sym HPl)). apply in_or_app. left. apply in_or_app. right. left. reflexivity. }
  destruct (cl_blk_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLD Hin) as (Hk & Ha & Hb).
  pose proof YM05.alloc_ceiling_lt. change (@cf_head CfParams_preset) with 16 in Ha. lia. }
destruct (cl_L1_entry fxk Wc memc rg (Z.of_nat (length ms)) keys saved F kp i R9 R21 R22 R25 R26 R27
  ltac:(lia) ltac:(lia) Hs32 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hk4 Hk8 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(destruct Hkp; lia) HSP2 SP SLIT SSHN SPN SN Hkp) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TE regs rg [w64 (Z.of_nat (length ms)); w64 keys; w64 saved; w64 kp; w64 (shadow_addr keys)]))
  by apply te_env.
pose (RUN := @crt_run_xw_inv fxk rc SK A_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (YSRrMemnorm.srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)) WS_HJ).
unfold crt_cfg.
paj_run_tok_x_inv RUN HS HJ SHOK HPM CL_SPAN.
- (* the inline check of the key slot (+0x4e8; its report +0x720) *)
  cbn [ms_mem mkst restrict]. unfold CL_Bx. change (SOff (xr 26) 0) with (SOff 58 0).
  assert (W26 : ew (TE regs rg [w64 (Z.of_nat (length ms)); w64 keys; w64 saved; w64 kp; w64 (shadow_addr keys)]) 58
    = w64 SHADOW_OFF) by (change 58%nat with (xr 26); unfold xr; rewrite (te_cur regs rg _ 26%bv 26) by reflexivity; exact R26).
  assert (W25 : ew (TE regs rg [w64 (Z.of_nat (length ms)); w64 keys; w64 saved; w64 kp; w64 (shadow_addr keys)]) 57
    = w64 (keys + 8 * Z.of_nat i))
    by (change 57%nat with (xr 25); unfold xr; rewrite (te_cur regs rg _ 25%bv 25) by reflexivity; exact R25).
  rewrite (U_atom _ 57 _ W25) by lia. rewrite (U_atom _ 58 SHADOW_OFF W26) by (unfold SHADOW_OFF; lia).
  exact Hraslot.
- lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil.
- apply frame_of_read_only in HF; [|vm_compute; reflexivity].
  rewrite HF in HJ, HPM. clear HFr HG.
  assert (KB : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
    getr (ms_regs ms0) r = getr rg r).
  { intros r Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [clkeep HS |]). destruct Hr. }
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (1%bv : bv 5) Q1.
  assert (X10 : getr (ms_regs ms0) 10 = w64 kp).
  { rewrite Q10. rewrite ?ew_ewset_other by lia. exact (te_more_lt regs rg _ 3 ltac:(lia)). }
  assert (X11 : getr (ms_regs ms0) 11 = w64 CRT_MOD_AT_A).
  { rewrite Q11. apply cl_modat_den. rewrite ?ew_ewset_other by lia. apply te_img. unfold A_TEXT, A_LIM. lia. }
  assert (X1 : getr (ms_regs ms0) 1 = Z_to_bv 64 (BASE + (CRT_PC_A + (CRT_CMP1_CALL + 4)))).
  { rewrite Q1. vm_compute. reflexivity. }
  pose proof (cl_dregs_eq rg (ms_regs ms0) F HDR ltac:(intros r Hr; apply KB; cbv [In] in Hr |- *; tauto)) as HDR1.
  pose proof (crt_dregs_bregs HDR1) as HBR1.
  assert (SY : cl_sarg Wc memc CRT_MOD_AT_A (Z.of_nat (length ck_MOD_AT))).
  { apply cl_sarg_cstr. exact (crt_cstr_modat_A LAWS zs_aligned img_shadow_vis_x _ _ _ _ _ _ HARc HRO HKM). }
  pose proof (cl_live_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sp1 sp1 HL HJ HB_HJ ltac:(lia) ltac:(unfold CRT_SP_F; lia)
    (fun a _ _ => eq_refl) (fun a Ha => Ha) HPM) as HL1.
  rewrite <- HF in HL1, SXk, SY.
  apply (cl_strcmp_call fxk Wc _ _ ms0 _ lyc Sc Hpc kj pos _ Lamc peakc _ 0 0 (CRT_CMP1_CALL + 4) kp CRT_MOD_AT_A
    (Z.of_nat (length nm)) (Z.of_nat (length ck_MOD_AT)) HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    HL1 HBR1 X1 ltac:(unfold CRT_CMP1_CALL; lia) ltac:(unfold CRT_CMP1_CALL; lia) X10 X11 SXk SY).
  intros regs2 mem2 md2 v WS_HJ2 HJ2 HB_HJ2 HP Hv Hcmp Hfr Hpr2 Hmn.
  rewrite HF in Hfr, Hpr2, Hmn, Hcmp.
  assert (HES : ESTACK = 4096) by reflexivity.
  change (CRT_sp1 (regs := regs)) with sp1 in Hfr.
  assert (Hlo : forall a, 0 <= a < sp1 - 2 * ESTACK -> aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a).
  { intros a Ha. apply Hfr; lia. }
  assert (Hhi : forall a, sp1 <= a < sp1 + CRT_SP_F -> aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a).
  { intros a Ha. apply Hfr; unfold CRT_SP_F in Ha; lia. }
  pose proof (crt_live_memnorm HL) as HMN0.
  pose proof (cl_rw_keep _ _ _ _ _ memc mem2 _ _ _ _ _ _ _ _ _ _ _ _ _ (sp1 - 2 * ESTACK) sp1 HRW HJ2 HB_HJ2
    ltac:(lia) ltac:(unfold CRT_SP_F; lia) Hfr Hpr2 ltac:(intros H0; exact (Hmn (HMN0 H0)))) as HRW2.
  pose proof (cl_dregs_eq _ regs2 F HDR1 ltac:(intros r Hr; apply (cl_cs_keep _ _ HP); cbv [In] in Hr |- *; tauto)) as HDR2.
  apply (KL1r fxk lyc Sc Hpc Wc mem2 md2 kj pos Dc Lamc peakc cset saved cap Dback ms regs2 i keys nm Hmb).
  destruct HSP2 as (SBK & SSV).
  refine (conj HRW2 (conj (conj _ _) (conj HDR2 (conj Hi (conj Hinv (conj (ex_intro _ u Hnth) (conj _ (conj _ (conj _
    (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))))))).
  + apply (cl_spill_keep Wc memc mem2); [exact Hhi | unfold CRT_SP_BACK; lia | unfold CRT_SP_BACK, CRT_SP_F; lia | exact SBK].
  + apply (cl_spill_keep Wc memc mem2); [exact Hhi | unfold CRT_SP_SAVED; lia | unfold CRT_SP_SAVED, CRT_SP_F; lia | exact SSV].
  + rewrite (cl_cs_keep _ _ HP 22%bv) by (cbv [In]; tauto). rewrite KB by (cbv [In]; tauto). exact R22.
  + rewrite (cl_cs_keep _ _ HP 24%bv) by (cbv [In]; tauto). rewrite KB by (cbv [In]; tauto). exact R24.
  + rewrite (cl_cs_keep _ _ HP 25%bv) by (cbv [In]; tauto). rewrite KB by (cbv [In]; tauto). exact R25.
  + destruct Hkeys as [Hk0 Hk1]. split; [exact Hk0|]. apply (ts_vm_av (w_H Wc) (w_H Wc) memc mem2); [|exact Hk1].
    intros j Hj. apply Hlo. unfold PJ_OFF_KEYS. lia.
  + apply (cl_spill_keep Wc memc mem2); [exact Hhi | unfold CL_SP_P; lia | unfold CL_SP_P, CRT_SP_F; lia | exact SP].
  + apply (cl_spill_keep Wc memc mem2); [exact Hhi | unfold CL_SP_LIT; lia | unfold CL_SP_LIT, CRT_SP_F; lia | exact SLIT].
  + apply (cl_spill_keep Wc memc mem2); [exact Hhi | unfold CRT_SP_SHN; lia | unfold CRT_SP_SHN, CRT_SP_F; lia | exact SSHN].
  + apply (cl_spill_keep Wc memc mem2); [exact Hhi | unfold CRT_SP_PN; lia | unfold CRT_SP_PN, CRT_SP_F; lia | exact SPN].
  + apply (cl_spill_keep Wc memc mem2); [exact Hhi | unfold CRT_SP_N; lia | unfold CRT_SP_N, CRT_SP_F; lia | exact SN].
  + rewrite Hv. rewrite Hcmp.
    pose proof Hcstr as (_ & _ & _ & (_ & Gk)).
    pose proof (crt_cstr_modat_A LAWS zs_aligned img_shadow_vis_x _ _ _ _ _ _ HARc HRO HKM) as ((Gm & _) & _).
    exact (cl_str_eq (w_H Wc) memc kp CRT_MOD_AT_A nm ck_MOD_AT Gk Gm).
Qed.
End L1.

(* ---- L1r's entry state (extras: 64 = n, 65 = keys, 66 = saved, 68 = shadow (keys); 67 unused) ---- *)
Lemma cl_L1r_entry : forall (fxk : YK11.FPState) (Wc : world SEGS) memc rg n keys saved F i cs,
  conds_ok (TE regs rg [w64 n; w64 keys; w64 saved; w64 0; w64 (shadow_addr keys)]) cs ->
  getr rg 9 = w64 (CRT_sp1 (regs := regs)) -> getr rg 21 = w64 doc -> getr rg 22 = w64 (Z.of_nat i) ->
  getr rg 25 = w64 (keys + 8 * Z.of_nat i) -> getr rg 26 = w64 SHADOW_OFF -> getr rg 27 = w64 F ->
  2 ^ 46 <= CRT_sp1 (regs := regs) -> CRT_sp1 (regs := regs) + 96 <= 2 ^ 47 -> CRT_sp1 (regs := regs) mod 32 = 0 ->
  4096 <= doc -> doc + 56 <= CRT_sp1 (regs := regs) -> 0 <= F -> F + 512 <= CRT_sp1 (regs := regs) ->
  4096 <= keys -> keys mod 8 = 0 -> keys + 8 * Z.of_nat i + 8 <= CRT_sp1 (regs := regs) ->
  Z.of_nat i < n -> n <= 2 ^ 54 -> 0 <= saved < 2 ^ 64 ->
  cl_sp2 Wc memc F saved ->
  crt_spill (regs := regs) Wc memc CL_SP_P (doc + PJ_OFF_KEYS) ->
  crt_spill (regs := regs) Wc memc CL_SP_LIT CRT_MOD_AT_A ->
  crt_spill (regs := regs) Wc memc CRT_SP_SHN (shadow_addr keys) ->
  crt_spill (regs := regs) Wc memc CRT_SP_PN n -> crt_spill (regs := regs) Wc memc CRT_SP_N n ->
  st_ok_pi SEGS VAL (TE regs rg [w64 n; w64 keys; w64 saved; w64 0; w64 (shadow_addr keys)]) (ss_L1r cs)
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_A + (CRT_CMP1_CALL + 4)))) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS CL_Bx [] (TE regs rg [w64 n; w64 keys; w64 saved; w64 0; w64 (shadow_addr keys)]) (mrestrict (w_H Wc) memc).
Proof.
intros fxk Wc memc rg n keys saved F i cs Hcs R9 R21 R22 R25 R26 R27 H1 H2 H3 H4 H5 HF0 HF1 Hk4 Hk8 Hkc Hin Hn Hsv
  (VBK & VSV) VP VLIT VSHN VPN VN.
unfold crt_spill, CL_SP_P, CL_SP_LIT, CRT_SP_SHN, CRT_SP_PN, CRT_SP_N, CRT_SP_BACK, CRT_SP_SAVED, CRT_OFF_BACK,
  PJ_OFF_KEYS in *.
set (sp1 := CRT_sp1 (regs := regs)) in *.
set (E := TE regs rg [w64 n; w64 keys; w64 saved; w64 0; w64 (shadow_addr keys)]).
assert (Hsh : 0 <= shadow_addr keys < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos keys 8 ltac:(lia) ltac:(lia)).
  assert (keys / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
assert (W9 : ew E (xr 9) = w64 sp1) by (unfold E, xr; rewrite (te_cur regs rg _ 9%bv 9) by reflexivity; exact R9).
assert (W21 : ew E (xr 21) = w64 doc) by (unfold E, xr; rewrite (te_cur regs rg _ 21%bv 21) by reflexivity; exact R21).
assert (W22 : ew E (xr 22) = w64 (Z.of_nat i)) by (unfold E, xr; rewrite (te_cur regs rg _ 22%bv 22) by reflexivity; exact R22).
assert (W25 : ew E (xr 25) = w64 (keys + 8 * Z.of_nat i))
  by (unfold E, xr; rewrite (te_cur regs rg _ 25%bv 25) by reflexivity; exact R25).
assert (W26 : ew E (xr 26) = w64 SHADOW_OFF) by (unfold E, xr; rewrite (te_cur regs rg _ 26%bv 26) by reflexivity; exact R26).
assert (W27 : ew E (xr 27) = w64 F) by (unfold E, xr; rewrite (te_cur regs rg _ 27%bv 27) by reflexivity; exact R27).
assert (E64 : ew E 64 = w64 n) by exact (te_more_lt regs rg _ 0 ltac:(lia)).
assert (E66 : ew E 66 = w64 saved) by exact (te_more_lt regs rg _ 2 ltac:(lia)).
assert (E68 : ew E 68 = w64 (shadow_addr keys)) by exact (te_more_lt regs rg _ 4 ltac:(lia)).
assert (UB : forall k v, ew E k = w64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E k) = v)
  by (intros k v Hk Hv; rewrite Hk; apply unsigned_lit_small; exact Hv).
split; [|unfold sh_ok; apply Forall_nil].
apply ts_st_ok.
all: try change (TE regs rg [w64 n; w64 keys; w64 saved; w64 0; w64 (shadow_addr keys)]) with E.
- apply te_regs_ok.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
  apply (ts_rok E _ (xr 9) sp1); [apply UB; [exact W9 | lia] | lia | lia | intros o Ho; lia |].
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (ts_chunk E _ _ 24 8 (SOff 66 0) saved); [| cbn; lia | cbn; lia | exact VSV].
    rewrite denot_lit_U, (U_atom_off E 66 saved 0 E66) by lia. rewrite Z.add_0_r. reflexivity.
  + apply (ts_chunk E _ _ 48 8 (SOff (xr 21) 32) (doc + 32)); [| cbn; lia | cbn; lia | exact VP].
    rewrite denot_lit_U, (U_atom_off E (xr 21) doc 32 W21) by lia. reflexivity.
  + apply (ts_chunk E _ _ 56 8 (SOff (xr 27) 32) (F + 32)); [| cbn; lia | cbn; lia | exact VBK].
    rewrite denot_lit_U, (U_atom_off E (xr 27) F 32 W27) by lia. reflexivity.
  + apply (ts_chunk E _ _ 64 8 (SOff 243 69824) CRT_MOD_AT_A); [| pose proof cl_lit_rng; cbn; lia | cbn; lia | exact VLIT].
    apply cl_modat_den. unfold E. apply te_img. unfold A_TEXT, A_LIM. lia.
  + apply (ts_chunk E _ _ 72 8 (SOff 68 0) (shadow_addr keys)); [| cbn; lia | cbn; lia | exact VSHN].
    rewrite denot_lit_U, (U_atom_off E 68 (shadow_addr keys) 0 E68) by lia. rewrite Z.add_0_r. reflexivity.
  + apply (ts_chunk E _ _ 80 8 (SOff 64 0) n); [| cbn; lia | cbn; lia | exact VPN].
    rewrite denot_lit_U, (U_atom_off E 64 n 0 E64) by lia. rewrite Z.add_0_r. reflexivity.
  + apply (ts_chunk E _ _ 88 8 (SOff 64 0) n); [| cbn; lia | cbn; lia | exact VN].
    rewrite denot_lit_U, (U_atom_off E 64 n 0 E64) by lia. rewrite Z.add_0_r. reflexivity.
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !ts_bv_some.
  cbn [zpairwise_disjoint zall_disjoint]. tauto.
- split; [|split; [exact Hcs | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite (UB _ _ W9 ltac:(lia)), (UB _ _ W25 ltac:(lia)), (UB _ _ W26 ltac:(unfold SHADOW_OFF; lia)),
    (UB _ _ W22 ltac:(lia)), (UB _ _ E64 ltac:(lia)).
  change (2 ^ 5) with 32. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
  unfold SHADOW_OFF. repeat split; lia.
Qed.

(* the search's end: no key below n is MOD_AT, so the index is n *)
Lemma cl_at_end : forall ms0, cm_at_inv ms0 (length ms0) (length ms0) -> cm_at ms0 = length ms0.
Proof.
intros ms0 Hinv. unfold cm_at_inv in Hinv. destruct Hinv as (_ & [(_ & Hno) | (Ea & Hlt)]); [|lia].
apply (proj2 (cm_at_out ms0)). intros Hin. apply in_map_iff in Hin as ([nm u] & Hnm & Hin). cbn in Hnm. subst nm.
apply In_nth_error in Hin as (j & Hj). pose proof (proj1 (nth_error_Some ms0 j) ltac:(rewrite Hj; discriminate)).
exact (Hno j _ _ H Hj eq_refl).
Qed.

Section L1ret.
Variable mb : nat.
Hypothesis KL1n : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i keys,
  (length ms - i < mb)%nat ->
  cl_at_L1 fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i keys ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk CRT_L1_OFF rg memc mdc) QFa.
Hypothesis KL2 : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg,
  cl_at_L2 fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk CRT_L2_OFF rg memc mdc) QFa.

(* ---- L1r -> L1 (i + 1) or L2: a2 = i on a hit, n on a miss; s6 = i + 1; `bgeu s6, n` and `beq a2, n` close the loop
   (new:742's `i < doc->n && at == doc->n`) ---- *)
Lemma cl_L1_ret : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i keys nm,
  (length ms - i <= mb)%nat ->
  cl_at_L1r fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i keys nm ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk (CRT_CMP1_CALL + 4) rg memc mdc) QFa.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i keys nm Hmb HL1r.
destruct HL1r as (HRW & HSP2 & HDR & Hi & Hinv & (u & Hnth) & R22 & R24 & R25 & Hkeys & SP & SLIT & SSHN & SPN & SN & Hv).
pose proof HRW as (Et & HFZ & HFK & HL & Hcs & Hcin & Hsv & Hcopy & Hback & Hd8 & Hrad & Hrab & Hrav & Hpos).
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ).
pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPl.
pose proof (crt_live_frame HL) as HFRM.
pose proof (crt_live_memnorm HL) as HPM.
pose proof (crt_side_ledger HSD) as HLD.
pose proof (crt_side_arodata HSD) as HRO.
pose proof (crt_side_doc HSD) as HDOC.
pose proof (crt_side_doc_blocks HSD) as HDL.
pose proof HJ as (HARc & _).
rewrite Et in HDOC.
destruct (cl_obj_key _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLD HDOC HDL Hkeys Hnth)
  as (kp & kb & Hkp & Hcstr & Hinkb & SXk & Hraslot & Hk4 & Hk8 & Hkce & _).
pose proof (crt_dregs_bregs HDR) as Hrec4.
pose proof (crt_bregs_sp Hrec4) as R2.
pose proof (crt_bregs_gp Hrec4) as R3.
pose proof (crt_bregs_tp Hrec4) as R4.
pose proof (crt_bregs_s0 Hrec4) as R8.
pose proof (crt_bregs_s1 Hrec4) as R9.
pose proof (crt_bregs_s2 Hrec4) as R18.
pose proof (crt_bregs_s4 Hrec4) as R20.
pose proof (crt_bregs_s3 Hrec4) as R19.
pose proof (crt_bregs_s7 Hrec4) as R23.
pose proof (crt_bregs_s10 Hrec4) as R26.
pose proof (crt_bregs_s11 Hrec4) as R27.
pose proof (crt_dregs_s5 HDR) as R21.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cl_sp0 as (H16 & Hsp0 & H47). pose proof cl_sp1 as (Hs32 & Hs1).
assert (HSTKC : STKC = 27632) by (vm_compute; reflexivity).
pose proof cl_doc_low as (Hdl0 & Hdl1).
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc (crt_frame_listed HFRM))
  as (Fb1 & Fb2 & Fb3).
change (fs_frame_bytes CRT_CID) with 512 in Fb2.
set (F := frame_addr lyc CRT_CID pos) in *.
set (sp1 := CRT_sp1 (regs := regs)) in *.
assert (Hsv0 : 4096 <= saved < 2 ^ 47).
{ assert (Hin : In (saved, cap) Lamc).
  { apply (Permutation_in _ (Permutation_sym HPl)). apply in_or_app. left. apply in_or_app. right. left. reflexivity. }
  destruct (cl_blk_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLD Hin) as (Hk & Ha & Hb).
  pose proof YM05.alloc_ceiling_lt. change (@cf_head CfParams_preset) with 16 in Ha. lia. }
set (n := Z.of_nat (length ms)) in *.
assert (En : n = Z.of_nat (length ms)) by reflexivity.
assert (Hn54 : n <= 2 ^ 54) by (unfold n in *; lia).
set (E := TE regs rg [w64 n; w64 keys; w64 saved; w64 0; w64 (shadow_addr keys)]).
assert (A10 : ew E (xr 10) = getr rg 10) by (unfold E, xr; apply (te_cur regs rg _ 10%bv 10); reflexivity).
assert (W22 : ew E (xr 22) = w64 (Z.of_nat i)) by (unfold E, xr; rewrite (te_cur regs rg _ 22%bv 22) by reflexivity; exact R22).
assert (E64 : ew E 64 = w64 n) by exact (te_more_lt regs rg _ 0 ltac:(lia)).
assert (UI : U E (SOff (xr 22) 0) = Z.of_nat i) by (apply (U_atom E _ _ W22); lia).
assert (UI1 : U E (SOff (xr 22) 1) = Z.of_nat i + 1) by (apply (U_atom_off E _ _ 1 W22); lia).
assert (UN : U E (SOff 64 0) = n) by (apply (U_atom E _ _ E64); lia).
assert (UA : U E (SOff (xr 10) 0) = bv_unsigned (getr rg 10)) by (rewrite ts_U0, A10; reflexivity).
assert (Ha0 : bv_unsigned (getr rg 10) = 0 <-> nm = ck_MOD_AT).
{ rewrite <- Hv. split; intros H0.
  - apply bv_eq. rewrite H0. reflexivity.
  - rewrite H0. reflexivity. }
pose (RUNTO := @crt_run_to_xw_inv fxk rc SK A_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (YSRrMemnorm.srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)) WS_HJ).
assert (HEI : img_env VAL A_LIM E) by apply te_env.
unfold crt_cfg.
assert (Hin_n : Z.of_nat i < n) by (unfold n; lia).
assert (Hkc : keys + 8 * Z.of_nat i + 8 <= sp1) by (pose proof YM05.alloc_ceiling_lt; unfold n in *; lia).
assert (ENTRY : forall cs, conds_ok E cs ->
  st_ok_pi SEGS VAL E (ss_L1r cs)
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_A + (CRT_CMP1_CALL + 4)))) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS CL_Bx [] E (mrestrict (w_H Wc) memc)).
{ intros cs Hcs0. exact (cl_L1r_entry fxk Wc memc rg n keys saved F i cs Hcs0 R9 R21 R22 R25 R26 R27
    ltac:(lia) ltac:(lia) Hs32 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hk4 Hk8 Hkc Hin_n Hn54 ltac:(lia)
    HSP2 SP SLIT SSHN SPN SN). }
(* the run's end, common to the four arms: nothing written, the kept registers, the spills *)
assert (FIN : forall ms0 md0 kj0,
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc memc md0 kj0 WS_HJ ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 26; 27]%bv -> getr (ms_regs ms0) r = getr rg r) ->
  cl_rw fxk lyc Sc Hpc Wc memc md0 kj0 pos Dc Lamc peakc cset saved cap Dback ms /\
  crt_dregs (regs := regs) (doc := doc) (ms_regs ms0) F).
{ intros ms0 md0 kj0 HJ0 KB. split.
  - exact (cl_rw_keep _ _ _ _ _ memc memc _ _ _ _ _ _ _ _ _ _ _ _ _ sp1 sp1 HRW HJ0 HB_HJ ltac:(lia)
      ltac:(unfold CRT_SP_F; lia) ltac:(intros a _ _; reflexivity) ltac:(intros a Ha; exact Ha) (crt_live_memnorm HL)).
  - exact (cl_dregs_eq rg (ms_regs ms0) F HDR KB). }
assert (UBi : U E (SOff (xr 22) 0) = Z.of_nat i) by exact UI.
assert (UI' : U E (SOff 54 0) = Z.of_nat i) by exact UI.
assert (UI1' : U E (SOff 54 1) = Z.of_nat i + 1) by exact UI1.
destruct (list_eq_dec Z.eq_dec nm ck_MOD_AT) as [Em | Em].
- (* ---- a hit: at = i (cm_at_inv_hit), to L2 whichever way `bgeu s6, n` goes ---- *)
  destruct (cm_at_inv_hit ms i (length ms) u Hinv eq_refl ltac:(rewrite <- Em; exact Hnth)) as (Eat & _).
  assert (Ha00 : bv_unsigned (getr rg 10) = 0) by (apply Ha0; exact Em).
  destruct (Nat.lt_ge_cases (Datatypes.S i) (length ms)) as [Hl | Hl].
  +   assert (Hcs0 : conds_ok E cl_cA1).
    { unfold cl_cA1. cbn [conds_ok]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_eq_U, UA, U_SLit, Ha00; reflexivity|]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_ltu_U, ?UI1, ?UI1', UN; apply Z.ltb_lt; unfold n; lia|]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_ne_U, ?UI, ?UI', UN; apply negb_true_iff, Z.eqb_neq; lia|]. exact I. }
    destruct (ENTRY cl_cA1 Hcs0) as [HS SHOK].
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM CL_SPAN (CRT_PC_A + CRT_L2_OFF).
    all: try (lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end;
      repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil).
    apply frame_of_read_only in HF; [|vm_compute; reflexivity].
    rewrite HF in HJ, HPM. clear HFr HG.
    assert (KB : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 26; 27]%bv -> getr (ms_regs ms0) r = getr rg r).
    { intros r Hr. unfold E in HS. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [clkeep HS |]). destruct Hr. }
    destruct (FIN ms0 _ _ HJ KB) as (HRW1 & HDR1).
    pmkst HS. rewrite HF.
    lazymatch goal with |- context [Z_to_bv 64 (BASE + ?pc)] =>
      replace pc with (CRT_PC_A + CRT_L2_OFF) by (vm_compute; reflexivity) end.
    apply (KL2 fxk lyc Sc Hpc Wc memc _ kj pos Dc Lamc peakc cset saved cap Dback ms (ms_regs ms0)).
    prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
    refine (conj HRW1 (conj HSP2 (conj HDR1 (conj _ (conj _ (conj SP (conj SPN SN))))))).
    * rewrite Q12, <- Eat. first [exact W22 | (rewrite denot_lit_U; f_equal; exact UI')].
    * rewrite Q13, (cl_eqflag_w (ew E 54) (ew E 64) (Z.of_nat i) n) by
        (first [change 54%nat with (xr 22); rewrite W22 | rewrite E64]; apply unsigned_lit_small; lia).
      rewrite <- Eat. rewrite (proj2 (Z.eqb_neq _ _)) by lia. rewrite (proj2 (Nat.eqb_neq _ _)) by lia. reflexivity.

  +   assert (Hcs0 : conds_ok E cl_cA2).
    { unfold cl_cA2. cbn [conds_ok]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_eq_U, UA, U_SLit, Ha00; reflexivity|]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_geu_U, ?UI1, ?UI1', UN; apply negb_true_iff, Z.ltb_ge; unfold n; lia|]. exact I. }
    destruct (ENTRY cl_cA2 Hcs0) as [HS SHOK].
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM CL_SPAN (CRT_PC_A + CRT_L2_OFF).
    all: try (lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end;
      repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil).
    apply frame_of_read_only in HF; [|vm_compute; reflexivity].
    rewrite HF in HJ, HPM. clear HFr HG.
    assert (KB : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 26; 27]%bv -> getr (ms_regs ms0) r = getr rg r).
    { intros r Hr. unfold E in HS. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [clkeep HS |]). destruct Hr. }
    destruct (FIN ms0 _ _ HJ KB) as (HRW1 & HDR1).
    pmkst HS. rewrite HF.
    lazymatch goal with |- context [Z_to_bv 64 (BASE + ?pc)] =>
      replace pc with (CRT_PC_A + CRT_L2_OFF) by (vm_compute; reflexivity) end.
    apply (KL2 fxk lyc Sc Hpc Wc memc _ kj pos Dc Lamc peakc cset saved cap Dback ms (ms_regs ms0)).
    prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
    refine (conj HRW1 (conj HSP2 (conj HDR1 (conj _ (conj _ (conj SP (conj SPN SN))))))).
    * rewrite Q12, <- Eat. first [exact W22 | (rewrite denot_lit_U; f_equal; exact UI')].
    * rewrite Q13, (cl_eqflag_w (ew E 54) (ew E 64) (Z.of_nat i) n) by
        (first [change 54%nat with (xr 22); rewrite W22 | rewrite E64]; apply unsigned_lit_small; lia).
      rewrite <- Eat. rewrite (proj2 (Z.eqb_neq _ _)) by lia. rewrite (proj2 (Nat.eqb_neq _ _)) by lia. reflexivity.

- (* ---- a miss: a2 = n; i + 1 < n back to L1 (the measure length ms - i drops), else the search ends at L2 ---- *)
  assert (Ha01 : bv_unsigned (getr rg 10) <> 0) by (intros H0; apply Em, Ha0, H0).
  pose proof (bv_unsigned_in_range 64 (getr rg 10)) as Ra10. change (bv_modulus 64) with (2 ^ 64) in Ra10.
  destruct (Nat.lt_ge_cases (Datatypes.S i) (length ms)) as [Hl | Hl].
  +   assert (Hcs0 : conds_ok E cl_cB1).
    { unfold cl_cB1. cbn [conds_ok]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_ne_U, UA, U_SLit; apply negb_true_iff, Z.eqb_neq; rewrite zcanon_id by (unfold M64; lia); exact Ha01|]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_ltu_U, ?UI1, ?UI1', UN; apply Z.ltb_lt; unfold n; lia|]. exact I. }
    destruct (ENTRY cl_cB1 Hcs0) as [HS SHOK].
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM CL_SPAN (CRT_PC_A + CRT_L1_OFF).
    all: try (lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end;
      repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil).
    apply frame_of_read_only in HF; [|vm_compute; reflexivity].
    rewrite HF in HJ, HPM. clear HFr HG.
    assert (KB : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 26; 27]%bv -> getr (ms_regs ms0) r = getr rg r).
    { intros r Hr. unfold E in HS. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [clkeep HS |]). destruct Hr. }
    destruct (FIN ms0 _ _ HJ KB) as (HRW1 & HDR1).
    pmkst HS. rewrite HF.
    lazymatch goal with |- context [Z_to_bv 64 (BASE + ?pc)] =>
      replace pc with (CRT_PC_A + CRT_L1_OFF) by (vm_compute; reflexivity) end.
    apply (KL1n fxk lyc Sc Hpc Wc memc _ kj pos Dc Lamc peakc cset saved cap Dback ms (ms_regs ms0) (Datatypes.S i) keys ltac:(lia)).
    prreg HS (22%bv : bv 5) Q22. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
    assert (W24 : ew E 56 = w64 (keys + 8 * Z.of_nat i))
      by (change 56%nat with (xr 24); unfold E, xr; rewrite (te_cur regs rg _ 24%bv 24) by reflexivity; exact R24).
    assert (W25 : ew E 57 = w64 (keys + 8 * Z.of_nat i))
      by (change 57%nat with (xr 25); unfold E, xr; rewrite (te_cur regs rg _ 25%bv 25) by reflexivity; exact R25).
    refine (conj HRW1 (conj HSP2 (conj HDR1 (conj Hl (conj (cm_at_inv_miss ms i (length ms) nm u Hinv eq_refl Hnth Em)
      (conj _ (conj _ (conj _ (conj Hkeys (conj SP (conj SLIT (conj SSHN (conj SPN SN))))))))))))).
    * rewrite Q22. change 54%nat with (xr 22). rewrite W22. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia.
    * rewrite Q24, W24. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia.
    * rewrite Q25, W25. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia.

  +   assert (Hcs0 : conds_ok E cl_cB2).
    { unfold cl_cB2. cbn [conds_ok]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_ne_U, UA, U_SLit; apply negb_true_iff, Z.eqb_neq; rewrite zcanon_id by (unfold M64; lia); exact Ha01|]. split; [unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite branch_geu_U, ?UI1, ?UI1', UN; apply negb_true_iff, Z.ltb_ge; unfold n; lia|]. exact I. }
    destruct (ENTRY cl_cB2 Hcs0) as [HS SHOK].
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM CL_SPAN (CRT_PC_A + CRT_L2_OFF).
    all: try (lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end;
      repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil).
    apply frame_of_read_only in HF; [|vm_compute; reflexivity].
    rewrite HF in HJ, HPM. clear HFr HG.
    assert (KB : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 26; 27]%bv -> getr (ms_regs ms0) r = getr rg r).
    { intros r Hr. unfold E in HS. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [clkeep HS |]). destruct Hr. }
    destruct (FIN ms0 _ _ HJ KB) as (HRW1 & HDR1).
    pmkst HS. rewrite HF.
    lazymatch goal with |- context [Z_to_bv 64 (BASE + ?pc)] =>
      replace pc with (CRT_PC_A + CRT_L2_OFF) by (vm_compute; reflexivity) end.
    apply (KL2 fxk lyc Sc Hpc Wc memc _ kj pos Dc Lamc peakc cset saved cap Dback ms (ms_regs ms0)).
    prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
    assert (Eat : cm_at ms = length ms).
    { apply cl_at_end. pose proof (cm_at_inv_miss ms i (length ms) nm u Hinv eq_refl Hnth Em) as H1.
      replace (Datatypes.S i) with (length ms) in H1 by lia. exact H1. }
    refine (conj HRW1 (conj HSP2 (conj HDR1 (conj _ (conj _ (conj SP (conj SPN SN))))))).
    * rewrite Q12, Eat. first [exact E64 | (rewrite denot_lit_U; f_equal; exact UN)].
    * rewrite Q13, (cl_eqflag_w (ew E 64) (ew E 64) n n) by (rewrite E64; apply unsigned_lit_small; lia).
      rewrite Z.eqb_refl, Eat, Nat.eqb_refl. reflexivity.

Qed.
End L1ret.

(* ---- THE AT-SEARCH CLOSED BY THE MEASURE length ms - i (S10TxString.v's ts_loop pattern): each iteration either
   leaves for L2 or re-enters L1 at i + 1 with a strictly smaller measure ---- *)
Section L1loop.
Hypothesis KL2 : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg,
  cl_at_L2 fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk CRT_L2_OFF rg memc mdc) QFa.
Lemma cl_L1_loop : forall mb fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i keys,
  (length ms - i <= mb)%nat ->
  cl_at_L1 fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i keys ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk CRT_L1_OFF rg memc mdc) QFa.
Proof.
induction mb as [|mb IH]; intros fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i keys Hmb HL1.
- exfalso. destruct HL1 as (_ & _ & _ & Hi & _). lia.
- apply (cl_L1_head (Datatypes.S mb)
    (fun fxk' lyc' Sc' Hpc' Wc' memc' mdc' kj' pos' Dc' Lamc' peakc' cset' saved' cap' Dback' ms' rg' i' keys' nm' Hm' H' =>
       cl_L1_ret (Datatypes.S mb)
         (fun fxk'' lyc'' Sc'' Hpc'' Wc'' memc'' mdc'' kj'' pos'' Dc'' Lamc'' peakc'' cset'' saved'' cap'' Dback'' ms'' rg''
              i'' keys'' Hlt H'' =>
            IH fxk'' lyc'' Sc'' Hpc'' Wc'' memc'' mdc'' kj'' pos'' Dc'' Lamc'' peakc'' cset'' saved'' cap'' Dback'' ms'' rg''
              i'' keys'' ltac:(lia) H'')
         KL2 fxk' lyc' Sc' Hpc' Wc' memc' mdc' kj' pos' Dc' Lamc' peakc' cset' saved' cap' Dback' ms' rg' i' keys' nm' Hm' H')
    fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i keys Hmb HL1).
Qed.
End L1loop.

(* ---- L2's entry state (extras: 64 = n, 65 = doc->keys, 66 = saved, 67 = doc->kids, 68 = back.kids, 69 = back.keys,
   70 = back.n) ---- *)
Lemma cl_L2_entry : forall (fxk : YK11.FPState) (Wc : world SEGS) memc rg n dkeys saved dkids bkids bkeys bn F atv fl cs,
  conds_ok (TE regs rg [w64 n; w64 dkeys; w64 saved; w64 dkids; w64 bkids; w64 bkeys; w64 bn]) cs ->
  getr rg 9 = w64 (CRT_sp1 (regs := regs)) -> getr rg 21 = w64 doc -> getr rg 26 = w64 SHADOW_OFF ->
  getr rg 27 = w64 F -> getr rg 12 = w64 atv -> getr rg 13 = w64 fl -> 0 <= atv <= 2 ^ 54 -> 0 <= fl <= 1 ->
  2 ^ 46 <= CRT_sp1 (regs := regs) -> CRT_sp1 (regs := regs) + 96 <= 2 ^ 47 -> CRT_sp1 (regs := regs) mod 32 = 0 ->
  4096 <= doc -> doc + 56 <= CRT_sp1 (regs := regs) -> doc mod 8 = 0 ->
  4096 <= F -> F + 512 <= CRT_sp1 (regs := regs) -> F mod 32 = 0 -> (doc + 56 <= F \/ F + 512 <= doc) ->
  0 <= n <= 2 ^ 54 -> 0 <= bn <= 2 ^ 54 -> 0 <= saved < 2 ^ 64 ->
  (forall a, CRT_sp1 (regs := regs) + 32 <= a < CRT_sp1 (regs := regs) + 96 -> apresent (w_H Wc) memc a) ->
  cl_sp2 Wc memc F saved ->
  crt_spill (regs := regs) Wc memc CL_SP_P (doc + PJ_OFF_KEYS) ->
  crt_spill (regs := regs) Wc memc CRT_SP_PN n -> crt_spill (regs := regs) Wc memc CRT_SP_N n ->
  rd_u64 SEGS (mrestrict (w_H Wc) memc) (F + 56) bkids -> rd_u64 SEGS (mrestrict (w_H Wc) memc) (F + 64) bkeys ->
  rd_u64 SEGS (mrestrict (w_H Wc) memc) (F + 72) bn ->
  rd_u64 SEGS (mrestrict (w_H Wc) memc) (doc + 24) dkids -> rd_u64 SEGS (mrestrict (w_H Wc) memc) (doc + 32) dkeys ->
  rd_u64 SEGS (mrestrict (w_H Wc) memc) (doc + 40) n ->
  st_ok_pi SEGS VAL (TE regs rg [w64 n; w64 dkeys; w64 saved; w64 dkids; w64 bkids; w64 bkeys; w64 bn]) (ss_L2 cs)
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_A + CRT_L2_OFF))) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS CL_Bx [] (TE regs rg [w64 n; w64 dkeys; w64 saved; w64 dkids; w64 bkids; w64 bkeys; w64 bn])
    (mrestrict (w_H Wc) memc).
Proof.
intros fxk Wc memc rg n dkeys saved dkids bkids bkeys bn F atv fl cs Hcs R9 R21 R26 R27 R12 R13 Ha Hfl H1 H2 H3
  H4 H5 H6 HF0 HF1 HF2 HdF Hn Hbn Hsv HP (VBK & VSV) VP VPN VN [Rbk VBKIDS] [Rbke VBKEYS] [Rbn VBN]
  [Rdk VDKIDS] [Rdke VDKEYS] [_ VDN].
unfold crt_spill, CL_SP_P, CRT_SP_PN, CRT_SP_N, CRT_SP_BACK, CRT_SP_SAVED, CRT_OFF_BACK, PJ_OFF_KEYS in *.
set (sp1 := CRT_sp1 (regs := regs)) in *.
set (E := TE regs rg [w64 n; w64 dkeys; w64 saved; w64 dkids; w64 bkids; w64 bkeys; w64 bn]).
assert (W9 : ew E (xr 9) = w64 sp1) by (unfold E, xr; rewrite (te_cur regs rg _ 9%bv 9) by reflexivity; exact R9).
assert (W21 : ew E (xr 21) = w64 doc) by (unfold E, xr; rewrite (te_cur regs rg _ 21%bv 21) by reflexivity; exact R21).
assert (W26 : ew E (xr 26) = w64 SHADOW_OFF) by (unfold E, xr; rewrite (te_cur regs rg _ 26%bv 26) by reflexivity; exact R26).
assert (W27 : ew E (xr 27) = w64 F) by (unfold E, xr; rewrite (te_cur regs rg _ 27%bv 27) by reflexivity; exact R27).
assert (W12 : ew E (xr 12) = w64 atv) by (unfold E, xr; rewrite (te_cur regs rg _ 12%bv 12) by reflexivity; exact R12).
assert (W13 : ew E (xr 13) = w64 fl) by (unfold E, xr; rewrite (te_cur regs rg _ 13%bv 13) by reflexivity; exact R13).
assert (E64 : ew E 64 = w64 n) by exact (te_more_lt regs rg _ 0 ltac:(lia)).
assert (E65 : ew E 65 = w64 dkeys) by exact (te_more_lt regs rg _ 1 ltac:(lia)).
assert (E66 : ew E 66 = w64 saved) by exact (te_more_lt regs rg _ 2 ltac:(lia)).
assert (E67 : ew E 67 = w64 dkids) by exact (te_more_lt regs rg _ 3 ltac:(lia)).
assert (E68 : ew E 68 = w64 bkids) by exact (te_more_lt regs rg _ 4 ltac:(lia)).
assert (E69 : ew E 69 = w64 bkeys) by exact (te_more_lt regs rg _ 5 ltac:(lia)).
assert (E70 : ew E 70 = w64 bn) by exact (te_more_lt regs rg _ 6 ltac:(lia)).
assert (UB : forall k v, ew E k = w64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E k) = v)
  by (intros k v Hk Hv; rewrite Hk; apply unsigned_lit_small; exact Hv).
split; [|unfold sh_ok; apply Forall_nil].
apply ts_st_ok.
all: try change (TE regs rg [w64 n; w64 dkeys; w64 saved; w64 dkids; w64 bkids; w64 bkeys; w64 bn]) with E.
- apply te_regs_ok.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
  + apply (ts_rok E _ (xr 9) sp1); [apply UB; [exact W9 | lia] | lia | lia | |].
    { intros o Ho. apply (apresent_writable SEGS). apply HP. cbn in Ho. lia. }
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (ts_chunk E _ _ 24 8 (SOff 66 0) saved); [| cbn; lia | cbn; lia | exact VSV].
      rewrite denot_lit_U, (U_atom_off E 66 saved 0 E66) by lia. rewrite Z.add_0_r. reflexivity.
    * apply (ts_chunk E _ _ 48 8 (SOff (xr 21) 32) (doc + 32)); [| cbn; lia | cbn; lia | exact VP].
      rewrite denot_lit_U, (U_atom_off E (xr 21) doc 32 W21) by lia. reflexivity.
    * apply (ts_chunk E _ _ 56 8 (SOff (xr 27) 32) (F + 32)); [| cbn; lia | cbn; lia | exact VBK].
      rewrite denot_lit_U, (U_atom_off E (xr 27) F 32 W27) by lia. reflexivity.
    * apply (ts_chunk E _ _ 80 8 (SOff 64 0) n); [| cbn; lia | cbn; lia | exact VPN].
      rewrite denot_lit_U, (U_atom_off E 64 n 0 E64) by lia. rewrite Z.add_0_r. reflexivity.
    * apply (ts_chunk E _ _ 88 8 (SOff 64 0) n); [| cbn; lia | cbn; lia | exact VN].
      rewrite denot_lit_U, (U_atom_off E 64 n 0 E64) by lia. rewrite Z.add_0_r. reflexivity.
  + apply (ts_rok E _ (xr 27) F); [apply UB; [exact W27 | lia] | lia | lia | intros o Ho; cbn in Ho; lia |].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (ts_chunk E _ _ 56 8 (SOff 68 0) bkids); [| cbn; lia | cbn; lia | exact VBKIDS].
      rewrite denot_lit_U, (U_atom_off E 68 bkids 0 E68) by lia. rewrite Z.add_0_r. reflexivity.
    * apply (ts_chunk E _ _ 64 8 (SOff 69 0) bkeys); [| cbn; lia | cbn; lia | exact VBKEYS].
      rewrite denot_lit_U, (U_atom_off E 69 bkeys 0 E69) by lia. rewrite Z.add_0_r. reflexivity.
    * apply (ts_chunk E _ _ 72 8 (SOff 70 0) bn); [| cbn; lia | cbn; lia | exact VBN].
      rewrite denot_lit_U, (U_atom_off E 70 bn 0 E70) by lia. rewrite Z.add_0_r. reflexivity.
  + apply (ts_rok E _ (xr 21) doc); [apply UB; [exact W21 | lia] | lia | lia | intros o Ho; cbn in Ho; lia |].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (ts_chunk E _ _ 24 8 (SOff 67 0) dkids); [| cbn; lia | cbn; lia | exact VDKIDS].
      rewrite denot_lit_U, (U_atom_off E 67 dkids 0 E67) by lia. rewrite Z.add_0_r. reflexivity.
    * apply (ts_chunk E _ _ 32 8 (SOff 65 0) dkeys); [| cbn; lia | cbn; lia | exact VDKEYS].
      rewrite denot_lit_U, (U_atom_off E 65 dkeys 0 E65) by lia. rewrite Z.add_0_r. reflexivity.
    * apply (ts_chunk E _ _ 40 8 (SOff 64 0) n); [| cbn; lia | cbn; lia | exact VDN].
      rewrite denot_lit_U, (U_atom_off E 64 n 0 E64) by lia. rewrite Z.add_0_r. reflexivity.
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !ts_bv_some.
  rewrite (UB _ _ W9 ltac:(lia)), (UB _ _ W27 ltac:(lia)), (UB _ _ W21 ltac:(lia)).
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact Hcs | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite (UB _ _ W9 ltac:(lia)), (UB _ _ W21 ltac:(lia)), (UB _ _ W26 ltac:(unfold SHADOW_OFF; lia)),
    (UB _ _ W27 ltac:(lia)), (UB _ _ W12 ltac:(lia)), (UB _ _ W13 ltac:(lia)), (UB _ _ E64 ltac:(lia)),
    (UB _ _ E70 ltac:(lia)).
  change (2 ^ 5) with 32. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
  unfold SHADOW_OFF. repeat split; lia.
Qed.

(* ======================================================================================================== *)
(* L2 (+0x528 .. +0x58c): THE PROPERTY ABORT OF new:748 (`back.n != doc->n + (at == doc->n)`, `bne a1, a0` at +0x53c)
   IS UNREACHABLE: back holds the rewritten tree JObj (pj_set_model ms ..), whose member count is
   length ms + (at == length ms) (Crt102Model.cm_set_len), and a3 is exactly (at == n). Then doc->n = 0 goes to C,
   else the member loop's set-up (the +0x740 report is unreachable: doc's 56 bytes are addressable). *)
Section L2.
Hypothesis KL3 : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg bkeys dkeys,
  cl_at_L3 fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg 0 bkeys dkeys ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk CRT_L3_OFF rg memc mdc) QFa.
Hypothesis KC : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg,
  cl_at_C fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk CRT_C_OFF rg memc mdc) QFa.

Lemma cl_L2 : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg,
  cl_at_L2 fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk CRT_L2_OFF rg memc mdc) QFa.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg HL2.
destruct HL2 as (HRW & HSP2 & HDR & R12 & R13 & SP & SPN & SN).
pose proof HRW as (Et & HFZ & HFK & HL & Hcs & Hcin & Hsv & Hcopy & Hback & Hd8 & Hrad & Hrab & Hrav & _).
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ).
pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPl.
pose proof (crt_live_frame HL) as HFRM.
pose proof (crt_live_memnorm HL) as HPM.
pose proof (crt_side_ledger HSD) as HLD.
pose proof (crt_side_arodata HSD) as HRO.
pose proof (crt_side_doc HSD) as HDOC.
pose proof (crt_side_doc_blocks HSD) as HDL.
pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkp & _).
pose proof (crt_dregs_bregs HDR) as Hrec5.
pose proof (crt_bregs_sp Hrec5) as R2.
pose proof (crt_bregs_gp Hrec5) as R3.
pose proof (crt_bregs_tp Hrec5) as R4.
pose proof (crt_bregs_s0 Hrec5) as R8.
pose proof (crt_bregs_s1 Hrec5) as R9.
pose proof (crt_bregs_s2 Hrec5) as R18.
pose proof (crt_bregs_s4 Hrec5) as R20.
pose proof (crt_bregs_s3 Hrec5) as R19.
pose proof (crt_bregs_s7 Hrec5) as R23.
pose proof (crt_bregs_s10 Hrec5) as R26.
pose proof (crt_bregs_s11 Hrec5) as R27.
pose proof (crt_dregs_s5 HDR) as R21.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof YM05.alloc_ceiling_lt as Hc47.
pose proof cl_sp0 as (H16 & Hsp0 & H47). pose proof cl_sp1 as (Hs32 & Hs1).
assert (HSTKC : STKC = 27632) by (vm_compute; reflexivity).
pose proof cl_doc_low as (Hdl0 & Hdl1).
pose proof (cl_doc_F _ _ _ _ _ _ _ _ HJ) as HdF.
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc (crt_frame_listed HFRM))
  as (Fb1 & Fb2 & Fb3).
change (fs_frame_bytes CRT_CID) with 512 in Fb2.
destruct (alx_frames SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc (crt_frame_listed HFRM))
  as (F32 & _).
set (F := frame_addr lyc CRT_CID pos) in *.
set (sp1 := CRT_sp1 (regs := regs)) in *.
(* doc's node and back's node: their header words *)
rewrite Et in HDOC.
destruct (cl_node_obj _ _ _ _ _ HDOC) as (dnum & dkids & dkeys & dcap & Di & _ & _ & Hdh & Hdn & Hdc & EDi & Hdm).
pose proof Hdh as (_ & _ & _ & _ & VDK & VDKE & VDN & _).
assert (Etc : tc = PjTree.JObj (PjTree.pj_set_model ms ck_MOD_AT (PjTree.JStr ck_STAMP))) by (unfold crt_tc; rewrite Et; reflexivity).
rewrite Etc in Hback.
destruct (cl_node_obj _ _ _ _ _ Hback) as (bnum & bkids & bkeys & bcap & Bi & _ & _ & Hbh & Hbn & Hbc & EBi & Hbm).
pose proof Hbh as (_ & _ & _ & _ & VBK & VBKE & VBN & _).
set (n := Z.of_nat (length ms)) in *.
set (psm := PjTree.pj_set_model ms ck_MOD_AT (PjTree.JStr ck_STAMP)) in *.
set (fl := if Nat.eqb (cm_at ms) (length ms) then 1 else 0) in *.
assert (Ebn : Z.of_nat (length psm) = n + fl).
{ unfold psm, n, fl. rewrite cm_set_len. destruct (Nat.eqb (cm_at ms) (length ms)); lia. }
assert (Hfl : 0 <= fl <= 1) by (unfold fl; destruct (Nat.eqb (cm_at ms) (length ms)); lia).
assert (Hat : (cm_at ms <= length ms)%nat) by apply cm_at_le.
assert (HinL : forall bk, In bk (Dback ++ (saved, cap) :: Dc) -> In bk Lamc).
{ intros bk Hb. apply (Permutation_in _ (Permutation_sym HPl)). apply in_or_app. left. exact Hb. }
assert (Hnr : n <= 2 ^ 54).
{ destruct Hdc as [(-> & _ & _) | (Hc0 & Hkd & _)]; [lia|].
  destruct (cl_blk_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLD Hkd) as (_ & Hb0 & Hb).
  change (@cf_head CfParams_preset) with 16 in Hb0. lia. }
assert (Hbnr : Z.of_nat (length psm) <= 2 ^ 54).
{ destruct Hbc as [(-> & _ & _) | (Hc0 & Hkd & _)]; [lia|].
  destruct (cl_blk_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLD (HinL _ ltac:(apply in_or_app; left; rewrite EBi;
    apply in_or_app; left; rewrite (proj2 (Z.eqb_neq bcap 0)) by lia; left; reflexivity))) as (_ & Hb0 & Hb).
  change (@cf_head CfParams_preset) with 16 in Hb0. lia. }
assert (Hsv0 : 4096 <= saved < 2 ^ 47).
{ assert (Hin : In (saved, cap) Lamc) by (apply HinL; apply in_or_app; right; left; reflexivity).
  destruct (cl_blk_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLD Hin) as (Hk & Ha & Hb).
  change (@cf_head CfParams_preset) with 16 in Ha. lia. }
assert (VBK' : rd_u64 SEGS (mrestrict (w_H Wc) memc) (F + 56) bkids)
  by (replace (F + 56) with (F + CRT_OFF_BACK + 24) by (unfold CRT_OFF_BACK; lia); exact VBK).
assert (VBKE' : rd_u64 SEGS (mrestrict (w_H Wc) memc) (F + 64) bkeys)
  by (replace (F + 64) with (F + CRT_OFF_BACK + 32) by (unfold CRT_OFF_BACK; lia); exact VBKE).
assert (VBN' : rd_u64 SEGS (mrestrict (w_H Wc) memc) (F + 72) (Z.of_nat (length psm)))
  by (replace (F + 72) with (F + CRT_OFF_BACK + 40) by (unfold CRT_OFF_BACK; lia); exact VBN).
pose proof VDK as [Rdk _]. pose proof VDKE as [Rdke _]. pose proof VBK as [Rbk _]. pose proof VBKE as [Rbke _].
set (E := TE regs rg [w64 n; w64 dkeys; w64 saved; w64 dkids; w64 bkids; w64 bkeys; w64 (Z.of_nat (length psm))]).
assert (W9 : ew E (xr 9) = w64 sp1) by (unfold E, xr; rewrite (te_cur regs rg _ 9%bv 9) by reflexivity; exact R9).
assert (W12 : ew E (xr 12) = w64 (Z.of_nat (cm_at ms)))
  by (unfold E, xr; rewrite (te_cur regs rg _ 12%bv 12) by reflexivity; exact R12).
assert (W13 : ew E (xr 13) = w64 fl) by (unfold E, xr; rewrite (te_cur regs rg _ 13%bv 13) by reflexivity; exact R13).
assert (W21 : ew E (xr 21) = w64 doc) by (unfold E, xr; rewrite (te_cur regs rg _ 21%bv 21) by reflexivity; exact R21).
assert (W26 : ew E (xr 26) = w64 SHADOW_OFF) by (unfold E, xr; rewrite (te_cur regs rg _ 26%bv 26) by reflexivity; exact R26).
assert (W27 : ew E (xr 27) = w64 F) by (unfold E, xr; rewrite (te_cur regs rg _ 27%bv 27) by reflexivity; exact R27).
assert (W24 : ew E (xr 24) = getr rg 24) by (unfold E, xr; apply (te_cur regs rg _ 24%bv 24); reflexivity).
assert (E64 : ew E 64 = w64 n) by exact (te_more_lt regs rg _ 0 ltac:(lia)).
assert (E65 : ew E 65 = w64 dkeys) by exact (te_more_lt regs rg _ 1 ltac:(lia)).
assert (E69 : ew E 69 = w64 bkeys) by exact (te_more_lt regs rg _ 5 ltac:(lia)).
assert (E70 : ew E 70 = w64 (Z.of_nat (length psm))) by exact (te_more_lt regs rg _ 6 ltac:(lia)).
assert (X41 : bv_unsigned (ew E 41) = sp1) by (change 41%nat with (xr 9); rewrite W9; apply unsigned_lit_small; lia).
assert (UN : U E (SOff 64 0) = n) by (apply (U_atom E _ _ E64); lia).
assert (UBN : U E (SOff 70 0) = Z.of_nat (length psm)) by (apply (U_atom E _ _ E70); lia).
assert (UFL : U E (SOff 45 0) = fl) by (change 45%nat with (xr 13); apply (U_atom E _ _ W13); lia).
assert (HBN : conds_ok E [cl_cBN]).
{ split; [|exact I]. unfold acond_ok, cl_cBN. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U, UBN, U_SAlu.
  change (SOff (xr 13) 0) with (SOff 45 0). rewrite UFL, UN. cbn [zalu_raw]. unfold zcanon, M64.
  rewrite Z.mod_small by lia. apply Z.eqb_eq. lia. }
assert (ENTRY : forall cs, conds_ok E cs ->
  st_ok_pi SEGS VAL E (ss_L2 cs)
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_A + CRT_L2_OFF))) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS CL_Bx [] E (mrestrict (w_H Wc) memc)).
{ intros cs Hcs0. destruct HSP2 as (SBK & SSV).
  exact (cl_L2_entry fxk Wc memc rg n dkeys saved dkids bkids bkeys (Z.of_nat (length psm)) F (Z.of_nat (cm_at ms)) fl cs
    Hcs0 R9 R21 R26 R27 R12 R13 ltac:(lia) Hfl ltac:(lia) ltac:(lia) Hs32 ltac:(lia) ltac:(lia) Hd8 ltac:(lia) ltac:(lia) F32
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros a Ha; apply Hstkp; lia) (conj SBK SSV) SP SPN SN
    VBK' VBKE' VBN' VDK VDKE VDN). }
assert (HEI : img_env VAL A_LIM E) by apply te_env.
pose (RUNTO := @crt_run_to_xw_inv fxk rc SK A_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (YSRrMemnorm.srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)) WS_HJ).
assert (W24v : bv_unsigned (getr rg 24) = saved \/ True) by (right; exact I).
assert (HSP2' := HSP2). destruct HSP2' as (SBK & SSV).
unfold crt_cfg.
destruct (Z.eq_dec n 0) as [Hn0 | Hn0].
- (* ---- doc->n = 0: `beqz a2` to C (+0x634) ---- *)
  assert (Hcs0 : conds_ok E cl_cL2C).
  { unfold cl_cL2C. split; [exact (proj1 HBN)|]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
    rewrite branch_eq_U, UN, U_SLit, Hn0. reflexivity. }
  destruct (ENTRY _ Hcs0) as [HS SHOK].
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM CL_SPAN (CRT_PC_A + CRT_C_OFF).
  all: try (lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end;
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ (xr 9) (sp1 - sp0));
      [reflexivity | change (xr 9) with 41%nat; rewrite X41; lia | cbn; lia | cbn; lia |];
    repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil).
  assert (Hav : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 32 <= a < sp1 + 96) ->
    aview SEGS (w_H Wc) (ms_mem ms0) a = aview SEGS (w_H Wc) memc a).
  { apply (ts_keep Wc _ _ memc (ms_mem ms0) _ HFr). intros a (r & Hri & Hr). vm_compute in Hri.
    repeat (destruct Hri as [<- | Hri]; [cbn [YP09.r_wlo YP09.r_whi YP09.r_base base_val] in Hr; rewrite ?X41 in Hr; lia |]);
      destruct Hri. }
  assert (Hpr : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) (ms_mem ms0) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  pose proof (cl_rw_keep _ _ _ _ _ memc (ms_mem ms0) _ _ _ _ _ _ _ _ _ _ _ _ _ (sp1 + 32) (sp1 + 96) HRW HJ HB_HJ
    ltac:(lia) ltac:(unfold CRT_SP_F; lia) Hav Hpr HPM) as HRW1.
  assert (KB : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 23; 26; 27]%bv -> getr (ms_regs ms0) r = getr rg r).
  { intros r Hr. unfold E in HS. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [clkeep HS |]). destruct Hr. }
  pose proof (cl_bregs_eq rg (ms_regs ms0) F (crt_dregs_bregs HDR) KB) as HBR1.
  lazymatch type of HS with st_ok_pi _ _ ?E2 _ _ => set (EE := E2) in * end.
  assert (WE : forall k v, ew E k = w64 v -> (k < 240)%nat -> ew EE k = w64 v).
  { intros k v Hk Hlt. unfold EE. rewrite ?ew_ewset_other by lia. exact Hk. }
  assert (XE41 : bv_unsigned (ew EE 41) = sp1) by (unfold EE; rewrite ?ew_ewset_other by lia; exact X41).
  assert (E66 : ew E 66 = w64 saved) by exact (te_more_lt regs rg _ 2 ltac:(lia)).
  clear HF HFr HG.
  pmkst HS.
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?pc)] =>
    replace pc with (CRT_PC_A + CRT_C_OFF) by (vm_compute; reflexivity) end.
  apply (KC fxk lyc Sc Hpc Wc (ms_mem ms0) _ kj pos Dc Lamc peakc cset saved cap Dback ms (ms_regs ms0)).
  refine (conj HRW1 (conj (conj _ _) (conj HBR1 _))).
  + clsp HS 0%nat 41%nat XE41; [clden (WE 59%nat F W27 ltac:(lia)) | lia].
  + clsp HS 0%nat 41%nat XE41; [clden (WE 66%nat saved E66 ltac:(lia)) | lia].
  + clsp HS 0%nat 41%nat XE41; [clden (WE 44%nat (Z.of_nat (cm_at ms)) W12 ltac:(lia)) | lia].
- (* ---- a member to compare: the member loop's set-up, to L3 (+0x590) at i = 0 ---- *)
  assert (Hcs0 : conds_ok E cl_cL2L3).
  { unfold cl_cL2L3. split; [exact (proj1 HBN)|]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
    rewrite branch_ne_U, UN, U_SLit. apply negb_true_iff, Z.eqb_neq. unfold zcanon, M64. rewrite Z.mod_0_l by lia. lia. }
  destruct (ENTRY _ Hcs0) as [HS SHOK].
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM CL_SPAN (CRT_PC_A + CRT_L3_OFF).
  all: try (lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end;
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ (xr 9) (sp1 - sp0));
      [reflexivity | change (xr 9) with 41%nat; rewrite X41; lia | cbn; lia | cbn; lia |];
    repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil).
  all: try (cbn [ms_mem mkst restrict]; unfold CL_Bx; change (SOff (xr 26) 0) with (SOff 58 0);
    assert (W21' : ew E 53 = w64 doc) by exact W21;
    assert (W26' : ew E 58 = w64 SHADOW_OFF) by exact W26;
    rewrite (U_atom_off E 53 doc 32 W21') by lia; rewrite (U_atom E 58 SHADOW_OFF W26') by (unfold SHADOW_OFF; lia);
    apply (range_addressable_sub _ SHADOW_OFF doc 56 (doc + 32) 8 Hrad); lia).
  assert (Hav : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 32 <= a < sp1 + 96) ->
    aview SEGS (w_H Wc) (ms_mem ms0) a = aview SEGS (w_H Wc) memc a).
  { apply (ts_keep Wc _ _ memc (ms_mem ms0) _ HFr). intros a (r & Hri & Hr). vm_compute in Hri.
    repeat (destruct Hri as [<- | Hri]; [cbn [YP09.r_wlo YP09.r_whi YP09.r_base base_val] in Hr; rewrite ?X41 in Hr; lia |]);
      destruct Hri. }
  assert (Hpr : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) (ms_mem ms0) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  pose proof (cl_rw_keep _ _ _ _ _ memc (ms_mem ms0) _ _ _ _ _ _ _ _ _ _ _ _ _ (sp1 + 32) (sp1 + 96) HRW HJ HB_HJ
    ltac:(lia) ltac:(unfold CRT_SP_F; lia) Hav Hpr HPM) as HRW1.
  assert (KB : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 23; 26; 27]%bv -> getr (ms_regs ms0) r = getr rg r).
  { intros r Hr. unfold E in HS. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [clkeep HS |]). destruct Hr. }
  pose proof (cl_bregs_eq rg (ms_regs ms0) F (crt_dregs_bregs HDR) KB) as HBR1.
  assert (Hbk47 : 0 <= bkeys < 2 ^ 47).
  { destruct Hbc as [(_ & _ & ->) | (Hc0 & _ & Hky)]; [lia|].
    destruct (cl_blk_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLD (HinL _ ltac:(apply in_or_app; left; rewrite EBi;
      apply in_or_app; left; rewrite (proj2 (Z.eqb_neq bcap 0)) by lia; right; left; reflexivity))) as (_ & Hb0 & Hb).
    lia. }
  assert (Hrd : forall a v, a + 8 <= YM05.alloc_ceiling -> 0 <= a -> rd_u64 SEGS (mrestrict (w_H Wc) memc) a v ->
    rd_u64 SEGS (mrestrict (w_H Wc) (ms_mem ms0)) a v).
  { intros a v Ha0 Ha1 [Rv Vv]. split; [exact Rv|]. apply (ts_vm_av (w_H Wc) (w_H Wc) memc (ms_mem ms0)); [|exact Vv].
    intros j Hj. apply Hav; lia. }
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  prreg HS (25%bv : bv 5) Q25. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
  lazymatch type of HS with st_ok_pi _ _ ?E2 _ _ => set (EE := E2) in * end.
  assert (WE : forall k v, ew E k = w64 v -> (k < 240)%nat -> ew EE k = w64 v).
  { intros k v Hk Hlt. unfold EE. rewrite ?ew_ewset_other by lia. exact Hk. }
  assert (XE41 : bv_unsigned (ew EE 41) = sp1) by (unfold EE; rewrite ?ew_ewset_other by lia; exact X41).
  assert (EE69 : ew EE 69 = w64 bkeys) by exact (WE 69%nat bkeys E69 ltac:(lia)).
  assert (EE65 : ew EE 65 = w64 dkeys) by exact (WE 65%nat dkeys E65 ltac:(lia)).
  assert (EE58 : ew EE 58 = w64 SHADOW_OFF) by exact (WE 58%nat SHADOW_OFF W26 ltac:(lia)).
  assert (EE53 : ew EE 53 = w64 doc) by exact (WE 53%nat doc W21 ltac:(lia)).
  assert (EE44 : ew EE 44 = w64 (Z.of_nat (cm_at ms))) by exact (WE 44%nat _ W12 ltac:(lia)).
  assert (EE64 : ew EE 64 = w64 n) by exact (WE 64%nat n E64 ltac:(lia)).
  assert (E66 : ew E 66 = w64 saved) by exact (te_more_lt regs rg _ 2 ltac:(lia)).
  clear HF HFr HG.
  pmkst HS.
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?pc)] =>
    replace pc with (CRT_PC_A + CRT_L3_OFF) by (vm_compute; reflexivity) end.
  apply (KL3 fxk lyc Sc Hpc Wc (ms_mem ms0) _ kj pos Dc Lamc peakc cset saved cap Dback ms (ms_regs ms0) bkeys dkeys).
  refine (conj HRW1 (conj (conj _ _) (conj HBR1 (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
    (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))))))))).
  + clsp HS 0%nat 41%nat XE41; [clden (WE 59%nat F W27 ltac:(lia)) | lia].
  + clsp HS 0%nat 41%nat XE41; [clden (WE 66%nat saved E66 ltac:(lia)) | lia].
  + unfold n in Hn0. lia.
  + change (frame_addr lyc CRT_CID pos) with F.
    apply Hrd; [unfold CRT_OFF_BACK, PJ_OFF_KEYS; lia | unfold CRT_OFF_BACK, PJ_OFF_KEYS; lia |].
    replace (F + CRT_OFF_BACK + PJ_OFF_KEYS) with (F + 64) by (unfold CRT_OFF_BACK, PJ_OFF_KEYS; lia). exact VBKE'.
  + apply Hrd; [unfold PJ_OFF_KEYS; lia | unfold PJ_OFF_KEYS; lia | exact VDKE].
  + rewrite Q10, E69. f_equal. lia.
  + rewrite Q11, E69. f_equal. lia.
  + rewrite Q12, E65. f_equal. lia.
  + rewrite Q25, E65. f_equal. lia.
  + assert (E58 : ew E 58 = w64 SHADOW_OFF) by exact W26.
    rewrite Q21, (cl_sh_w (ew E 58) (ew E 69) bkeys) by
      (first [rewrite E58; apply unsigned_lit_small; unfold SHADOW_OFF; lia | rewrite E69; apply unsigned_lit_small; lia | lia]).
    f_equal. lia.
  + assert (E44 : ew E 44 = w64 (Z.of_nat (cm_at ms))) by exact W12.
    rewrite Q22, E44. f_equal. rewrite Z.sub_0_r. rewrite Z.mod_small by lia. reflexivity.
  + clsp HS 0%nat 41%nat XE41; [clden (WE 44%nat (Z.of_nat (cm_at ms)) W12 ltac:(lia)) | lia].
  + clsp HS 0%nat 41%nat XE41.
    * rewrite denot_lit_U. f_equal. unfold PJ_OFF_KIDS. exact (cl_sh_off EE 58 53 doc 24 EE58 EE53 ltac:(lia) ltac:(lia) ltac:(lia)).
    * unfold shadow_addr, SHADOW_OFF, PJ_OFF_KIDS. pose proof (Z.div_pos (doc + 24) 8 ltac:(lia) ltac:(lia)).
      assert ((doc + 24) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
  + clsp HS 0%nat 41%nat XE41; [clden (WE 53%nat doc W21 ltac:(lia)) | unfold PJ_OFF_KIDS; lia].
  + clsp HS 0%nat 41%nat XE41; [clden (WE 64%nat n E64 ltac:(lia)) | lia].
  + clsp HS 0%nat 41%nat XE41; [rewrite denot_lit_U, U_SLit; reflexivity | lia].
Qed.
End L2.

(* ---- L3's entry state (extras: 64 = n - i, 65 = 56 i, 66 = saved, 67 = at, 68 = doc, 69 = back.keys[i],
   70 = doc->keys[i]) ---- *)
Lemma cl_L3_entry : forall (fxk : YK11.FPState) (Wc : world SEGS) memc rg cn ko saved atv bkeys dkeys F bki dki i,
  getr rg 9 = w64 (CRT_sp1 (regs := regs)) -> getr rg 11 = w64 (bkeys + 8 * Z.of_nat i) ->
  getr rg 12 = w64 (dkeys + 8 * Z.of_nat i) -> getr rg 21 = w64 (shadow_addr bkeys + Z.of_nat i) ->
  getr rg 25 = w64 (dkeys + 8 * Z.of_nat i) -> getr rg 26 = w64 SHADOW_OFF -> getr rg 27 = w64 F ->
  2 ^ 46 <= CRT_sp1 (regs := regs) -> CRT_sp1 (regs := regs) + 96 <= 2 ^ 47 -> CRT_sp1 (regs := regs) mod 32 = 0 ->
  4096 <= doc -> doc + 56 <= CRT_sp1 (regs := regs) -> 4096 <= F -> F + 512 <= CRT_sp1 (regs := regs) -> F mod 32 = 0 ->
  4096 <= bkeys -> bkeys mod 8 = 0 -> bkeys + 8 * Z.of_nat i + 8 <= CRT_sp1 (regs := regs) ->
  4096 <= dkeys -> dkeys mod 8 = 0 -> dkeys + 8 * Z.of_nat i + 8 <= CRT_sp1 (regs := regs) ->
  (bkeys + 8 * Z.of_nat i + 8 <= dkeys + 8 * Z.of_nat i \/ dkeys + 8 * Z.of_nat i + 8 <= bkeys + 8 * Z.of_nat i) ->
  1 <= cn <= 2 ^ 54 -> 0 <= ko < 2 ^ 64 -> 0 <= saved < 2 ^ 64 -> 0 <= atv < 2 ^ 64 -> 0 <= bki < 2 ^ 64 ->
  0 <= dki < 2 ^ 64 ->
  (forall a, CRT_sp1 (regs := regs) + 64 <= a < CRT_sp1 (regs := regs) + 80 -> apresent (w_H Wc) memc a) ->
  cl_sp2 Wc memc F saved ->
  crt_spill (regs := regs) Wc memc CRT_SP_AT atv ->
  crt_spill (regs := regs) Wc memc CL_SP_KSH (shadow_addr (doc + PJ_OFF_KIDS)) ->
  crt_spill (regs := regs) Wc memc CL_SP_P (doc + PJ_OFF_KIDS) ->
  crt_spill (regs := regs) Wc memc CRT_SP_PN cn -> crt_spill (regs := regs) Wc memc CRT_SP_N ko ->
  rd_u64 SEGS (mrestrict (w_H Wc) memc) (bkeys + 8 * Z.of_nat i) bki ->
  rd_u64 SEGS (mrestrict (w_H Wc) memc) (dkeys + 8 * Z.of_nat i) dki ->
  st_ok_pi SEGS VAL (TE regs rg [w64 cn; w64 ko; w64 saved; w64 atv; w64 doc; w64 bki; w64 dki]) ss_L3
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_A + CRT_L3_OFF))) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS CL_Bx [] (TE regs rg [w64 cn; w64 ko; w64 saved; w64 atv; w64 doc; w64 bki; w64 dki])
    (mrestrict (w_H Wc) memc).
Proof.
intros fxk Wc memc rg cn ko saved atv bkeys dkeys F bki dki i R9 R11 R12 R21 R25 R26 R27 H1 H2 H3 H4 H5 HF0 HF1 HF2
  Hb4 Hb8 Hbc Hd4 Hd8 Hdc Hbd Hcn Hko Hsv Hatv Hbki Hdki HP (VBK & VSV) VAT VKSH VP VPN VN [_ VBKI] [_ VDKI].
unfold crt_spill, CL_SP_P, CL_SP_KSH, CRT_SP_AT, CRT_SP_PN, CRT_SP_N, CRT_SP_BACK, CRT_SP_SAVED, CRT_OFF_BACK,
  PJ_OFF_KIDS in *.
set (sp1 := CRT_sp1 (regs := regs)) in *.
set (E := TE regs rg [w64 cn; w64 ko; w64 saved; w64 atv; w64 doc; w64 bki; w64 dki]).
assert (W9 : ew E (xr 9) = w64 sp1) by (unfold E, xr; rewrite (te_cur regs rg _ 9%bv 9) by reflexivity; exact R9).
assert (W11 : ew E (xr 11) = w64 (bkeys + 8 * Z.of_nat i))
  by (unfold E, xr; rewrite (te_cur regs rg _ 11%bv 11) by reflexivity; exact R11).
assert (W12 : ew E (xr 12) = w64 (dkeys + 8 * Z.of_nat i))
  by (unfold E, xr; rewrite (te_cur regs rg _ 12%bv 12) by reflexivity; exact R12).
assert (W21 : ew E (xr 21) = w64 (shadow_addr bkeys + Z.of_nat i))
  by (unfold E, xr; rewrite (te_cur regs rg _ 21%bv 21) by reflexivity; exact R21).
assert (W25 : ew E (xr 25) = w64 (dkeys + 8 * Z.of_nat i))
  by (unfold E, xr; rewrite (te_cur regs rg _ 25%bv 25) by reflexivity; exact R25).
assert (W26 : ew E (xr 26) = w64 SHADOW_OFF) by (unfold E, xr; rewrite (te_cur regs rg _ 26%bv 26) by reflexivity; exact R26).
assert (W27 : ew E (xr 27) = w64 F) by (unfold E, xr; rewrite (te_cur regs rg _ 27%bv 27) by reflexivity; exact R27).
assert (E64 : ew E 64 = w64 cn) by exact (te_more_lt regs rg _ 0 ltac:(lia)).
assert (E65 : ew E 65 = w64 ko) by exact (te_more_lt regs rg _ 1 ltac:(lia)).
assert (E66 : ew E 66 = w64 saved) by exact (te_more_lt regs rg _ 2 ltac:(lia)).
assert (E67 : ew E 67 = w64 atv) by exact (te_more_lt regs rg _ 3 ltac:(lia)).
assert (E68 : ew E 68 = w64 doc) by exact (te_more_lt regs rg _ 4 ltac:(lia)).
assert (E69 : ew E 69 = w64 bki) by exact (te_more_lt regs rg _ 5 ltac:(lia)).
assert (E70 : ew E 70 = w64 dki) by exact (te_more_lt regs rg _ 6 ltac:(lia)).
assert (UB : forall k v, ew E k = w64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E k) = v)
  by (intros k v Hk Hv; rewrite Hk; apply unsigned_lit_small; exact Hv).
assert (Hsb : 0 <= shadow_addr bkeys + Z.of_nat i < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos bkeys 8 ltac:(lia) ltac:(lia)).
  assert (bkeys / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
split; [|unfold sh_ok; apply Forall_nil].
apply ts_st_ok.
all: try change (TE regs rg [w64 cn; w64 ko; w64 saved; w64 atv; w64 doc; w64 bki; w64 dki]) with E.
- apply te_regs_ok.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
  + apply (ts_rok E _ (xr 9) sp1); [apply UB; [exact W9 | lia] | lia | lia | |].
    { intros o Ho. apply (apresent_writable SEGS). apply HP. cbn in Ho. lia. }
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (ts_chunk E _ _ 24 8 (SOff 66 0) saved); [| cbn; lia | cbn; lia | exact VSV].
      rewrite denot_lit_U, (U_atom_off E 66 saved 0 E66) by lia. rewrite Z.add_0_r. reflexivity.
    * apply (ts_chunk E _ _ 32 8 (SOff 67 0) atv); [| cbn; lia | cbn; lia | exact VAT].
      rewrite denot_lit_U, (U_atom_off E 67 atv 0 E67) by lia. rewrite Z.add_0_r. reflexivity.
    * apply (ts_chunk E _ _ 40 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 68 24) (SLit 3)) (SOff (xr 26) 0)) (shadow_addr (doc + 24)));
        [| unfold shadow_addr, SHADOW_OFF; pose proof (Z.div_pos (doc + 24) 8 ltac:(lia) ltac:(lia));
           assert ((doc + 24) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia); cbn; lia | cbn; lia | exact VKSH].
      rewrite denot_lit_U. f_equal. exact (cl_sh_off E (xr 26) 68 doc 24 W26 E68 ltac:(lia) ltac:(lia) ltac:(lia)).
    * apply (ts_chunk E _ _ 48 8 (SOff 68 24) (doc + 24)); [| cbn; lia | cbn; lia | exact VP].
      rewrite denot_lit_U, (U_atom_off E 68 doc 24 E68) by lia. reflexivity.
    * apply (ts_chunk E _ _ 56 8 (SOff (xr 27) 32) (F + 32)); [| cbn; lia | cbn; lia | exact VBK].
      rewrite denot_lit_U, (U_atom_off E (xr 27) F 32 W27) by lia. reflexivity.
    * apply (ts_chunk E _ _ 80 8 (SOff 64 0) cn); [| cbn; lia | cbn; lia | exact VPN].
      rewrite denot_lit_U, (U_atom_off E 64 cn 0 E64) by lia. rewrite Z.add_0_r. reflexivity.
    * apply (ts_chunk E _ _ 88 8 (SOff 65 0) ko); [| cbn; lia | cbn; lia | exact VN].
      rewrite denot_lit_U, (U_atom_off E 65 ko 0 E65) by lia. rewrite Z.add_0_r. reflexivity.
  + apply (ts_rok E _ (xr 11) (bkeys + 8 * Z.of_nat i)); [apply UB; [exact W11 | lia] | lia | lia | intros o Ho; cbn in Ho; lia |].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (ts_chunk E _ _ 0 8 (SOff 69 0) bki); [| cbn; lia | cbn; lia | rewrite Z.add_0_r; exact VBKI].
    rewrite denot_lit_U, (U_atom_off E 69 bki 0 E69) by lia. rewrite Z.add_0_r. reflexivity.
  + apply (ts_rok E _ (xr 12) (dkeys + 8 * Z.of_nat i)); [apply UB; [exact W12 | lia] | lia | lia | intros o Ho; cbn in Ho; lia |].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (ts_chunk E _ _ 0 8 (SOff 70 0) dki); [| cbn; lia | cbn; lia | rewrite Z.add_0_r; exact VDKI].
    rewrite denot_lit_U, (U_atom_off E 70 dki 0 E70) by lia. rewrite Z.add_0_r. reflexivity.
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !ts_bv_some.
  rewrite (UB _ _ W9 ltac:(lia)), (UB _ _ W11 ltac:(lia)), (UB _ _ W12 ltac:(lia)).
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | split; [|split; [|exact I]]]].
  + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (UB _ _ W9 ltac:(lia)), (UB _ _ W11 ltac:(lia)), (UB _ _ W12 ltac:(lia)),
      (UB _ _ W26 ltac:(unfold SHADOW_OFF; lia)), (UB _ _ W27 ltac:(lia)), (UB _ _ E64 ltac:(lia)).
    change (2 ^ 5) with 32. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
    unfold SHADOW_OFF. repeat split; lia.
  + apply U_inj. rewrite (proj1 (cl_sh_U E (xr 26) (xr 11) (bkeys + 8 * Z.of_nat i)
      (UB _ _ W26 ltac:(unfold SHADOW_OFF; lia)) (UB _ _ W11 ltac:(lia)) ltac:(lia))) || idtac.
    rewrite (U_atom_off E (xr 21) _ 0 W21) by lia. rewrite Z.add_0_r.
    rewrite (proj2 (cl_sh_U E (xr 26) (xr 11) (bkeys + 8 * Z.of_nat i)
      (UB _ _ W26 ltac:(unfold SHADOW_OFF; lia)) (UB _ _ W11 ltac:(lia)) ltac:(lia))).
    unfold shadow_addr. rewrite Z.mul_comm, Z.div_add by lia. lia.
  + apply U_inj.
    rewrite (proj2 (cl_sh_U E (xr 26) (xr 25) (dkeys + 8 * Z.of_nat i)
      (UB _ _ W26 ltac:(unfold SHADOW_OFF; lia)) (UB _ _ W25 ltac:(lia)) ltac:(lia))).
    rewrite (proj2 (cl_sh_U E (xr 26) (xr 12) (dkeys + 8 * Z.of_nat i)
      (UB _ _ W26 ltac:(unfold SHADOW_OFF; lia)) (UB _ _ W12 ltac:(lia)) ltac:(lia))). reflexivity.
Qed.

(* ======================================================================================================== *)
(* L3: THE MEMBER LOOP (new:750-755). One iteration is L3 -> strcmp (back.keys[i], doc->keys[i]) at +0x5bc -> L3r
   (+0x5c0) -> [i <> at: same (&back.kids[i], &doc->kids[i]) at +0x5f0 -> L3s (+0x5f4)] -> L3 (i + 1) or C; the loop
   closes by the measure length ms - i. *)
Section L3h.
Variable mb : nat.
Hypothesis KL3r : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i bkeys dkeys,
  (length ms - i <= mb)%nat ->
  cl_at_L3r fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i bkeys dkeys ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk (CRT_CMP2_CALL + 4) rg memc mdc) QFa.

(* ---- L3 -> the strcmp (back.keys[i], doc->keys[i]) at +0x5bc -> L3r: the two inline slot checks (+0x714, +0x718
   unreachable: the two key arrays are ledger blocks), and the compare says EQUAL: pj_set_model keeps every key
   (Crt102Model.cm_set_member), so the property abort of new:754 (`bnez a0` at +0x5c0) is not taken ---- *)
Lemma cl_L3_head : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i bkeys dkeys,
  (length ms - i <= mb)%nat ->
  cl_at_L3 fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i bkeys dkeys ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk CRT_L3_OFF rg memc mdc) QFa.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i bkeys dkeys Hmb HL3.
destruct HL3 as (HRW & HSP2 & HBR & Hi & Hbk & Hdk & R10 & R11 & R12 & R25 & R21 & R22 & SAT & SKSH & SP & SPN & SN).
pose proof HRW as (Et & HFZ & HFK & HL & Hcs & Hcin & Hsv & Hcopy & Hback & Hd8 & Hrad & Hrab & Hrav & Hpos).
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ).
pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPl.
pose proof (crt_live_dx_apart HL) as HDx.
pose proof (crt_live_frame HL) as HFRM.
pose proof (crt_live_memnorm HL) as HPM.
pose proof (crt_side_ledger HSD) as HLD.
pose proof (crt_side_arodata HSD) as HRO.
pose proof (crt_side_doc HSD) as HDOC.
pose proof (crt_side_doc_blocks HSD) as HDL.
pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkp & _).
rewrite Et in HDOC.
assert (Etc : tc = PjTree.JObj (PjTree.pj_set_model ms ck_MOD_AT (PjTree.JStr ck_STAMP))) by (unfold crt_tc; rewrite Et; reflexivity).
rewrite Etc in Hback.
destruct (nth_error ms i) as [[nm u]|] eqn:Hnth; [|apply nth_error_None in Hnth; lia].
destruct (cm_set_member ms (PjTree.JStr ck_STAMP) i nm u Hnth) as (u' & Hnth' & _ & _).
assert (HinL : forall bk, In bk (Dback ++ (saved, cap) :: Dc) -> In bk Lamc).
{ intros bk Hb. apply (Permutation_in _ (Permutation_sym HPl)). apply in_or_app. left. exact Hb. }
assert (HDb : forall bk, In bk Dback -> In bk Lamc) by (intros bk Hb; apply HinL; apply in_or_app; left; exact Hb).
destruct (cl_obj_key _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLD Hback HDb
  ltac:(replace (frame_addr lyc CRT_CID pos + CRT_OFF_BACK + 32) with
          (frame_addr lyc CRT_CID pos + CRT_OFF_BACK + PJ_OFF_KEYS) by (unfold PJ_OFF_KEYS; lia); exact Hbk) Hnth')
  as (bkp & bkb & Hbkp & Hbcs & Hinbk & SXb & Hrabs & Hbk4 & Hbk8 & Hbkc & bkc & Hbkd & Hbkl & Hbkcap).
destruct (cl_obj_key _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLD HDOC HDL
  ltac:(replace (doc + 32) with (doc + PJ_OFF_KEYS) by (unfold PJ_OFF_KEYS; lia); exact Hdk) Hnth)
  as (dkp & dkb & Hdkp & Hdcs & Hindk & SXd & Hrads & Hdk4 & Hdk8 & Hdkc & dkc & Hdkd & Hdkl & Hdkcap).
(* the two key arrays are different blocks of the ledger: back's is the read-back's, doc's the entry's *)
assert (Hap : bkeys + bkc <= dkeys \/ dkeys + dkc <= bkeys).
{ apply (cl_lam_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLD Hbkl Hdkl). intros E.
  apply (HDx (bkeys, bkc)); [apply in_or_app; left; exact Hbkd | rewrite E; exact Hdkd]. }
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cl_sp0 as (H16 & Hsp0 & H47). pose proof cl_sp1 as (Hs32 & Hs1).
assert (HSTKC : STKC = 27632) by (vm_compute; reflexivity).
pose proof cl_doc_low as (Hdl0 & Hdl1).
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc (crt_frame_listed HFRM))
  as (Fb1 & Fb2 & Fb3).
change (fs_frame_bytes CRT_CID) with 512 in Fb2.
destruct (alx_frames SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc (crt_frame_listed HFRM))
  as (F32 & _).
pose proof (crt_bregs_sp HBR) as R2.
pose proof (crt_bregs_gp HBR) as R3.
pose proof (crt_bregs_tp HBR) as R4.
pose proof (crt_bregs_s0 HBR) as R8.
pose proof (crt_bregs_s1 HBR) as R9.
pose proof (crt_bregs_s2 HBR) as R18.
pose proof (crt_bregs_s4 HBR) as R20.
pose proof (crt_bregs_s3 HBR) as R19.
pose proof (crt_bregs_s7 HBR) as R23.
pose proof (crt_bregs_s10 HBR) as R26.
pose proof (crt_bregs_s11 HBR) as R27.
set (F := frame_addr lyc CRT_CID pos) in *.
set (sp1 := CRT_sp1 (regs := regs)) in *.
assert (Hsv0 : 4096 <= saved < 2 ^ 47).
{ assert (Hin : In (saved, cap) Lamc) by (apply HinL; apply in_or_app; right; left; reflexivity).
  destruct (cl_blk_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLD Hin) as (Hk & Ha & Hb).
  pose proof YM05.alloc_ceiling_lt. change (@cf_head CfParams_preset) with 16 in Ha. lia. }
set (n := Z.of_nat (length ms)) in *.
assert (Hat : (cm_at ms <= length ms)%nat) by apply cm_at_le.
assert (Hlen : (length ms <= length (PjTree.pj_set_model ms ck_MOD_AT (PjTree.JStr ck_STAMP)))%nat)
  by (rewrite cm_set_len; destruct (Nat.eqb (cm_at ms) (length ms)); lia).
pose proof Hbkp as [Rbkp _]. pose proof Hdkp as [Rdkp _].
destruct (cl_L3_entry fxk Wc memc rg (n - Z.of_nat i) (56 * Z.of_nat i) saved (Z.of_nat (cm_at ms)) bkeys dkeys F bkp dkp i
  R9 R11 R12 R21 R25 R26 R27 ltac:(lia) ltac:(lia) Hs32 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F32
  Hbk4 Hbk8 ltac:(unfold n in *; lia) Hdk4 Hdk8 ltac:(unfold n in *; lia) ltac:(unfold n in *; lia) ltac:(unfold n in *; lia)
  ltac:(unfold n in *; lia) ltac:(lia) ltac:(lia) Rbkp Rdkp
  ltac:(intros a Ha; apply Hstkp; lia) HSP2 SAT SKSH SP SPN SN Hbkp Hdkp) as [HS SHOK].
set (E := TE regs rg [w64 (n - Z.of_nat i); w64 (56 * Z.of_nat i); w64 saved; w64 (Z.of_nat (cm_at ms)); w64 doc;
  w64 bkp; w64 dkp]) in *.
assert (HEI : img_env VAL A_LIM E) by apply te_env.
assert (W9 : ew E (xr 9) = w64 sp1) by (unfold E, xr; rewrite (te_cur regs rg _ 9%bv 9) by reflexivity; exact R9).
assert (X41 : bv_unsigned (ew E 41) = sp1) by (change 41%nat with (xr 9); rewrite W9; apply unsigned_lit_small; lia).
assert (W11 : ew E 43 = w64 (bkeys + 8 * Z.of_nat i))
  by (change 43%nat with (xr 11); unfold E, xr; rewrite (te_cur regs rg _ 11%bv 11) by reflexivity; exact R11).
assert (W12 : ew E 44 = w64 (dkeys + 8 * Z.of_nat i))
  by (change 44%nat with (xr 12); unfold E, xr; rewrite (te_cur regs rg _ 12%bv 12) by reflexivity; exact R12).
assert (W26 : ew E 58 = w64 SHADOW_OFF)
  by (change 58%nat with (xr 26); unfold E, xr; rewrite (te_cur regs rg _ 26%bv 26) by reflexivity; exact R26).
pose (RUN := @crt_run_xw_inv fxk rc SK A_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (YSRrMemnorm.srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)) WS_HJ).
unfold crt_cfg.
paj_run_tok_x_inv RUN HS HJ SHOK HPM CL_SPAN.
all: try (cbn [ms_mem mkst restrict]; unfold CL_Bx; change (SOff (xr 26) 0) with (SOff 58 0);
  first [rewrite (U_atom E 43 _ W11) by lia | rewrite (U_atom E 44 _ W12) by lia];
  rewrite (U_atom E 58 SHADOW_OFF W26) by (unfold SHADOW_OFF; lia);
  first [exact Hrabs | exact Hrads]).
all: try (lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
  let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end;
  repeat (first [apply awr_ok_cons_ro; [cbn; lia|]
                | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ (xr 9) (sp1 - sp0));
                    [reflexivity | change (xr 9) with 41%nat; rewrite X41; lia | cbn; lia | cbn; lia |]]);
  apply awr_ok_nil).
(* ---- the run's end, at the call: it wrote 0x40 / 0x48 only ---- *)
assert (Hav : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 64 <= a < sp1 + 80) ->
  aview SEGS (w_H Wc) (ms_mem ms0) a = aview SEGS (w_H Wc) memc a).
{ apply (ts_keep Wc _ _ memc (ms_mem ms0) _ HFr). intros a (r & Hri & Hr). vm_compute in Hri.
  repeat (destruct Hri as [<- | Hri]; [cbn [YP09.r_wlo YP09.r_whi YP09.r_base base_val] in Hr; rewrite ?X41 in Hr; lia |]);
    destruct Hri. }
assert (Hpr : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) (ms_mem ms0) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (cl_rw_keep _ _ _ _ _ memc (ms_mem ms0) _ _ _ _ _ _ _ _ _ _ _ _ _ (sp1 + 64) (sp1 + 80) HRW HJ HB_HJ
  ltac:(lia) ltac:(unfold CRT_SP_F; lia) Hav Hpr HPM) as HRW1.
assert (KB : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]%bv -> getr (ms_regs ms0) r = getr rg r).
{ intros r Hr. unfold E in HS. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [clkeep HS |]). destruct Hr. }
pose proof (cl_bregs_eq rg (ms_regs ms0) F HBR ltac:(intros r Hr; apply KB; cbv [In] in Hr |- *; tauto)) as HBR1.
assert (Hrd : forall m a v, a + 8 <= YM05.alloc_ceiling -> 0 <= a ->
  (forall z, 0 <= z < YM05.alloc_ceiling -> aview SEGS (w_H Wc) m z = aview SEGS (w_H Wc) memc z) ->
  rd_u64 SEGS (mrestrict (w_H Wc) memc) a v -> rd_u64 SEGS (mrestrict (w_H Wc) m) a v).
{ intros m a v Ha0 Ha1 Hk [Rv Vv]. split; [exact Rv|]. apply (ts_vm_av (w_H Wc) (w_H Wc) memc m); [|exact Vv].
  intros j Hj. apply Hk. lia. }
assert (Hlow0 : forall z, 0 <= z < YM05.alloc_ceiling -> aview SEGS (w_H Wc) (ms_mem ms0) z = aview SEGS (w_H Wc) memc z)
  by (intros z Hz; apply Hav; lia).
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (1%bv : bv 5) Q1. prreg HS (24%bv : bv 5) Q24.
lazymatch type of HS with st_ok _ ?E2 _ _ => set (EE := E2) in * end.
assert (WE : forall k v, ew E k = w64 v -> (k < 240)%nat -> ew EE k = w64 v).
{ intros k v Hk Hlt. unfold EE. rewrite ?ew_ewset_other by lia. exact Hk. }
assert (XE41 : bv_unsigned (ew EE 41) = sp1) by (unfold EE; rewrite ?ew_ewset_other by lia; exact X41).
assert (W10 : ew E 42 = w64 (bkeys + 8 * Z.of_nat i))
  by (change 42%nat with (xr 10); unfold E, xr; rewrite (te_cur regs rg _ 10%bv 10) by reflexivity; exact R10).
assert (X10 : getr (ms_regs ms0) 10 = w64 bkp) by (rewrite Q10; exact (WE 69%nat bkp (te_more_lt regs rg _ 5 ltac:(lia)) ltac:(lia))).
assert (X11 : getr (ms_regs ms0) 11 = w64 dkp) by (rewrite Q11; exact (WE 70%nat dkp (te_more_lt regs rg _ 6 ltac:(lia)) ltac:(lia))).
assert (X24 : getr (ms_regs ms0) 24 = w64 (dkeys + 8 * Z.of_nat i)) by (rewrite Q24; exact (WE 44%nat _ W12 ltac:(lia))).
assert (X1 : getr (ms_regs ms0) 1 = Z_to_bv 64 (BASE + (CRT_PC_A + (CRT_CMP2_CALL + 4)))) by (rewrite Q1; vm_compute; reflexivity).
pose proof (cl_pi_of_ok _ _ _ _ HS) as HSpi.
assert (SBK0 : crt_spill (regs := regs) Wc (ms_mem ms0) CL_SP_BK (bkeys + 8 * Z.of_nat i)).
{ unfold CL_SP_BK. clsp HSpi 0%nat 41%nat XE41; [clden (WE 42%nat _ W10 ltac:(lia)) | lia]. }
assert (SBK20 : crt_spill (regs := regs) Wc (ms_mem ms0) CL_SP_BK2 (bkeys + 8 * Z.of_nat i)).
{ unfold CL_SP_BK2. clsp HSpi 0%nat 41%nat XE41; [clden (WE 43%nat _ W11 ltac:(lia)) | lia]. }
clear HSpi.
clear HF HFr HG.
(* ---- the two keys again, in the run's final memory ---- *)
pose proof HRW1 as (_ & _ & _ & HL1 & _ & _ & _ & _ & Hback1 & _).
destruct (crt_live_journal HL1) as (WS_HJ1 & HJ1 & HB_HJ1). pose proof (crt_live_side HL1) as HSD1.
pose proof (crt_side_ledger HSD1) as HLD1.
pose proof (crt_side_doc HSD1) as HDOC1.
pose proof (crt_side_doc_blocks HSD1) as HDL1.
pose proof HJ1 as (HARc1 & _).
rewrite Et in HDOC1. rewrite Etc in Hback1.
assert (Hbk1 : rd_u64 SEGS (mrestrict (w_H Wc) (ms_mem ms0)) (F + CRT_OFF_BACK + 32) bkeys).
{ apply (Hrd _ (F + CRT_OFF_BACK + 32) bkeys ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia) Hlow0).
  replace (F + CRT_OFF_BACK + 32) with (F + CRT_OFF_BACK + PJ_OFF_KEYS) by (unfold PJ_OFF_KEYS; lia). exact Hbk. }
assert (Hdk1 : rd_u64 SEGS (mrestrict (w_H Wc) (ms_mem ms0)) (doc + 32) dkeys).
{ apply (Hrd _ (doc + 32) dkeys ltac:(lia) ltac:(lia) Hlow0).
  replace (doc + 32) with (doc + PJ_OFF_KEYS) by (unfold PJ_OFF_KEYS; lia). exact Hdk. }
destruct (cl_obj_key _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc1 HLD1 Hback1 HDb Hbk1 Hnth')
  as (bkp' & bkb' & Hbkp' & Hbcs' & _ & SXb' & _).
destruct (cl_obj_key _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc1 HLD1 HDOC1 HDL1 Hdk1 Hnth)
  as (dkp' & dkb' & Hdkp' & Hdcs' & _ & SXd' & _).
assert (Ebk : bkp' = bkp).
{ destruct Hbkp' as [Zb1 Vb1].
  destruct (Hrd _ (bkeys + 8 * Z.of_nat i) bkp ltac:(unfold n in *; lia) ltac:(lia) Hlow0 Hbkp) as [Zb2 Vb2].
  exact (cl_vm_det _ _ _ _ _ Vb1 Vb2 Zb1 Zb2). }
assert (Edk : dkp' = dkp).
{ destruct Hdkp' as [Zd1 Vd1].
  destruct (Hrd _ (dkeys + 8 * Z.of_nat i) dkp ltac:(unfold n in *; lia) ltac:(lia) Hlow0 Hdkp) as [Zd2 Vd2].
  exact (cl_vm_det _ _ _ _ _ Vd1 Vd2 Zd1 Zd2). }
subst bkp' dkp'.
apply (cl_strcmp_call fxk Wc _ _ ms0 _ lyc Sc Hpc _ pos _ Lamc peakc _ 0 0 (CRT_CMP2_CALL + 4) bkp dkp
  (Z.of_nat (length nm)) (Z.of_nat (length nm)) HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  HL1 HBR1 X1 ltac:(unfold CRT_CMP2_CALL; lia) ltac:(unfold CRT_CMP2_CALL; lia) X10 X11 SXb' SXd').
intros regs2 mem2 md2 v WS_HJ2 HJ2 HB_HJ2 HP Hv Hcmp Hfr Hpr2 Hmn.
assert (HES : ESTACK = 4096) by reflexivity.
change (CRT_sp1 (regs := regs)) with sp1 in Hfr.
assert (Hv0 : v = w64 0).
{ apply Hcmp. pose proof Hbcs' as (_ & _ & _ & (_ & Gb)). pose proof Hdcs' as (_ & _ & _ & (_ & Gd)).
  exact (proj2 (cl_str_eq (w_H Wc) (ms_mem ms0) bkp dkp nm nm Gb Gd) eq_refl). }
assert (Hlo2 : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. rewrite Hfr by lia. apply Hav; lia. }
assert (Kc : forall a, sp1 <= a < sp1 + CRT_SP_F -> aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) (ms_mem ms0) a)
  by (intros a Ha; apply Hfr; unfold CRT_SP_F in Ha; lia).
assert (Km : forall off, 0 <= off -> off + 8 <= CRT_SP_F -> (off + 8 <= 64 \/ 80 <= off) ->
  forall a, sp1 + off <= a < sp1 + off + 8 -> aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros off H0 H1 H2 a Ha. unfold CRT_SP_F in H1. rewrite Kc by (unfold CRT_SP_F; lia). apply Hav; lia. }
pose proof (crt_live_memnorm HL1) as HMN1.
pose proof (cl_rw_keep _ _ _ _ _ (ms_mem ms0) mem2 _ _ _ _ _ _ _ _ _ _ _ _ _ (sp1 - 2 * ESTACK) sp1 HRW1 HJ2 HB_HJ2
  ltac:(lia) ltac:(unfold CRT_SP_F; lia) Hfr Hpr2 ltac:(intros H0; exact (Hmn (HMN1 H0)))) as HRW2.
pose proof (cl_bregs_eq _ regs2 F HBR1 ltac:(intros r Hr; apply (cl_cs_keep _ _ HP); cbv [In] in Hr |- *; tauto)) as HBR2.
eapply (KL3r fxk lyc Sc Hpc Wc mem2 md2 _ pos Dc Lamc peakc cset saved cap Dback ms regs2 i bkeys dkeys Hmb).
destruct HSP2 as (SBK & SSV).
unfold CRT_SP_AT, CL_SP_KSH, CL_SP_P, CRT_SP_PN, CRT_SP_N, CRT_SP_BACK, CRT_SP_SAVED in *.
refine (conj (conj HRW2 (conj (conj _ _) (conj HBR2 (conj Hi (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))))))))) _).
- lazymatch goal with |- crt_spill _ _ ?off _ =>
    apply (cl_spill_keep8 Wc memc mem2 off); [intros a Ha; change (CRT_sp1 (regs := regs)) with sp1 in Ha; apply (Km off); unfold CRT_SP_AT, CL_SP_KSH, CL_SP_P, CRT_SP_PN, CRT_SP_N, CRT_SP_BACK, CRT_SP_SAVED, CRT_SP_F in *; lia | exact SBK] end.
- lazymatch goal with |- crt_spill _ _ ?off _ =>
    apply (cl_spill_keep8 Wc memc mem2 off); [intros a Ha; change (CRT_sp1 (regs := regs)) with sp1 in Ha; apply (Km off); unfold CRT_SP_AT, CL_SP_KSH, CL_SP_P, CRT_SP_PN, CRT_SP_N, CRT_SP_BACK, CRT_SP_SAVED, CRT_SP_F in *; lia | exact SSV] end.
- exact (Hrd _ (F + CRT_OFF_BACK + PJ_OFF_KEYS) bkeys ltac:(unfold CRT_OFF_BACK, PJ_OFF_KEYS; lia)
    ltac:(unfold CRT_OFF_BACK, PJ_OFF_KEYS; lia) Hlo2 Hbk).
- exact (Hrd _ (doc + PJ_OFF_KEYS) dkeys ltac:(unfold PJ_OFF_KEYS; lia) ltac:(unfold PJ_OFF_KEYS; lia) Hlo2 Hdk).
- rewrite (cl_cs_keep _ _ HP 21%bv) by (cbv [In]; tauto). rewrite KB by (cbv [In]; tauto). exact R21.
- rewrite (cl_cs_keep _ _ HP 22%bv) by (cbv [In]; tauto). rewrite KB by (cbv [In]; tauto). exact R22.
- rewrite (cl_cs_keep _ _ HP 24%bv) by (cbv [In]; tauto). exact X24.
- rewrite (cl_cs_keep _ _ HP 25%bv) by (cbv [In]; tauto). rewrite KB by (cbv [In]; tauto). exact R25.
- lazymatch goal with |- crt_spill _ _ ?off _ =>
    apply (cl_spill_keep8 Wc memc mem2 off); [intros a Ha; change (CRT_sp1 (regs := regs)) with sp1 in Ha; apply (Km off); unfold CRT_SP_AT, CL_SP_KSH, CL_SP_P, CRT_SP_PN, CRT_SP_N, CRT_SP_BACK, CRT_SP_SAVED, CRT_SP_F in *; lia | exact SAT] end.
- lazymatch goal with |- crt_spill _ _ ?off _ =>
    apply (cl_spill_keep8 Wc memc mem2 off); [intros a Ha; change (CRT_sp1 (regs := regs)) with sp1 in Ha; apply (Km off); unfold CRT_SP_AT, CL_SP_KSH, CL_SP_P, CRT_SP_PN, CRT_SP_N, CRT_SP_BACK, CRT_SP_SAVED, CRT_SP_F in *; lia | exact SKSH] end.
- lazymatch goal with |- crt_spill _ _ ?off _ =>
    apply (cl_spill_keep8 Wc memc mem2 off); [intros a Ha; change (CRT_sp1 (regs := regs)) with sp1 in Ha; apply (Km off); unfold CRT_SP_AT, CL_SP_KSH, CL_SP_P, CRT_SP_PN, CRT_SP_N, CRT_SP_BACK, CRT_SP_SAVED, CRT_SP_F in *; lia | exact SP] end.
- lazymatch goal with |- crt_spill _ _ ?off _ =>
    apply (cl_spill_keep8 Wc memc mem2 off); [intros a Ha; change (CRT_sp1 (regs := regs)) with sp1 in Ha; apply (Km off); unfold CRT_SP_AT, CL_SP_KSH, CL_SP_P, CRT_SP_PN, CRT_SP_N, CRT_SP_BACK, CRT_SP_SAVED, CRT_SP_F in *; lia | exact SPN] end.
- lazymatch goal with |- crt_spill _ _ ?off _ =>
    apply (cl_spill_keep8 Wc memc mem2 off); [intros a Ha; change (CRT_sp1 (regs := regs)) with sp1 in Ha; apply (Km off); unfold CRT_SP_AT, CL_SP_KSH, CL_SP_P, CRT_SP_PN, CRT_SP_N, CRT_SP_BACK, CRT_SP_SAVED, CRT_SP_F in *; lia | exact SN] end.
- apply (cl_spill_keep8 Wc (ms_mem ms0) mem2); [intros a Ha; change (CRT_sp1 (regs := regs)) with sp1 in Ha; apply Kc; unfold CL_SP_BK, CRT_SP_F in *; lia | exact SBK0].
- apply (cl_spill_keep8 Wc (ms_mem ms0) mem2); [intros a Ha; change (CRT_sp1 (regs := regs)) with sp1 in Ha; apply Kc; unfold CL_SP_BK2, CRT_SP_F in *; lia | exact SBK20].
- rewrite Hv, Hv0. reflexivity.
Qed.
End L3h.

(* ---- cl_rw ACROSS A CALL THAT KEEPS THE ALLOCATOR STATE AND HAS AN EMPTY FOOTPRINT (same): the Kit's call lemmas for
   the live state, the trees and the freeable shapes; the frames clause for the shadow of doc / back / v ---- *)
Lemma cl_rw_call0 : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms
    (fx' : YK11.FPState) STK1 ly2 W2 mem2 md2 k1,
  cl_rw fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms ->
  (exists WS, AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly2 Sc Hpc W2 mem2 md2 (kj + k1) WS /\
     YCbqGwild.wbudget [] (prh_wk F_check_round_trip) WS) ->
  ajournal_xR (SK := SK) SEGS B PST ARx RZW STK1 (CRT_sp1 (regs := regs)) [] lyc Sc Hpc Wc memc mdc []
    ly2 Sc Hpc W2 mem2 md2 k1 ->
  0 <= STK1 -> frm_zero (@YK11.fp_csr fx') -> fregs_kept_x fxk fx' ->
  prh_ledger B ly2 Sc Hpc W2 mem2 Lamc peakc (cnt + ck_crt_count t cset) SIZE_MAXZ 0 most 0 ->
  ablocks B ly2 Sc = ablocks B lyc Sc ->
  (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem2) ->
  cl_rw fx' ly2 Sc Hpc W2 mem2 md2 (kj + k1) pos Dc Lamc peakc cset saved cap Dback ms.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms fx' STK1 ly2 W2 mem2 md2 k1 HRW HJe HJc
  HSTK HFZ2 HFK2 HLED2 Eab HMN2.
destruct HRW as (Et & HFZ & HFK & HL & Hcs & Hcin & Hsv & Hcopy & Hback & Hd8 & Hrad & Hrab & Hrav & Hpos & Hfd & HPcp
  & (Fc & Hfoc & Efoc) & Hdep & Hpb & (Fb & Hfob & Efob) & Ecap).
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ).
pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPl.
pose proof (crt_live_blocks_perm HL) as HPb.
pose proof (crt_live_dx_apart HL) as HAP.
pose proof (crt_live_frame HL) as HFRM.
pose proof (crt_side_ledger HSD) as HLD.
pose proof (crt_side_peak HSD) as Hpk.
pose proof (crt_side_room HSD) as HRL.
pose proof (crt_side_arodata HSD) as HRO.
pose proof (crt_side_doc HSD) as HDOC.
pose proof (crt_side_doc_blocks HSD) as HDL.
pose proof HJ as (HARc & HLYc & _ & _ & _ & HFRc & _).
pose proof HJc as (_ & HLY1 & _).
pose proof HLY1 as (_ & _ & _ & _ & _ & EFF & _).
assert (EF : frame_addr ly2 CRT_CID pos = frame_addr lyc CRT_CID pos) by (unfold frame_addr; rewrite EFF; reflexivity).
pose proof (crt102rw_side_call LAWS HPRE HTREE lyc Sc Hpc Wc memc mdc kj pos _ Lamc peakc _ 0 0 STK1 [] ly2 Sc Hpc W2 mem2
  md2 k1 Lamc peakc _ 0 0 HL HJc (Forall_nil _) (fun a Hf => False_ind _ (inFP_nil a Hf)) HLED2 ltac:(lia) HRL HDL) as HSD2.
assert (HPB2 : Permutation (ablocks B ly2 Sc) (ablocks B ly S ++ ck_hblks (Dback ++ (saved, cap) :: Dc)))
  by (rewrite Eab; exact HPb).
pose proof (crt102rw_live_call LAWS HPRE lyc Sc Hpc Wc memc mdc kj pos _ Lamc peakc _ 0 0 STK1 [] ly2 Sc Hpc W2 mem2 md2 k1
  _ Lamc peakc _ 0 0 HL HJe HJc HSTK (fun a Hf => False_ind _ (inFP_nil a Hf)) HSD2 HPl HPB2 HAP HMN2) as HL2.
assert (HinL : forall bk, In bk (Dback ++ (saved, cap) :: Dc) -> In bk Lamc).
{ intros bk Hb. apply (Permutation_in _ (Permutation_sym HPl)). apply in_or_app. left. exact Hb. }
assert (HDc : forall bk, In bk Dc -> In bk Lamc) by (intros bk Hb; apply HinL; apply in_or_app; right; right; exact Hb).
assert (HDb : forall bk, In bk Dback -> In bk Lamc) by (intros bk Hb; apply HinL; apply in_or_app; left; exact Hb).
pose proof (crt_frame_listed HFRM) as Hinf.
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc Hinf) as (Fb1 & Fb2 & _).
change (fs_frame_bytes CRT_CID) with 512 in Fb2.
assert (HFr : forall off, 0 <= off -> off + 56 <= 512 -> exists cid0 pos0, In (cid0, pos0) (frames Sc) /\
  frame_addr lyc cid0 pos0 <= frame_addr lyc CRT_CID pos + off /\
  frame_addr lyc CRT_CID pos + off + 56 <= frame_addr lyc cid0 pos0 + fs_frame_bytes cid0).
{ intros off H0 H1. exists CRT_CID, pos. split; [exact Hinf|]. change (fs_frame_bytes CRT_CID) with 512. lia. }
pose proof HTREE as (_ & _ & _ & (_ & (cid & pos' & Hfin & Hfa1 & Hfa2) & _)).
pose proof HPRE as ((HAR & _) & _).
destruct (alx_layout SEGS B ARx LAWS ly S Hp W mem md lyc HAR HLYc) as (_ & Efa & _).
assert (Hfin' : In (cid, pos') (frames Sc)) by (rewrite HFRc; apply in_or_app; right; exact Hfin).
rewrite <- (Efa cid pos') in Hfa1, Hfa2.
unfold cl_rw. rewrite EF.
refine (conj Et (conj HFZ2 (conj _ (conj HL2 (conj Hcs (conj Hcin (conj Hsv (conj _ (conj _ (conj Hd8 (conj _ (conj _ (conj _ (conj Hpos (conj _ (conj HPcp (conj (ex_intro _ Fc (conj _ Efoc)) (conj Hdep (conj Hpb (conj (ex_intro _ Fb (conj _ Efob)) Ecap)))))))))))))))))))).
- intros r0 Hr0. rewrite (HFK2 r0 Hr0). exact (HFK r0 Hr0).
- exact (crt102rw_tree_call LAWS lyc Sc Hpc Wc memc mdc kj STK1 [] ly2 Sc Hpc W2 mem2 md2 k1 Lamc peakc _ 0 Lamc peakc _ 0
    _ _ Dc HARc HJc HLD HLED2 (HFr CRT_OFF_COPY ltac:(unfold CRT_OFF_COPY; lia) ltac:(unfold CRT_OFF_COPY; lia))
    HDc HDc (fun a Hf => False_ind _ (inFP_nil a Hf)) Hcopy).
- exact (crt102rw_tree_call LAWS lyc Sc Hpc Wc memc mdc kj STK1 [] ly2 Sc Hpc W2 mem2 md2 k1 Lamc peakc _ 0 Lamc peakc _ 0
    _ _ Dback HARc HJc HLD HLED2 (HFr CRT_OFF_BACK ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia))
    HDb HDb (fun a Hf => False_ind _ (inFP_nil a Hf)) Hback).
- exact (cl_ra_frame_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ cid pos' doc 56 HARc HJc Hfin' Hfa1 Hfa2 ltac:(lia) Hrad).
- exact (cl_ra_frame_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ CRT_CID pos (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) 56 HARc HJc Hinf
    ltac:(unfold CRT_OFF_BACK; lia)
    ltac:(change (fs_frame_bytes CRT_CID) with 512; unfold CRT_OFF_BACK; lia) ltac:(lia) Hrab).
- exact (cl_ra_frame_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ CRT_CID pos (frame_addr lyc CRT_CID pos + CRT_OFF_V) 56 HARc HJc Hinf
    ltac:(unfold CRT_OFF_V; lia)
    ltac:(change (fs_frame_bytes CRT_CID) with 512; unfold CRT_OFF_V; lia) ltac:(lia) Hrav).
- exact (crt102rw_fd_call LAWS lyc Sc Hpc Wc memc mdc kj STK1 [] ly2 Sc Hpc W2 mem2 md2 k1 Lamc peakc _ 0 Lamc peakc _ 0
    _ DOC_D Dc HARc HJc HLD HLED2 (HFr CRT_OFF_COPY ltac:(unfold CRT_OFF_COPY; lia) ltac:(unfold CRT_OFF_COPY; lia))
    HDc HDc (fun a Hf => False_ind _ (inFP_nil a Hf)) Hfd).
- exact (cl_fo_call _ _ _ _ _ _ kj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HJc HLD HLED2
    (HFr CRT_OFF_COPY ltac:(unfold CRT_OFF_COPY; lia) ltac:(unfold CRT_OFF_COPY; lia)) HDc HDc
    (fun a Hf => False_ind _ (inFP_nil a Hf)) Hfoc).
- exact (cl_fo_call _ _ _ _ _ _ kj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HJc HLD HLED2
    (HFr CRT_OFF_BACK ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia)) HDb HDb
    (fun a Hf => False_ind _ (inFP_nil a Hf)) Hfob).
Qed.

(* ---- A `same` FROM check_round_trip AT THE REALIGNED sp (+0x5f0): the tsame_specX text at n = DOC_D through the
   Kit's call rule; same allocates nothing (S' = S, Hp' = Hp, the ledger at S'), so the continuation gets the allocator
   state unchanged, the answer and the two journals. The text's GUARDED stack-presence premise (PRH_FnEx.v:370,
   `spZ regs <= pa -> YGcallStackUp.astack_up_x ..`) is discharged by its guard being false: the caller gives
   `pa < spZ (ms_regs ms)` (at its one call, in cl_L3r, the root is a kid of back inside a Lam block, whose end is at
   most alloc_ceiling <= sp1 - STK_same DOC_D) ---- *)
Lemma cl_same_call : forall (fxk : YK11.FPState) Wc E ss ms mdc lyc Sc Hpc kj pos Dx Lamc peakc cntc (off pa pb : Z)
    (ta tb : PjTree.jv) (Da Db : list (Z * Z)),
  frm_zero (@YK11.fp_csr fxk) ->
  @st_ok SEGS fxk E ss (restrict (w_H Wc) ms) -> ss_resv ss = None -> ss_pc ss = SIGMA AS_same ->
  bv_unsigned (ew E 2) = sp0 ->
  livea lyc Sc Hpc Wc (ms_mem ms) mdc kj pos Dx Lamc peakc cntc 0 0 ->
  crt_bregs (regs := regs) (ms_regs ms) (frame_addr lyc CRT_CID pos) ->
  getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRT_PC_A + off)) -> 0 <= off < 2048 -> off mod 2 = 0 ->
  getr (ms_regs ms) 10 = w64 pa -> getr (ms_regs ms) 11 = w64 pb -> pa < spZ (ms_regs ms) ->
  PRH_FnEx.prhex_tree lyc Sc Lamc Wc (ms_regs ms) (ms_mem ms) pa ta Da ->
  PRH_FnEx.prhex_tree lyc Sc Lamc Wc (ms_regs ms) (ms_mem ms) pb tb Db ->
  (PjTree.depth ta <= DOC_D)%nat ->
  (forall z, PRH_Reader.pj_footR pa Da z -> ~ (spZ (ms_regs ms) - @STK_same prh_img_A DOC_D <= z < spZ (ms_regs ms))) ->
  (forall z, PRH_Reader.pj_footR pb Db z -> ~ (spZ (ms_regs ms) - @STK_same prh_img_A DOC_D <= z < spZ (ms_regs ms))) ->
  (forall (fx' : YK11.FPState) ly2 W2 regs2 mem2 md2 k1,
     frm_zero (@YK11.fp_csr fx') -> fregs_kept_x fxk fx' ->
     (exists WS, AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly2 Sc Hpc W2 mem2 md2 (kj + k1) WS /\
     YCbqGwild.wbudget [] (prh_wk F_check_round_trip) WS) ->
     ajournal_xR (SK := SK) SEGS B PST ARx RZW (@STK_same prh_img_A DOC_D) (CRT_sp1 (regs := regs)) [] lyc Sc Hpc Wc (ms_mem ms)
       mdc [] ly2 Sc Hpc W2 mem2 md2 k1 ->
     aregs_preserved (ms_regs ms) regs2 ->
     (ta = tb /\ getr regs2 10 = w64 1 \/ ta <> tb /\ getr regs2 10 = w64 0) ->
     ablocks B ly2 Sc = ablocks B lyc Sc ->
     prh_ledger B ly2 Sc Hpc W2 mem2 Lamc peakc cntc SIZE_MAXZ 0 most 0 ->
     (YAkMemnorm.memnorm SEGS (ms_mem ms) -> YAkMemnorm.memnorm SEGS mem2) ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2
       (mkCfg (@YK11.mkst fx' regs2 (Z_to_bv 64 (BASE + (CRT_PC_A + off))) mem2 (YK11.seg_rom SEGS)) md2) QFa) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg ms mdc) QFa.
Proof.
intros fxk Wc E ss ms mdc lyc Sc Hpc kj pos Dx Lamc peakc cntc off pa pb ta tb Da Db HFZ HS Hrv Hpcs HE2 HL HBR Hra Hoff
  Hoff2 X10 X11 Hpa HTa HTb Hdep HFa HFb HK.
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_side HL) as HSD.
pose proof (crt_side_ledger HSD) as HLc.
assert (HSTKs : 0 <= @STK_same prh_img_A DOC_D /\ @STK_same prh_img_A DOC_D + 240 <= STKC) by (vm_compute; split; discriminate).
refine (crt102rw_call LAWS HPRE fxk (@STK_same prh_img_A DOC_D) [] off (SIGMA AS_same) Wc E ss ms mdc lyc Sc Hpc kj pos Dx
  Lamc peakc cntc 0 0 _ HFZ HS Hrv Hpcs HE2 HL HBR Hra Hoff Hoff2 (proj1 HSTKs) (proj2 HSTKs) _ _ _).
- intros a Hfa. exfalso. exact (inFP_nil a Hfa).
- (* same's text is plain (SRr, fpostm at wle): into the call rule's R premise by Crt102Kit.crt102rw_lift_x *)
  intros ch1 HPRE1. apply (crt102rw_lift_x (B := B) (ARx := ARx) fxk); [exact HFZ|].
  (* the guard `spZ regs <= pa` of the stack-presence premise is false here (Hpa), so the premise holds vacuously *)
  exact (SAME fxk lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) mdc ch1 pa pb ta tb Da Db Lamc peakc cntc SIZE_MAXZ 0 most 0
    HPRE1 (fun Hle => False_ind _ (Z.lt_irrefl pa (Z.lt_le_trans _ _ _ Hpa Hle))) X10 X11 HTa HTb Hdep HFa HFb HLc).
- intros fx' ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HFZ2 HFK2 HJe HJc HP
    ((_ & Hres & _ & _ & EHp & ES & Eab & HLED2) & HMNk).
  subst S2 Hp2.
  exact (HK fx' ly2 W2 regs2 mem2 md2 k1 HFZ2 HFK2 HJe HJc HP Hres Eab HLED2 HMNk).
Qed.

(* ---- the entry state of the member loop's second half (cl_ss3; extras 64 = n - i, 65 = 56 i, 66 = saved, 67 = at,
   68 = doc, 69 = back.kids, 70 = doc->kids, 71 = &back.keys[i]) ---- *)
Lemma cl_L3x_entry : forall (fxk : YK11.FPState) (Wc : world SEGS) memc rg pc cs cn ko saved atv F bkids dkids bk8,
  conds_ok (TE regs rg [w64 cn; w64 ko; w64 saved; w64 atv; w64 doc; w64 bkids; w64 dkids; w64 bk8]) cs ->
  getr rg 9 = w64 (CRT_sp1 (regs := regs)) -> getr rg 26 = w64 SHADOW_OFF -> getr rg 27 = w64 F ->
  2 ^ 46 <= CRT_sp1 (regs := regs) -> CRT_sp1 (regs := regs) + 96 <= 2 ^ 47 -> CRT_sp1 (regs := regs) mod 32 = 0 ->
  4096 <= doc -> doc + 56 <= CRT_sp1 (regs := regs) -> doc mod 8 = 0 ->
  4096 <= F -> F + 512 <= CRT_sp1 (regs := regs) -> F mod 32 = 0 -> (doc + 56 <= F \/ F + 512 <= doc) ->
  1 <= cn <= 2 ^ 54 -> 0 <= ko <= 2 ^ 60 -> 0 <= saved < 2 ^ 64 -> 0 <= atv < 2 ^ 64 -> 0 <= bkids < 2 ^ 64 ->
  0 <= dkids < 2 ^ 64 -> 0 <= bk8 < 2 ^ 64 ->
  (forall a, CRT_sp1 (regs := regs) + 80 <= a < CRT_sp1 (regs := regs) + 96 -> apresent (w_H Wc) memc a) ->
  cl_sp2 Wc memc F saved ->
  crt_spill (regs := regs) Wc memc CRT_SP_AT atv ->
  crt_spill (regs := regs) Wc memc CL_SP_KSH (shadow_addr (doc + PJ_OFF_KIDS)) ->
  crt_spill (regs := regs) Wc memc CL_SP_P (doc + PJ_OFF_KIDS) ->
  crt_spill (regs := regs) Wc memc CL_SP_BK bk8 -> crt_spill (regs := regs) Wc memc CL_SP_BK2 bk8 ->
  crt_spill (regs := regs) Wc memc CRT_SP_PN cn -> crt_spill (regs := regs) Wc memc CRT_SP_N ko ->
  rd_u64 SEGS (mrestrict (w_H Wc) memc) (F + 56) bkids -> rd_u64 SEGS (mrestrict (w_H Wc) memc) (doc + 24) dkids ->
  st_ok_pi SEGS VAL (TE regs rg [w64 cn; w64 ko; w64 saved; w64 atv; w64 doc; w64 bkids; w64 dkids; w64 bk8]) (cl_ss3 pc cs)
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + pc)) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS CL_Bx [] (TE regs rg [w64 cn; w64 ko; w64 saved; w64 atv; w64 doc; w64 bkids; w64 dkids; w64 bk8])
    (mrestrict (w_H Wc) memc).
Proof.
intros fxk Wc memc rg pc cs cn ko saved atv F bkids dkids bk8 Hcs R9 R26 R27 H1 H2 H3 H4 H5 H6 HF0 HF1 HF2 HdF Hcn Hko
  Hsv Hatv Hbki Hdki Hbk8 HP (VBK & VSV) VAT VKSH VP VBKa VBKb VPN VN [_ VBKIDS] [_ VDKIDS].
unfold crt_spill, CL_SP_P, CL_SP_KSH, CRT_SP_AT, CRT_SP_PN, CRT_SP_N, CRT_SP_BACK, CRT_SP_SAVED, CRT_OFF_BACK,
  CL_SP_BK, CL_SP_BK2, PJ_OFF_KIDS in *.
set (sp1 := CRT_sp1 (regs := regs)) in *.
set (E := TE regs rg [w64 cn; w64 ko; w64 saved; w64 atv; w64 doc; w64 bkids; w64 dkids; w64 bk8]).
assert (W9 : ew E (xr 9) = w64 sp1) by (unfold E, xr; rewrite (te_cur regs rg _ 9%bv 9) by reflexivity; exact R9).
assert (W26 : ew E (xr 26) = w64 SHADOW_OFF) by (unfold E, xr; rewrite (te_cur regs rg _ 26%bv 26) by reflexivity; exact R26).
assert (W27 : ew E (xr 27) = w64 F) by (unfold E, xr; rewrite (te_cur regs rg _ 27%bv 27) by reflexivity; exact R27).
assert (E64 : ew E 64 = w64 cn) by exact (te_more_lt regs rg _ 0 ltac:(lia)).
assert (E65 : ew E 65 = w64 ko) by exact (te_more_lt regs rg _ 1 ltac:(lia)).
assert (E66 : ew E 66 = w64 saved) by exact (te_more_lt regs rg _ 2 ltac:(lia)).
assert (E67 : ew E 67 = w64 atv) by exact (te_more_lt regs rg _ 3 ltac:(lia)).
assert (E68 : ew E 68 = w64 doc) by exact (te_more_lt regs rg _ 4 ltac:(lia)).
assert (E69 : ew E 69 = w64 bkids) by exact (te_more_lt regs rg _ 5 ltac:(lia)).
assert (E70 : ew E 70 = w64 dkids) by exact (te_more_lt regs rg _ 6 ltac:(lia)).
assert (E71 : ew E 71 = w64 bk8) by exact (te_more_lt regs rg _ 7 ltac:(lia)).
assert (UB : forall k v, ew E k = w64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E k) = v)
  by (intros k v Hk Hv; rewrite Hk; apply unsigned_lit_small; exact Hv).
split; [|unfold sh_ok; apply Forall_nil].
apply ts_st_ok.
all: try change (TE regs rg [w64 cn; w64 ko; w64 saved; w64 atv; w64 doc; w64 bkids; w64 dkids; w64 bk8]) with E.
- apply te_regs_ok.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
  + apply (ts_rok E _ (xr 9) sp1); [apply UB; [exact W9 | lia] | lia | lia | |].
    { intros o Ho. apply (apresent_writable SEGS). apply HP. cbn in Ho. lia. }
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (ts_chunk E _ _ 24 8 (SOff 66 0) saved); [| cbn; lia | cbn; lia | exact VSV].
      rewrite denot_lit_U, (U_atom_off E 66 saved 0 E66) by lia. rewrite Z.add_0_r. reflexivity.
    * apply (ts_chunk E _ _ 32 8 (SOff 67 0) atv); [| cbn; lia | cbn; lia | exact VAT].
      rewrite denot_lit_U, (U_atom_off E 67 atv 0 E67) by lia. rewrite Z.add_0_r. reflexivity.
    * apply (ts_chunk E _ _ 40 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 68 24) (SLit 3)) (SOff (xr 26) 0)) (shadow_addr (doc + 24)));
        [| unfold shadow_addr, SHADOW_OFF; pose proof (Z.div_pos (doc + 24) 8 ltac:(lia) ltac:(lia));
           assert ((doc + 24) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia); cbn; lia | cbn; lia | exact VKSH].
      rewrite denot_lit_U. f_equal. exact (cl_sh_off E (xr 26) 68 doc 24 W26 E68 ltac:(lia) ltac:(lia) ltac:(lia)).
    * apply (ts_chunk E _ _ 48 8 (SOff 68 24) (doc + 24)); [| cbn; lia | cbn; lia | exact VP].
      rewrite denot_lit_U, (U_atom_off E 68 doc 24 E68) by lia. reflexivity.
    * apply (ts_chunk E _ _ 56 8 (SOff (xr 27) 32) (F + 32)); [| cbn; lia | cbn; lia | exact VBK].
      rewrite denot_lit_U, (U_atom_off E (xr 27) F 32 W27) by lia. reflexivity.
    * apply (ts_chunk E _ _ 64 8 (SOff 71 0) bk8); [| cbn; lia | cbn; lia | exact VBKa].
      rewrite denot_lit_U, (U_atom_off E 71 bk8 0 E71) by lia. rewrite Z.add_0_r. reflexivity.
    * apply (ts_chunk E _ _ 72 8 (SOff 71 0) bk8); [| cbn; lia | cbn; lia | exact VBKb].
      rewrite denot_lit_U, (U_atom_off E 71 bk8 0 E71) by lia. rewrite Z.add_0_r. reflexivity.
    * apply (ts_chunk E _ _ 80 8 (SOff 64 0) cn); [| cbn; lia | cbn; lia | exact VPN].
      rewrite denot_lit_U, (U_atom_off E 64 cn 0 E64) by lia. rewrite Z.add_0_r. reflexivity.
    * apply (ts_chunk E _ _ 88 8 (SOff 65 0) ko); [| cbn; lia | cbn; lia | exact VN].
      rewrite denot_lit_U, (U_atom_off E 65 ko 0 E65) by lia. rewrite Z.add_0_r. reflexivity.
  + apply (ts_rok E _ (xr 27) F); [apply UB; [exact W27 | lia] | lia | lia | intros o Ho; cbn in Ho; lia |].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (ts_chunk E _ _ 56 8 (SOff 69 0) bkids); [| cbn; lia | cbn; lia | exact VBKIDS].
    rewrite denot_lit_U, (U_atom_off E 69 bkids 0 E69) by lia. rewrite Z.add_0_r. reflexivity.
  + apply (ts_rok E _ 68 doc); [apply UB; [exact E68 | lia] | lia | lia | intros o Ho; cbn in Ho; lia |].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (ts_chunk E _ _ 24 8 (SOff 70 0) dkids); [| cbn; lia | cbn; lia | exact VDKIDS].
    rewrite denot_lit_U, (U_atom_off E 70 dkids 0 E70) by lia. rewrite Z.add_0_r. reflexivity.
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !ts_bv_some.
  rewrite (UB _ _ W9 ltac:(lia)), (UB _ _ W27 ltac:(lia)), (UB _ _ E68 ltac:(lia)).
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact Hcs | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite (UB _ _ W9 ltac:(lia)), (UB _ _ W26 ltac:(unfold SHADOW_OFF; lia)), (UB _ _ W27 ltac:(lia)),
    (UB _ _ E68 ltac:(lia)), (UB _ _ E64 ltac:(lia)), (UB _ _ E65 ltac:(lia)).
  change (2 ^ 5) with 32. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
  unfold SHADOW_OFF. repeat split; lia.
Qed.

(* ======================================================================================================== *)
(* THE MEMBER LOOP'S SECOND HALF: from L3r (the keys compared EQUAL) at i = at, or from L3s (same said TRUE) at i <> at,
   the update (+0x5f8 .. +0x630: n - i - 1 into 0x50, 56 (i + 1) into 0x58, s5 += 1, s6 -= 1, s9 += 8, the three
   argument registers for i + 1) and `bnez a3` back to L3 (i + 1) or on to C *)
Section L3t.
Variable mb : nat.
Hypothesis KL3n : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i bkeys dkeys,
  (length ms - i < mb)%nat ->
  cl_at_L3 fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i bkeys dkeys ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk CRT_L3_OFF rg memc mdc) QFa.
Hypothesis KC : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg,
  cl_at_C fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk CRT_C_OFF rg memc mdc) QFa.

Lemma cl_L3_tail : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i bkeys dkeys
    (pc0 : Z) (a0 : Z),
  (length ms - i <= mb)%nat ->
  cl_l3core fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i bkeys dkeys ->
  getr rg 10 = w64 a0 ->
  (pc0 = CRT_CMP2_CALL + 4 /\ a0 = 0 /\ i = cm_at ms \/ pc0 = CRT_SAME_CALL + 4 /\ a0 = 1) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk pc0 rg memc mdc) QFa.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i bkeys dkeys pc0 a0 Hmb HC R10 Hcase.
destruct HC as (HRW & HSP2 & HBR & Hi & Hbk & Hdk & R21 & R22 & R24 & R25 & SAT & SKSH & SP & SPN & SN & SBK & SBK2).
pose proof HRW as (Et & HFZ & HFK & HL & Hcs & Hcin & Hsv & Hcopy & Hback & Hd8 & Hrad & Hrab & Hrav & _).
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ).
pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPl.
pose proof (crt_live_frame HL) as HFRM.
pose proof (crt_live_memnorm HL) as HPM.
pose proof (crt_side_ledger HSD) as HLD.
pose proof (crt_side_arodata HSD) as HRO.
pose proof (crt_side_doc HSD) as HDOC.
pose proof (crt_side_doc_blocks HSD) as HDL.
pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkp & _).
pose proof (crt_bregs_sp HBR) as R2.
pose proof (crt_bregs_gp HBR) as R3.
pose proof (crt_bregs_tp HBR) as R4.
pose proof (crt_bregs_s0 HBR) as R8.
pose proof (crt_bregs_s1 HBR) as R9.
pose proof (crt_bregs_s2 HBR) as R18.
pose proof (crt_bregs_s4 HBR) as R20.
pose proof (crt_bregs_s3 HBR) as R19.
pose proof (crt_bregs_s7 HBR) as R23.
pose proof (crt_bregs_s10 HBR) as R26.
pose proof (crt_bregs_s11 HBR) as R27.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof YM05.alloc_ceiling_lt as Hc47.
pose proof cl_sp0 as (H16 & Hsp0 & H47). pose proof cl_sp1 as (Hs32 & Hs1).
assert (HSTKC : STKC = 27632) by (vm_compute; reflexivity).
pose proof cl_doc_low as (Hdl0 & Hdl1).
pose proof (cl_doc_F _ _ _ _ _ _ _ _ HJ) as HdF.
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc (crt_frame_listed HFRM))
  as (Fb1 & Fb2 & _).
change (fs_frame_bytes CRT_CID) with 512 in Fb2.
destruct (alx_frames SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc (crt_frame_listed HFRM))
  as (F32 & _).
set (F := frame_addr lyc CRT_CID pos) in *.
set (sp1 := CRT_sp1 (regs := regs)) in *.
rewrite Et in HDOC.
assert (Etc : tc = PjTree.JObj (PjTree.pj_set_model ms ck_MOD_AT (PjTree.JStr ck_STAMP))) by (unfold crt_tc; rewrite Et; reflexivity).
rewrite Etc in Hback.
destruct (cl_node_obj _ _ _ _ _ HDOC) as (dnum & dkids & dkeys' & dcap & Di & _ & _ & Hdh & Hdn & Hdc & _ & _).
pose proof Hdh as (_ & _ & _ & _ & VDK & _).
destruct (cl_node_obj _ _ _ _ _ Hback) as (bnum & bkids & bkeys' & bcap & Bi & _ & _ & Hbh & _ & _ & _ & _).
pose proof Hbh as (_ & _ & _ & _ & VBK & _).
assert (VBK' : rd_u64 SEGS (mrestrict (w_H Wc) memc) (F + 56) bkids)
  by (replace (F + 56) with (F + CRT_OFF_BACK + 24) by (unfold CRT_OFF_BACK; lia); exact VBK).
assert (Hsv0 : 4096 <= saved < 2 ^ 47).
{ assert (Hin : In (saved, cap) Lamc).
  { apply (Permutation_in _ (Permutation_sym HPl)). apply in_or_app. left. apply in_or_app. right. left. reflexivity. }
  destruct (cl_blk_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLD Hin) as (Hk & Ha & Hb).
  change (@cf_head CfParams_preset) with 16 in Ha. lia. }
assert (HinL : forall bk, In bk (Dback ++ (saved, cap) :: Dc) -> In bk Lamc).
{ intros bk Hb. apply (Permutation_in _ (Permutation_sym HPl)). apply in_or_app. left. exact Hb. }
assert (HDb : forall bk, In bk Dback -> In bk Lamc) by (intros bk Hb; apply HinL; apply in_or_app; left; exact Hb).
destruct (nth_error ms i) as [[nm u]|] eqn:Hnth; [|apply nth_error_None in Hnth; lia].
destruct (cm_set_member ms (PjTree.JStr ck_STAMP) i nm u Hnth) as (u' & Hnth' & _ & _).
destruct (cl_obj_key _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLD Hback HDb
  ltac:(replace (frame_addr lyc CRT_CID pos + CRT_OFF_BACK + 32) with
          (frame_addr lyc CRT_CID pos + CRT_OFF_BACK + PJ_OFF_KEYS) by (unfold PJ_OFF_KEYS; lia); exact Hbk) Hnth')
  as (bkp & bkb & Hbkp & _ & _ & _ & _ & Hbk4 & Hbk8 & Hbkc & _).
destruct (cl_obj_key _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLD HDOC HDL
  ltac:(replace (doc + 32) with (doc + PJ_OFF_KEYS) by (unfold PJ_OFF_KEYS; lia); exact Hdk) Hnth)
  as (dkp & dkb & Hdkp & _ & _ & _ & _ & Hdk4 & Hdk8 & Hdkc & _).
assert (Hlen : (length ms <= length (PjTree.pj_set_model ms ck_MOD_AT (PjTree.JStr ck_STAMP)))%nat)
  by (rewrite cm_set_len; destruct (Nat.eqb (cm_at ms) (length ms)); lia).
assert (Hnr : Z.of_nat (length ms) <= 2 ^ 54).
{ destruct Hdc as [(-> & _ & _) | (Hc0 & Hkd & _)]; [lia|].
  destruct (cl_blk_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLD Hkd) as (_ & Hb0 & Hb).
  change (@cf_head CfParams_preset) with 16 in Hb0. lia. }
set (n := Z.of_nat (length ms)) in *.
assert (Hat : (cm_at ms <= length ms)%nat) by apply cm_at_le.
pose proof VBK' as [Rbki _]. pose proof VDK as [Rdki _].
pose proof Hbk as [Rbk _]. pose proof Hdk as [Rdk _].
set (E := TE regs rg [w64 (n - Z.of_nat i); w64 (56 * Z.of_nat i); w64 saved; w64 (Z.of_nat (cm_at ms)); w64 doc;
  w64 bkids; w64 dkids; w64 (bkeys + 8 * Z.of_nat i)]).
assert (ENTRY : forall pc cs, conds_ok E cs ->
  st_ok_pi SEGS VAL E (cl_ss3 pc cs)
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + pc)) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS CL_Bx [] E (mrestrict (w_H Wc) memc)).
{ intros pc cs Hcs0. exact (cl_L3x_entry fxk Wc memc rg pc cs (n - Z.of_nat i) (56 * Z.of_nat i) saved (Z.of_nat (cm_at ms))
    F bkids dkids (bkeys + 8 * Z.of_nat i) Hcs0 R9 R26 R27 ltac:(lia) ltac:(lia) Hs32 ltac:(lia) ltac:(lia) Hd8
    ltac:(lia) ltac:(lia) F32 HdF ltac:(unfold n in *; lia) ltac:(unfold n in *; lia) ltac:(lia) ltac:(lia) Rbki Rdki
    ltac:(unfold n in *; lia) ltac:(intros a Ha; apply Hstkp; lia) HSP2 SAT SKSH SP SBK SBK2 SPN SN VBK'
    ltac:(replace (doc + 24) with (doc + PJ_OFF_KIDS) by (unfold PJ_OFF_KIDS; lia); exact VDK)). }
pose (RUNTO := @crt_run_to_xw_inv fxk rc SK A_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (YSRrMemnorm.srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)) WS_HJ).
assert (HEI : img_env VAL A_LIM E) by apply te_env.
assert (W9 : ew E (xr 9) = w64 sp1) by (unfold E, xr; rewrite (te_cur regs rg _ 9%bv 9) by reflexivity; exact R9).
assert (X41 : bv_unsigned (ew E 41) = sp1) by (change 41%nat with (xr 9); rewrite W9; apply unsigned_lit_small; lia).
assert (UA : U E (SOff 42 0) = a0).
{ change 42%nat with (xr 10). rewrite ts_U0. unfold E, xr. rewrite (te_cur regs rg _ 10%bv 10) by reflexivity. rewrite R10.
  destruct Hcase as [(_ & -> & _) | (_ & ->)]; reflexivity. }
assert (U22 : U E (SOff 54 0) = (Z.of_nat (cm_at ms) - Z.of_nat i) mod 2 ^ 64).
{ change 54%nat with (xr 22). rewrite ts_U0. unfold E, xr. rewrite (te_cur regs rg _ 22%bv 22) by reflexivity. rewrite R22.
  unfold w64. apply unsigned_lit_small. apply Z.mod_pos_bound. lia. }
assert (UC : U E (SOff 64 (-1)) = n - Z.of_nat i - 1).
{ assert (E64 : ew E 64 = w64 (n - Z.of_nat i)) by exact (te_more_lt regs rg _ 0 ltac:(lia)).
  rewrite (U_atom_off E 64 (n - Z.of_nat i) (-1) E64) by (unfold n in *; lia). lia. }
(* the run's end: what it wrote ([0x50, 0x60)), the kept registers, the spills *)
assert (FIN : forall ms0 md0 kj0,
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc (ms_mem ms0) md0 kj0 WS_HJ ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS (ms_mem ms0)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 80 <= a < sp1 + 96) ->
     aview SEGS (w_H Wc) (ms_mem ms0) a = aview SEGS (w_H Wc) memc a) ->
  (forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) (ms_mem ms0) a) ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 23; 26; 27]%bv -> getr (ms_regs ms0) r = getr rg r) ->
  cl_rw fxk lyc Sc Hpc Wc (ms_mem ms0) md0 kj0 pos Dc Lamc peakc cset saved cap Dback ms /\
  cl_sp2 Wc (ms_mem ms0) F saved /\ crt_bregs (regs := regs) (ms_regs ms0) F /\
  crt_spill (regs := regs) Wc (ms_mem ms0) CRT_SP_AT (Z.of_nat (cm_at ms)) /\
  crt_spill (regs := regs) Wc (ms_mem ms0) CL_SP_KSH (shadow_addr (doc + PJ_OFF_KIDS)) /\
  crt_spill (regs := regs) Wc (ms_mem ms0) CL_SP_P (doc + PJ_OFF_KIDS) /\
  rd_u64 SEGS (mrestrict (w_H Wc) (ms_mem ms0)) (F + CRT_OFF_BACK + PJ_OFF_KEYS) bkeys /\
  rd_u64 SEGS (mrestrict (w_H Wc) (ms_mem ms0)) (doc + PJ_OFF_KEYS) dkeys).
{ intros ms0 md0 kj0 HJ0 HPM0 Hav Hpr KB.
  assert (K8 : forall off, 0 <= off -> off + 8 <= 80 -> forall a, sp1 + off <= a < sp1 + off + 8 ->
    aview SEGS (w_H Wc) (ms_mem ms0) a = aview SEGS (w_H Wc) memc a) by (intros off H0 H1 a Ha; apply Hav; lia).
  assert (Hrd : forall a v, a + 8 <= YM05.alloc_ceiling -> 0 <= a -> rd_u64 SEGS (mrestrict (w_H Wc) memc) a v ->
    rd_u64 SEGS (mrestrict (w_H Wc) (ms_mem ms0)) a v).
  { intros a v Ha0 Ha1 [Rv Vv]. split; [exact Rv|]. apply (ts_vm_av (w_H Wc) (w_H Wc) memc (ms_mem ms0)); [|exact Vv].
    intros j Hj. apply Hav; lia. }
  destruct HSP2 as (SBKa & SSV).
  unfold CRT_SP_AT, CL_SP_KSH, CL_SP_P, CRT_SP_BACK, CRT_SP_SAVED in *.
  refine (conj (cl_rw_keep _ _ _ _ _ memc (ms_mem ms0) _ _ _ _ _ _ _ _ _ _ _ _ _ (sp1 + 80) (sp1 + 96) HRW HJ0 HB_HJ
    ltac:(lia) ltac:(unfold CRT_SP_F; lia) Hav Hpr HPM0) (conj (conj _ _) (conj (cl_bregs_eq rg (ms_regs ms0) F HBR KB)
    (conj _ (conj _ (conj _ (conj _ _))))))).
  - exact (cl_spill_keep8 Wc memc (ms_mem ms0) 56 _ (K8 56 ltac:(lia) ltac:(lia)) SBKa).
  - exact (cl_spill_keep8 Wc memc (ms_mem ms0) 24 _ (K8 24 ltac:(lia) ltac:(lia)) SSV).
  - exact (cl_spill_keep8 Wc memc (ms_mem ms0) 32 _ (K8 32 ltac:(lia) ltac:(lia)) SAT).
  - exact (cl_spill_keep8 Wc memc (ms_mem ms0) 40 _ (K8 40 ltac:(lia) ltac:(lia)) SKSH).
  - exact (cl_spill_keep8 Wc memc (ms_mem ms0) 48 _ (K8 48 ltac:(lia) ltac:(lia)) SP).
  - exact (Hrd (F + CRT_OFF_BACK + PJ_OFF_KEYS) bkeys ltac:(unfold CRT_OFF_BACK, PJ_OFF_KEYS; lia)
      ltac:(unfold CRT_OFF_BACK, PJ_OFF_KEYS; lia) Hbk).
  - exact (Hrd (doc + PJ_OFF_KEYS) dkeys ltac:(unfold PJ_OFF_KEYS; lia) ltac:(unfold PJ_OFF_KEYS; lia) Hdk). }
assert (Hcond0 : forall rest, conds_ok E rest ->
  conds_ok E ((if Z.eqb a0 0 then cl_cR_eq else cl_cS_ok) :: (if Z.eqb a0 0 then [cl_cR_at] else []) ++ rest)).
{ intros rest Hr. destruct Hcase as [(_ & -> & Ei) | (_ & ->)]; cbn [Z.eqb app].
  - split; [unfold acond_ok, cl_cR_eq; cbn [ac_c ac_a ac_b]; change (xr 10) with 42%nat; rewrite branch_eq_U, UA, U_SLit;
      reflexivity|].
    split; [|exact Hr]. unfold acond_ok, cl_cR_at; cbn [ac_c ac_a ac_b]. change (xr 22) with 54%nat.
    rewrite branch_eq_U, U22, U_SLit, Ei, Z.sub_diag. reflexivity.
  - split; [|exact Hr]. unfold acond_ok, cl_cS_ok; cbn [ac_c ac_a ac_b]. change (xr 10) with 42%nat.
    rewrite branch_ne_U, UA, U_SLit. reflexivity. }
unfold crt_cfg.
destruct (Z.eq_dec (n - Z.of_nat i - 1) 0) as [Hlast | Hmore].
- (* ---- the last member: on to C ---- *)
  assert (Hcs0 := Hcond0 [cl_cR_last] ltac:(split; [|exact I]; unfold acond_ok, cl_cR_last; cbn [ac_c ac_a ac_b];
    rewrite branch_eq_U, UC, U_SLit, Hlast; reflexivity)).
  destruct (ENTRY (CRT_PC_A + pc0) _ Hcs0) as [HS SHOK].
  destruct Hcase as [(-> & -> & _) | (-> & ->)]; cbn [Z.eqb app] in HS;
  (paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM CL_SPAN (CRT_PC_A + CRT_C_OFF);
   [ .. | lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end;
     repeat (first [apply awr_ok_cons_ro; [cbn; lia|]
                   | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ (xr 9) (sp1 - sp0));
                       [reflexivity | change (xr 9) with 41%nat; rewrite X41; lia | cbn; lia | cbn; lia |]]);
     apply awr_ok_nil | ]).
  all: assert (Hav : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 80 <= a < sp1 + 96) ->
         aview SEGS (w_H Wc) (ms_mem ms0) a = aview SEGS (w_H Wc) memc a);
    [ apply (ts_keep Wc _ _ memc (ms_mem ms0) _ HFr); intros a (r & Hri & Hr); vm_compute in Hri;
      repeat (destruct Hri as [<- | Hri]; [cbn [YP09.r_wlo YP09.r_whi YP09.r_base base_val] in Hr; rewrite ?X41 in Hr; lia |]);
      destruct Hri | ].
  all: assert (Hpr : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) (ms_mem ms0) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  all: assert (KB : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 23; 26; 27]%bv -> getr (ms_regs ms0) r = getr rg r)
    by (intros r Hr; unfold E in HS; cbv [In] in Hr; repeat (destruct Hr as [<- | Hr]; [clkeep HS |]); destruct Hr).
  all: destruct (FIN ms0 _ _ HJ HPM Hav Hpr KB) as (HRW1 & HSP21 & HBR1 & SAT1 & SKSH1 & SP1 & Hbk1 & Hdk1).
  all: clear HF HFr HG.
  all: pmkst HS.
  all: lazymatch goal with |- context [Z_to_bv 64 (BASE + ?pc)] =>
    replace pc with (CRT_PC_A + CRT_C_OFF) by (vm_compute; reflexivity) end.
  all: exact (KC fxk lyc Sc Hpc Wc (ms_mem ms0) _ _ pos Dc Lamc peakc cset saved cap Dback ms (ms_regs ms0)
    (conj HRW1 (conj HSP21 (conj HBR1 SAT1)))).
- (* ---- another member: back to L3 at i + 1, the measure length ms - i dropping by one ---- *)
  assert (Hcs0 := Hcond0 [cl_cR_more] ltac:(split; [|exact I]; unfold acond_ok, cl_cR_more; cbn [ac_c ac_a ac_b];
    rewrite branch_ne_U, UC, U_SLit; apply negb_true_iff, Z.eqb_neq; exact Hmore)).
  destruct (ENTRY (CRT_PC_A + pc0) _ Hcs0) as [HS SHOK].
  destruct Hcase as [(-> & -> & _) | (-> & ->)]; cbn [Z.eqb app] in HS;
  (paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM CL_SPAN (CRT_PC_A + CRT_L3_OFF);
   [ .. | lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end;
     repeat (first [apply awr_ok_cons_ro; [cbn; lia|]
                   | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ (xr 9) (sp1 - sp0));
                       [reflexivity | change (xr 9) with 41%nat; rewrite X41; lia | cbn; lia | cbn; lia |]]);
     apply awr_ok_nil | ]).
  all: assert (Hav : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 80 <= a < sp1 + 96) ->
         aview SEGS (w_H Wc) (ms_mem ms0) a = aview SEGS (w_H Wc) memc a);
    [ apply (ts_keep Wc _ _ memc (ms_mem ms0) _ HFr); intros a (r & Hri & Hr); vm_compute in Hri;
      repeat (destruct Hri as [<- | Hri]; [cbn [YP09.r_wlo YP09.r_whi YP09.r_base base_val] in Hr; rewrite ?X41 in Hr; lia |]);
      destruct Hri | ].
  all: assert (Hpr : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) (ms_mem ms0) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  all: assert (KB : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 23; 26; 27]%bv -> getr (ms_regs ms0) r = getr rg r)
    by (intros r Hr; unfold E in HS; cbv [In] in Hr; repeat (destruct Hr as [<- | Hr]; [clkeep HS |]); destruct Hr).
  all: destruct (FIN ms0 _ _ HJ HPM Hav Hpr KB) as (HRW1 & HSP21 & HBR1 & SAT1 & SKSH1 & SP1 & Hbk1 & Hdk1).
  all: prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11; prreg HS (12%bv : bv 5) Q12;
    prreg HS (21%bv : bv 5) Q21; prreg HS (22%bv : bv 5) Q22; prreg HS (25%bv : bv 5) Q25.
  all: clear HF HFr HG.
  all: pmkst HS.
  all: lazymatch goal with |- context [Z_to_bv 64 (BASE + ?pc)] =>
    replace pc with (CRT_PC_A + CRT_L3_OFF) by (vm_compute; reflexivity) end.
  all: eapply (KL3n fxk lyc Sc Hpc Wc (ms_mem ms0) _ _ pos Dc Lamc peakc cset saved cap Dback ms (ms_regs ms0)
    (Datatypes.S i) bkeys dkeys ltac:(unfold n in *; lia)).
  all: refine (conj HRW1 (conj HSP21 (conj HBR1 (conj _ (conj Hbk1 (conj Hdk1 (conj _ (conj _
    (conj _ (conj _ (conj _ (conj _ (conj SAT1 (conj SKSH1 (conj SP1 (conj _ _)))))))))))))))).
  all: try (unfold n in *; lia).
  all: assert (E71 : ew E 71 = w64 (bkeys + 8 * Z.of_nat i)) by exact (te_more_lt regs rg _ 7 ltac:(lia)).
  all: assert (E64 : ew E 64 = w64 (n - Z.of_nat i)) by exact (te_more_lt regs rg _ 0 ltac:(lia)).
  all: assert (E65 : ew E 65 = w64 (56 * Z.of_nat i)) by exact (te_more_lt regs rg _ 1 ltac:(lia)).
  all: assert (W24 : ew E 56 = w64 (dkeys + 8 * Z.of_nat i))
    by (change 56%nat with (xr 24); unfold E, xr; rewrite (te_cur regs rg _ 24%bv 24) by reflexivity; exact R24).
  all: assert (W25 : ew E 57 = w64 (dkeys + 8 * Z.of_nat i))
    by (change 57%nat with (xr 25); unfold E, xr; rewrite (te_cur regs rg _ 25%bv 25) by reflexivity; exact R25).
  all: assert (W21 : ew E 53 = w64 (shadow_addr bkeys + Z.of_nat i))
    by (change 53%nat with (xr 21); unfold E, xr; rewrite (te_cur regs rg _ 21%bv 21) by reflexivity; exact R21).
  all: assert (W22 : ew E 54 = w64 ((Z.of_nat (cm_at ms) - Z.of_nat i) mod 2 ^ 64))
    by (change 54%nat with (xr 22); unfold E, xr; rewrite (te_cur regs rg _ 22%bv 22) by reflexivity; exact R22).
  all: assert (Hsb : 0 <= shadow_addr bkeys + Z.of_nat i < 2 ^ 64)
    by (unfold shadow_addr, SHADOW_OFF; pose proof (Z.div_pos bkeys 8 ltac:(lia) ltac:(lia));
        assert (bkeys / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia); unfold n in *; lia).
  all: assert (Hm22 : 0 <= (Z.of_nat (cm_at ms) - Z.of_nat i) mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  all: lazymatch goal with
    | |- getr _ 10 = _ => rewrite Q10, E71
    | |- getr _ 11 = _ => rewrite Q11, E71
    | |- getr _ 12 = _ => rewrite Q12, W24
    | |- getr _ 25 = _ => rewrite Q25, W25
    | |- getr _ 21 = _ => rewrite Q21, W21
    | |- getr _ 22 = _ => rewrite Q22, W22
    | |- crt_spill _ _ CRT_SP_PN _ => unfold CRT_SP_PN; clsp HS 0%nat 41%nat X41; [clden E64 | unfold n in *; lia]
    | |- crt_spill _ _ CRT_SP_N _ => unfold CRT_SP_N; clsp HS 0%nat 41%nat X41; [clden E65 | unfold n in *; lia]
    end.
  all: try (unfold w64 at 1; rewrite unsigned_lit_small by (unfold n in *; lia); unfold w64; apply cl_zbv_mod;
    first [f_equal; lia | rewrite Z.mod_mod by lia; rewrite Z.add_mod_idemp_l by lia; f_equal; lia]).
Qed.
End L3t.

(* ---- L3r (+0x5c0): the property abort of new:754's strcmp half (`bnez a0`) is not taken (a0 = 0); at i = at the
   member's value is not compared (new:752 `i != at`, `beqz s6`) and the update follows; at i <> at the inline check
   of doc->kids (+0x728's report unreachable: doc's 56 bytes are addressable) and `same (&back.kids[i], &doc->kids[i])`
   at +0x5f0, whose two trees are ONE tree (pj_set_model keeps every member but at's: cm_set_member), so it answers 1 ---- *)
Section L3r.
Variable mb : nat.
Hypothesis KL3n : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i bkeys dkeys,
  (length ms - i < mb)%nat ->
  cl_at_L3 fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i bkeys dkeys ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk CRT_L3_OFF rg memc mdc) QFa.
Hypothesis KC : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg,
  cl_at_C fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk CRT_C_OFF rg memc mdc) QFa.

Lemma cl_L3r : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i bkeys dkeys,
  (length ms - i <= mb)%nat ->
  cl_at_L3r fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i bkeys dkeys ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk (CRT_CMP2_CALL + 4) rg memc mdc) QFa.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i bkeys dkeys Hmb (HC & R10).
destruct (Nat.eq_dec i (cm_at ms)) as [Ei | Ni].
{ exact (cl_L3_tail mb KL3n KC fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i bkeys dkeys
    (CRT_CMP2_CALL + 4) 0 Hmb HC R10 (or_introl (conj eq_refl (conj eq_refl Ei)))). }
pose proof HC as (HRW & HSP2 & HBR & Hi & Hbk & Hdk & R21 & R22 & R24 & R25 & SAT & SKSH & SP & SPN & SN & SBK & SBK2).
pose proof HRW as (Et & HFZ & HFK & HL & Hcs & Hcin & Hsv & Hcopy & Hback & Hd8 & Hrad & Hrab & Hrav & _).
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ).
pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPl.
pose proof (crt_live_frame HL) as HFRM.
pose proof (crt_live_memnorm HL) as HPM.
pose proof (crt_side_ledger HSD) as HLD.
pose proof (crt_side_arodata HSD) as HRO.
pose proof (crt_side_doc HSD) as HDOC.
pose proof (crt_side_doc_blocks HSD) as HDL.
pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkp & _).
pose proof (crt_bregs_sp HBR) as R2.
pose proof (crt_bregs_gp HBR) as R3.
pose proof (crt_bregs_tp HBR) as R4.
pose proof (crt_bregs_s0 HBR) as R8.
pose proof (crt_bregs_s1 HBR) as R9.
pose proof (crt_bregs_s2 HBR) as R18.
pose proof (crt_bregs_s4 HBR) as R20.
pose proof (crt_bregs_s3 HBR) as R19.
pose proof (crt_bregs_s7 HBR) as R23.
pose proof (crt_bregs_s10 HBR) as R26.
pose proof (crt_bregs_s11 HBR) as R27.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof YM05.alloc_ceiling_lt as Hc47.
pose proof cl_sp0 as (H16 & Hsp0 & H47). pose proof cl_sp1 as (Hs32 & Hs1).
assert (HSTKC : STKC = 27632) by (vm_compute; reflexivity).
pose proof cl_doc_low as (Hdl0 & Hdl1).
pose proof (cl_doc_F _ _ _ _ _ _ _ _ HJ) as HdF.
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc (crt_frame_listed HFRM))
  as (Fb1 & Fb2 & _).
change (fs_frame_bytes CRT_CID) with 512 in Fb2.
destruct (alx_frames SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc (crt_frame_listed HFRM))
  as (F32 & _).
set (F := frame_addr lyc CRT_CID pos) in *.
set (sp1 := CRT_sp1 (regs := regs)) in *.
rewrite Et in HDOC.
assert (Etc : tc = PjTree.JObj (PjTree.pj_set_model ms ck_MOD_AT (PjTree.JStr ck_STAMP))) by (unfold crt_tc; rewrite Et; reflexivity).
rewrite Etc in Hback.
destruct (cl_node_obj _ _ _ _ _ HDOC) as (dnum & dkids & dkeys' & dcap & Di & _ & _ & Hdh & Hdn & Hdc & _ & _).
pose proof Hdh as (_ & _ & _ & _ & VDK & _).
destruct (cl_node_obj _ _ _ _ _ Hback) as (bnum & bkids & bkeys' & bcap & Bi & _ & _ & Hbh & _ & _ & _ & _).
pose proof Hbh as (_ & _ & _ & _ & VBK & _).
assert (VBK' : rd_u64 SEGS (mrestrict (w_H Wc) memc) (F + 56) bkids)
  by (replace (F + 56) with (F + CRT_OFF_BACK + 24) by (unfold CRT_OFF_BACK; lia); exact VBK).
assert (HinL : forall bk, In bk (Dback ++ (saved, cap) :: Dc) -> In bk Lamc).
{ intros bk Hb. apply (Permutation_in _ (Permutation_sym HPl)). apply in_or_app. left. exact Hb. }
assert (HDb : forall bk, In bk Dback -> In bk Lamc) by (intros bk Hb; apply HinL; apply in_or_app; left; exact Hb).
assert (Hsv0 : 4096 <= saved < 2 ^ 47).
{ assert (Hin : In (saved, cap) Lamc) by (apply HinL; apply in_or_app; right; left; reflexivity).
  destruct (cl_blk_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLD Hin) as (Hk & Ha & Hb).
  change (@cf_head CfParams_preset) with 16 in Ha. lia. }
destruct (nth_error ms i) as [[nm u]|] eqn:Hnth; [|apply nth_error_None in Hnth; lia].
destruct (cm_set_member ms (PjTree.JStr ck_STAMP) i nm u Hnth) as (u' & Hnth' & Eu & _).
specialize (Eu Ni). subst u'.
destruct (cl_obj_key _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLD Hback HDb
  ltac:(replace (F + CRT_OFF_BACK + 32) with (F + CRT_OFF_BACK + PJ_OFF_KEYS) by (unfold PJ_OFF_KEYS; lia); exact Hbk) Hnth')
  as (bkp & bkb & Hbkp & _ & _ & _ & _ & Hbk4 & Hbk8 & Hbkc & _).
destruct (cl_obj_key _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLD HDOC HDL
  ltac:(replace (doc + 32) with (doc + PJ_OFF_KEYS) by (unfold PJ_OFF_KEYS; lia); exact Hdk) Hnth)
  as (dkp & dkb & Hdkp & _ & _ & _ & _ & Hdk4 & Hdk8 & Hdkc & _).
assert (Hlen : (length ms <= length (PjTree.pj_set_model ms ck_MOD_AT (PjTree.JStr ck_STAMP)))%nat)
  by (rewrite cm_set_len; destruct (Nat.eqb (cm_at ms) (length ms)); lia).
assert (Hnr : Z.of_nat (length ms) <= 2 ^ 54).
{ destruct Hdc as [(-> & _ & _) | (Hc0 & Hkd & _)]; [lia|].
  destruct (cl_blk_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLD Hkd) as (_ & Hb0 & Hb).
  change (@cf_head CfParams_preset) with 16 in Hb0. lia. }
set (n := Z.of_nat (length ms)) in *.
assert (Hat : (cm_at ms <= length ms)%nat) by apply cm_at_le.
pose proof VBK' as [Rbki _]. pose proof VDK as [Rdki _].
pose proof Hbk as [Rbk _]. pose proof Hdk as [Rdk _].
set (E := TE regs rg [w64 (n - Z.of_nat i); w64 (56 * Z.of_nat i); w64 saved; w64 (Z.of_nat (cm_at ms)); w64 doc;
  w64 bkids; w64 dkids; w64 (bkeys + 8 * Z.of_nat i)]).
assert (UA : U E (SOff 42 0) = 0).
{ change 42%nat with (xr 10). rewrite ts_U0. unfold E, xr. rewrite (te_cur regs rg _ 10%bv 10) by reflexivity. rewrite R10.
  reflexivity. }
assert (U22 : U E (SOff 54 0) = (Z.of_nat (cm_at ms) - Z.of_nat i) mod 2 ^ 64).
{ change 54%nat with (xr 22). rewrite ts_U0. unfold E, xr. rewrite (te_cur regs rg _ 22%bv 22) by reflexivity. rewrite R22.
  unfold w64. apply unsigned_lit_small. apply Z.mod_pos_bound. lia. }
assert (Hcs0 : conds_ok E [cl_cR_eq; cl_cR_nat]).
{ split; [unfold acond_ok, cl_cR_eq; cbn [ac_c ac_a ac_b]; change (xr 10) with 42%nat; rewrite branch_eq_U, UA, U_SLit;
    reflexivity|].
  split; [|exact I]. unfold acond_ok, cl_cR_nat; cbn [ac_c ac_a ac_b]. change (xr 22) with 54%nat.
  rewrite branch_ne_U, U22, U_SLit. apply negb_true_iff, Z.eqb_neq. intros H0.
  apply Z.mod_divide in H0; [|lia]. destruct H0 as [q Hq].
  assert (q = 0) by (unfold n in *; nia). subst q. apply Ni. lia. }
destruct (cl_L3x_entry fxk Wc memc rg (CRT_PC_A + (CRT_CMP2_CALL + 4)) _ (n - Z.of_nat i) (56 * Z.of_nat i) saved
  (Z.of_nat (cm_at ms)) F bkids dkids (bkeys + 8 * Z.of_nat i) Hcs0 R9 R26 R27 ltac:(lia) ltac:(lia) Hs32 ltac:(lia)
  ltac:(lia) Hd8 ltac:(lia) ltac:(lia) F32 HdF ltac:(unfold n in *; lia) ltac:(unfold n in *; lia) ltac:(lia) ltac:(lia)
  Rbki Rdki ltac:(unfold n in *; lia) ltac:(intros a Ha; apply Hstkp; lia) HSP2 SAT SKSH SP SBK SBK2 SPN SN VBK'
  ltac:(replace (doc + 24) with (doc + PJ_OFF_KIDS) by (unfold PJ_OFF_KIDS; lia); exact VDK)) as [HS SHOK].
fold E in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by apply te_env.
assert (W9 : ew E (xr 9) = w64 sp1) by (unfold E, xr; rewrite (te_cur regs rg _ 9%bv 9) by reflexivity; exact R9).
assert (X41 : bv_unsigned (ew E 41) = sp1) by (change 41%nat with (xr 9); rewrite W9; apply unsigned_lit_small; lia).
assert (HE2 : bv_unsigned (ew E 2) = sp0) by (unfold E; rewrite (te_entry regs rg _ 2%bv 2) by reflexivity; reflexivity).
pose (RUN := @crt_run_xw_inv fxk rc SK A_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (YSRrMemnorm.srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)) WS_HJ).
unfold crt_cfg.
paj_run_tok_x_inv RUN HS HJ SHOK HPM CL_SPAN.
- (* the inline check of doc->kids (+0x5c8; its report +0x728) *)
  cbn [ms_mem mkst restrict]. unfold CL_Bx. change (SOff (xr 26) 0) with (SOff 58 0).
  assert (E68 : ew E 68 = w64 doc) by exact (te_more_lt regs rg _ 4 ltac:(lia)).
  assert (W26 : ew E 58 = w64 SHADOW_OFF)
    by (change 58%nat with (xr 26); unfold E, xr; rewrite (te_cur regs rg _ 26%bv 26) by reflexivity; exact R26).
  rewrite (U_atom_off E 68 doc 24 E68) by lia. rewrite (U_atom E 58 SHADOW_OFF W26) by (unfold SHADOW_OFF; lia).
  apply (range_addressable_sub _ SHADOW_OFF doc 56 (doc + 24) 8 Hrad); lia.
- lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
  repeat (first [apply awr_ok_cons_ro; [cbn; lia|]
                | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ (xr 9) (sp1 - sp0));
                    [reflexivity | change (xr 9) with 41%nat; rewrite X41; lia | cbn; lia | cbn; lia |]]).
  apply awr_ok_nil.
- (* ---- at the call `same (&back.kids[i], &doc->kids[i])` (+0x5f0) ---- *)
  assert (Hav : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 80 <= a < sp1 + 96) ->
    aview SEGS (w_H Wc) (ms_mem ms0) a = aview SEGS (w_H Wc) memc a).
  { apply (ts_keep Wc _ _ memc (ms_mem ms0) _ HFr). intros a (r & Hri & Hr). vm_compute in Hri.
    repeat (destruct Hri as [<- | Hri]; [cbn [YP09.r_wlo YP09.r_whi YP09.r_base base_val] in Hr; rewrite ?X41 in Hr; lia |]);
      destruct Hri. }
  assert (Hpr : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) (ms_mem ms0) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  pose proof (cl_rw_keep _ _ _ _ _ memc (ms_mem ms0) _ _ _ _ _ _ _ _ _ _ _ _ _ (sp1 + 80) (sp1 + 96) HRW HJ HB_HJ
    ltac:(lia) ltac:(unfold CRT_SP_F; lia) Hav Hpr HPM) as HRW1.
  assert (KB : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
    getr (ms_regs ms0) r = getr rg r).
  { intros r Hr. unfold E in HS. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [clkeep HS |]). destruct Hr. }
  pose proof (cl_bregs_eq rg (ms_regs ms0) F HBR ltac:(intros r Hr; apply KB; cbv [In] in Hr |- *; tauto)) as HBR1.
  assert (K8 : forall off, 0 <= off -> off + 8 <= 80 -> forall a, sp1 + off <= a < sp1 + off + 8 ->
    aview SEGS (w_H Wc) (ms_mem ms0) a = aview SEGS (w_H Wc) memc a) by (intros off H0 H1 a Ha; apply Hav; lia).
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (1%bv : bv 5) Q1.
  lazymatch type of HS with st_ok _ ?E2 _ _ => set (EE := E2) in * end.
  assert (WE : forall k v, ew E k = w64 v -> (k < 240)%nat -> ew EE k = w64 v).
  { intros k v Hk Hlt. unfold EE. rewrite ?ew_ewset_other by lia. exact Hk. }
  assert (XE41 : bv_unsigned (ew EE 41) = sp1) by (unfold EE; rewrite ?ew_ewset_other by lia; exact X41).
  assert (E65 : ew E 65 = w64 (56 * Z.of_nat i)) by exact (te_more_lt regs rg _ 1 ltac:(lia)).
  assert (E69 : ew E 69 = w64 bkids) by exact (te_more_lt regs rg _ 5 ltac:(lia)).
  assert (E70 : ew E 70 = w64 dkids) by exact (te_more_lt regs rg _ 6 ltac:(lia)).
  assert (E64 : ew E 64 = w64 (n - Z.of_nat i)) by exact (te_more_lt regs rg _ 0 ltac:(lia)).
  assert (HE2' : bv_unsigned (ew EE 2) = sp0) by (unfold EE; rewrite ?ew_ewset_other by lia; exact HE2).
  (* the two member values: one tree u, over blocks of back's and of doc's *)
  pose proof HRW1 as (_ & _ & _ & HL1 & _ & _ & _ & _ & Hback1 & _).
  destruct (crt_live_journal HL1) as (WS_HJ1 & HJ1 & HB_HJ1). pose proof (crt_live_side HL1) as HSD1.
  pose proof (crt_side_ledger HSD1) as HLD1.
  pose proof (crt_side_doc HSD1) as HDOC1.
  pose proof (crt_side_doc_blocks HSD1) as HDL1.
  pose proof HJ1 as (HARc1 & _).
  rewrite Et in HDOC1. rewrite Etc in Hback1.
  destruct (cl_node_obj _ _ _ _ _ HDOC1) as (dnum1 & dkids1 & dkeys1 & dcap1 & Di1 & _ & _ & Hdh1 & Hdn1 & Hdc1 & EDi1 & Hdm1).
  destruct (cl_node_obj _ _ _ _ _ Hback1) as (bnum1 & bkids1 & bkeys1 & bcap1 & Bi1 & _ & _ & Hbh1 & Hbn1 & Hbc1 & EBi1 & Hbm1).
  assert (Hlow0 : forall z, 0 <= z < YM05.alloc_ceiling -> aview SEGS (w_H Wc) (ms_mem ms0) z = aview SEGS (w_H Wc) memc z)
    by (intros z Hz; apply Hav; lia).
  assert (Ebk : bkids1 = bkids).
  { pose proof Hbh1 as (_ & _ & _ & _ & [Q1' V1] & _). destruct VBK' as [Q2 V2].
    assert (V2' : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms0)) (F + 56) 8 bkids).
    { apply (ts_vm_av (w_H Wc) (w_H Wc) memc (ms_mem ms0)); [|exact V2]. intros j Hj. apply Hlow0. lia. }
    change (frame_addr lyc CRT_CID pos) with F in V1.
    replace (F + CRT_OFF_BACK + 24) with (F + 56) in V1 by (unfold CRT_OFF_BACK; lia).
    exact (cl_vm_det _ _ _ _ _ V1 V2' Q1' Q2). }
  assert (Edk : dkids1 = dkids).
  { pose proof Hdh1 as (_ & _ & _ & _ & [Q1' V1] & _). destruct VDK as [Q2 V2].
    assert (V2' : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms0)) (doc + 24) 8 dkids).
    { apply (ts_vm_av (w_H Wc) (w_H Wc) memc (ms_mem ms0)); [|exact V2]. intros j Hj. apply Hlow0. lia. }
    exact (cl_vm_det _ _ _ _ _ V1 V2' Q1' Q2). }
  subst bkids1 dkids1.
  assert (HinL1 : forall bk, In bk (Dback ++ (saved, cap) :: Dc) -> In bk Lamc).
  { intros bk Hb. apply (Permutation_in _ (Permutation_sym HPl)). apply in_or_app. left. exact Hb. }
  assert (HBi : forall bk, In bk Bi1 -> In bk Lamc).
  { intros bk Hb. apply HinL1. apply in_or_app. left. rewrite EBi1. apply in_or_app. right. exact Hb. }
  assert (HDi : forall bk, In bk Di1 -> In bk Lamc).
  { intros bk Hb. apply HDL1. rewrite EDi1. apply in_or_app. right. exact Hb. }
  destruct (cl_mems_nth _ _ _ _ _ _ _ _ _ _ Hbm1 Hnth') as (bkp1 & bkb1 & D1b & _ & _ & _ & HiB & Hub).
  destruct (cl_mems_nth _ _ _ _ _ _ _ _ _ _ Hdm1 Hnth) as (dkp1 & dkb1 & D1d & _ & _ & _ & HiD & Hud).
  destruct Hbc1 as [(Ec0 & _ & _) | (Hbc0 & Hbkl & _)]; [unfold n in *; lia|].
  destruct Hdc1 as [(Ec0 & _ & _) | (Hdc0 & Hdkl & _)]; [unfold n in *; lia|].
  unfold prh_lin in Hbkl, Hdkl.
  destruct (cl_hblk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc1 HLD1 Hbkl) as (_ & Hb16 & _ & Hbce & Hb4 & Hbbs & Hbhv & _).
  destruct (cl_hblk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc1 HLD1 Hdkl) as (_ & Hd16 & _ & Hdce & Hd4 & Hdbs & Hdhv & _).
  assert (Hlen1 : (length ms <= length (PjTree.pj_set_model ms ck_MOD_AT (PjTree.JStr ck_STAMP)))%nat) by exact Hlen.
  assert (Hpb : Z.of_nat (length (PjTree.pj_set_model ms ck_MOD_AT (PjTree.JStr ck_STAMP))) <= bcap1) by exact Hbn1.
  assert (Hpd : Z.of_nat (length ms) <= dcap1) by exact Hdn1.
  assert (HSTKs : 0 <= @STK_same prh_img_A DOC_D /\ @STK_same prh_img_A DOC_D + 240 <= STKC) by (vm_compute; split; discriminate).
  assert (Hsp1 : spZ (ms_regs ms0) = sp1).
  { unfold spZ. rewrite KB by (cbv [In]; tauto). rewrite R2. apply unsigned_lit_small. lia. }
  assert (Hceil : YM05.alloc_ceiling <= sp1 - @STK_same prh_img_A DOC_D) by lia.
  assert (HTa : PRH_FnEx.prhex_tree lyc Sc Lamc Wc (ms_regs ms0) (ms_mem ms0) (bkids + 56 * Z.of_nat i) u D1b).
  { refine (conj Hub (conj _ (conj _ _))).
    - left. exists bkids, (56 * bcap1). split; [exact Hbkl | unfold n in *; lia].
    - exact (block_shadow_range _ SHADOW_OFF bkids (56 * bcap1) (bkids + 56 * Z.of_nat i) 56 Hbbs ltac:(lia) ltac:(lia)).
    - apply (cl_hull_sub _ bkids (56 * bcap1)); [apply Hbhv; lia | lia | lia | lia | lia]. }
  assert (HTb : PRH_FnEx.prhex_tree lyc Sc Lamc Wc (ms_regs ms0) (ms_mem ms0) (dkids + 56 * Z.of_nat i) u D1d).
  { refine (conj Hud (conj _ (conj _ _))).
    - left. exists dkids, (56 * dcap1). split; [exact Hdkl | unfold n in *; lia].
    - exact (block_shadow_range _ SHADOW_OFF dkids (56 * dcap1) (dkids + 56 * Z.of_nat i) 56 Hdbs ltac:(lia) ltac:(lia)).
    - apply (cl_hull_sub _ dkids (56 * dcap1)); [apply Hdhv; lia | lia | lia | lia | lia]. }
  assert (HFa : forall z, PRH_Reader.pj_footR (bkids + 56 * Z.of_nat i) D1b z ->
    ~ (spZ (ms_regs ms0) - @STK_same prh_img_A DOC_D <= z < spZ (ms_regs ms0))).
  { intros z Hz. rewrite Hsp1.
    pose proof (cl_foot_low _ _ _ _ _ _ _ _ _ _ _ _ _ (bkids + 56 * Z.of_nat i) D1b z HARc1 HLD1
      (fun bk Hb => HBi bk (HiB bk Hb)) ltac:(lia) ltac:(unfold n in *; lia) Hz). lia. }
  assert (HFb : forall z, PRH_Reader.pj_footR (dkids + 56 * Z.of_nat i) D1d z ->
    ~ (spZ (ms_regs ms0) - @STK_same prh_img_A DOC_D <= z < spZ (ms_regs ms0))).
  { intros z Hz. rewrite Hsp1.
    pose proof (cl_foot_low _ _ _ _ _ _ _ _ _ _ _ _ _ (dkids + 56 * Z.of_nat i) D1d z HARc1 HLD1
      (fun bk Hb => HDi bk (HiD bk Hb)) ltac:(lia) ltac:(unfold n in *; lia) Hz). lia. }
  assert (Hdep : (PjTree.depth u <= DOC_D)%nat).
  { assert (Hd0 : (PjTree.depth (PjTree.JObj ms) <= PjGrammar.MAXD)%nat) by (rewrite <- Et; exact (cm_in_depth x t cl_in)).
    pose proof (cm_member_depth_nth ms i (nm, u) Hd0 Hi) as Hm. rewrite (nth_error_nth ms i (nm, u) Hnth) in Hm.
    cbn [snd] in Hm. lia. }
  assert (U65 : bv_unsigned (ew E 65) = 56 * Z.of_nat i) by (rewrite E65; apply unsigned_lit_small; unfold n in *; lia).
  assert (U69 : bv_unsigned (ew E 69) = bkids) by (rewrite E69; apply unsigned_lit_small; lia).
  assert (U70 : bv_unsigned (ew E 70) = dkids) by (rewrite E70; apply unsigned_lit_small; lia).
  assert (X10 : getr (ms_regs ms0) 10 = w64 (bkids + 56 * Z.of_nat i)).
  { rewrite Q10, (cl_add_w _ _ (56 * Z.of_nat i) bkids U65 U69) by (unfold n in *; lia). f_equal. lia. }
  assert (X11 : getr (ms_regs ms0) 11 = w64 (dkids + 56 * Z.of_nat i)).
  { rewrite Q11, (cl_add_w _ _ (56 * Z.of_nat i) dkids U65 U70) by (unfold n in *; lia). f_equal. lia. }
  assert (X1 : getr (ms_regs ms0) 1 = Z_to_bv 64 (BASE + (CRT_PC_A + (CRT_SAME_CALL + 4))))
    by (rewrite Q1; vm_compute; reflexivity).
  (* the spills at the call (the run rewrote 0x50 / 0x58 with their old values) *)
  pose proof (cl_pi_of_ok _ _ _ _ HS) as HSpi.
  assert (SPN0 : crt_spill (regs := regs) Wc (ms_mem ms0) CRT_SP_PN (n - Z.of_nat i)).
  { unfold CRT_SP_PN. clsp HSpi 0%nat 41%nat XE41; [clden (WE 64%nat _ E64 ltac:(lia)) | unfold n in *; lia]. }
  assert (SN0 : crt_spill (regs := regs) Wc (ms_mem ms0) CRT_SP_N (56 * Z.of_nat i)).
  { unfold CRT_SP_N. clsp HSpi 0%nat 41%nat XE41; [clden (WE 65%nat _ E65 ltac:(lia)) | unfold n in *; lia]. }
  clear HSpi.
  destruct HSP2 as (SBKs & SSVs).
  assert (S0 : forall off v, 0 <= off -> off + 8 <= 80 -> crt_spill (regs := regs) Wc memc off v ->
    crt_spill (regs := regs) Wc (ms_mem ms0) off v)
    by (intros off v H0 H1 Hsp; exact (cl_spill_keep8 Wc memc (ms_mem ms0) off v (K8 off H0 H1) Hsp)).
  (* the root pa = back's kid i lies in back's kids block, below alloc_ceiling <= sp1 - STK_same DOC_D: the guard of
     same's stack-presence premise is false at this call *)
  assert (Hpa : bkids + 56 * Z.of_nat i < spZ (ms_regs ms0)) by (rewrite Hsp1; unfold n in *; lia).
  clear HF HFr HG.
  apply (cl_same_call fxk Wc _ _ ms0 _ lyc Sc Hpc _ pos _ Lamc peakc _ (CRT_SAME_CALL + 4) _ _ u u D1b D1d HFZ HS
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HE2' HL1 HBR1 X1 ltac:(unfold CRT_SAME_CALL; lia)
    ltac:(unfold CRT_SAME_CALL; lia) X10 X11 Hpa HTa HTb Hdep HFa HFb).
  intros fx' ly2 W2 regs2 mem2 md2 k1 HFZ2 HFK2 HJe HJc HP Hres Eab HLED2 HMNk.
  destruct (crt102rw_call_keep LAWS HPRE _ _ _ _ _ _ _ pos _ [] ly2 Sc Hpc W2 mem2 md2 k1 HJ1 HJc
    (fun a Hf => False_ind _ (inFP_nil a Hf))) as (EF & KS & _).
  assert (X10' : getr regs2 10 = w64 1) by (destruct Hres as [(_ & H1) | (Hne & _)]; [exact H1 | exfalso; exact (Hne eq_refl)]).
  pose proof (cl_rw_call0 fxk lyc Sc Hpc Wc (ms_mem ms0) _ _ pos Dc Lamc peakc cset saved cap Dback ms fx'
    (@STK_same prh_img_A DOC_D) ly2 W2 mem2 md2 k1 HRW1 HJe HJc (proj1 HSTKs) HFZ2 HFK2 HLED2 Eab HMNk) as HRW2.
  assert (SK2 : forall off v, 0 <= off -> off + 8 <= 240 -> crt_spill (regs := regs) Wc (ms_mem ms0) off v ->
    crt_spill (regs := regs) W2 mem2 off v)
    by (intros off v H0 H1 Hsp; exact (crt102rw_spill_keep HPRE Wc W2 (ms_mem ms0) mem2 off v KS H0 H1 Hsp)).
  pose proof HTREE as (_ & _ & _ & (_ & (cid & pos' & Hfin & Hfa1 & Hfa2) & _)).
  pose proof HPRE as ((HAR0 & _) & _).
  pose proof HJ1 as (_ & HLYc & _ & _ & _ & HFRc & _).
  destruct (alx_layout SEGS B ARx LAWS ly S Hp W mem md lyc HAR0 HLYc) as (_ & Efa & _).
  assert (Hfin' : In (cid, pos') (frames Sc)) by (rewrite HFRc; apply in_or_app; right; exact Hfin).
  rewrite <- (Efa cid pos') in Hfa1, Hfa2.
  assert (Hrd2 : forall a v, rd_u64 SEGS (mrestrict (w_H Wc) memc) a v -> a + 8 <= YM05.alloc_ceiling -> 0 <= a ->
    rd_u64 SEGS (mrestrict (w_H Wc) (ms_mem ms0)) a v).
  { intros a v [Rv Vv] Ha0 Ha1. split; [exact Rv|]. apply (ts_vm_av (w_H Wc) (w_H Wc) memc (ms_mem ms0)); [|exact Vv].
    intros j Hj. apply Hlow0. lia. }
  refine (cl_L3_tail mb KL3n KC fx' ly2 Sc Hpc W2 mem2 md2 _ pos Dc Lamc peakc cset saved cap Dback ms regs2 i bkeys dkeys
    (CRT_SAME_CALL + 4) 1 Hmb _ X10' (or_intror (conj eq_refl eq_refl))).
  unfold CRT_SP_AT, CL_SP_KSH, CL_SP_P, CRT_SP_PN, CRT_SP_N, CRT_SP_BACK, CRT_SP_SAVED, CL_SP_BK, CL_SP_BK2 in *.
  unfold cl_l3core. rewrite EF.
  refine (conj HRW2 (conj (conj _ _) (conj _ (conj Hi (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
    (conj _ (conj _ (conj _ (conj _ _)))))))))))))))).
  + exact (SK2 56 _ ltac:(lia) ltac:(lia) (S0 56 _ ltac:(lia) ltac:(lia) SBKs)).
  + exact (SK2 24 _ ltac:(lia) ltac:(lia) (S0 24 _ ltac:(lia) ltac:(lia) SSVs)).
  + exact (cl_bregs_eq _ regs2 F HBR1 ltac:(intros r Hr; apply (cl_cs_keep _ _ HP); cbv [In] in Hr |- *; tauto)).
  + apply (cl_rd_frame_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ CRT_CID pos _ _ HJc (crt_frame_listed HFRM));
      [unfold CRT_OFF_BACK, PJ_OFF_KEYS; lia | change (fs_frame_bytes CRT_CID) with 512; unfold CRT_OFF_BACK, PJ_OFF_KEYS; lia |].
    exact (Hrd2 _ _ Hbk ltac:(unfold CRT_OFF_BACK, PJ_OFF_KEYS; lia) ltac:(unfold CRT_OFF_BACK, PJ_OFF_KEYS; lia)).
  + apply (cl_rd_frame_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ cid pos' _ _ HJc Hfin'); [unfold PJ_OFF_KEYS; lia | unfold PJ_OFF_KEYS; lia |].
    exact (Hrd2 _ _ Hdk ltac:(unfold PJ_OFF_KEYS; lia) ltac:(unfold PJ_OFF_KEYS; lia)).
  + rewrite (cl_cs_keep _ _ HP 21%bv) by (cbv [In]; tauto). rewrite KB by (cbv [In]; tauto). exact R21.
  + rewrite (cl_cs_keep _ _ HP 22%bv) by (cbv [In]; tauto). rewrite KB by (cbv [In]; tauto). exact R22.
  + rewrite (cl_cs_keep _ _ HP 24%bv) by (cbv [In]; tauto). rewrite KB by (cbv [In]; tauto). exact R24.
  + rewrite (cl_cs_keep _ _ HP 25%bv) by (cbv [In]; tauto). rewrite KB by (cbv [In]; tauto). exact R25.
  + exact (SK2 32 _ ltac:(lia) ltac:(lia) (S0 32 _ ltac:(lia) ltac:(lia) SAT)).
  + exact (SK2 40 _ ltac:(lia) ltac:(lia) (S0 40 _ ltac:(lia) ltac:(lia) SKSH)).
  + exact (SK2 48 _ ltac:(lia) ltac:(lia) (S0 48 _ ltac:(lia) ltac:(lia) SP)).
  + exact (SK2 80 _ ltac:(lia) ltac:(lia) SPN0).
  + exact (SK2 88 _ ltac:(lia) ltac:(lia) SN0).
  + exact (SK2 64 _ ltac:(lia) ltac:(lia) (S0 64 _ ltac:(lia) ltac:(lia) SBK)).
  + exact (SK2 72 _ ltac:(lia) ltac:(lia) (S0 72 _ ltac:(lia) ltac:(lia) SBK2)).
Qed.
End L3r.

(* ---- THE MEMBER LOOP CLOSED BY THE MEASURE length ms - i: each iteration leaves for C or re-enters L3 at i + 1 ---- *)
Section L3loop.
Hypothesis KC : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg,
  cl_at_C fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk CRT_C_OFF rg memc mdc) QFa.
Lemma cl_L3_loop : forall mb fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i bkeys dkeys,
  (length ms - i <= mb)%nat ->
  cl_at_L3 fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i bkeys dkeys ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk CRT_L3_OFF rg memc mdc) QFa.
Proof.
induction mb as [|mb IH];
  intros fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i bkeys dkeys Hmb HL3.
- exfalso. destruct HL3 as (_ & _ & _ & Hi & _). lia.
- apply (cl_L3_head (Datatypes.S mb)
    (fun fxk' lyc' Sc' Hpc' Wc' memc' mdc' kj' pos' Dc' Lamc' peakc' cset' saved' cap' Dback' ms' rg' i' bk' dk' Hm' H' =>
       cl_L3r (Datatypes.S mb)
         (fun fxk'' lyc'' Sc'' Hpc'' Wc'' memc'' mdc'' kj'' pos'' Dc'' Lamc'' peakc'' cset'' saved'' cap'' Dback'' ms'' rg''
              i'' bk'' dk'' Hlt H'' =>
            IH fxk'' lyc'' Sc'' Hpc'' Wc'' memc'' mdc'' kj'' pos'' Dc'' Lamc'' peakc'' cset'' saved'' cap'' Dback'' ms''
              rg'' i'' bk'' dk'' ltac:(lia) H'')
         KC fxk' lyc' Sc' Hpc' Wc' memc' mdc' kj' pos' Dc' Lamc' peakc' cset' saved' cap' Dback' ms' rg' i' bk' dk' Hm' H')
    fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg i bkeys dkeys Hmb HL3).
Qed.
End L3loop.

(* ======================================================================================================== *)
(* C (+0x634): THE THREE FINAL CHECKS (new:759-764) and THE EXIT (+0x6cc .. +0x6dc). C reads back.keys[at] and
   compares it with MOD_AT (strcmp at +0x664, `bnez a0` -> +0x6f8: the property abort of new:759's first half), reads
   back.kids[at].type (`bne a1, 4` at +0x710 -> +0x6f8: new:759's second half) and compares back.kids[at].str with STAMP
   (strcmp at +0x6c4, `bnez a0` -> +0x6f8: new:764). Crt102Model.cm_set_at: the member of the rewritten tree at
   `at` is (MOD_AT, JStr STAMP), so all three are not taken. The exit frees saved (fuzz_free, +0x6d0) and back
   (pj_free, +0x6d8), sets s6 = 0 and jumps to X (+0x304). *)

(* ---- the exit's helpers: a block's footprint, apartness through the ledger's NoDup heads, the two position steps ---- *)
(* a byte of a freed block's footprint: the block of Dt it lies in (Crt102Rewrite.v's crt102rw_fp_hull, restated:
   that file is not on this slice's Require path) *)
Lemma cl_fp_hull : forall Dt a0, inFP (ablocks_fp (PRH_FnPj.prhPj_hbl Dt)) a0 ->
  exists bb kb, In (bb, kb) Dt /\ bb - cf_head <= a0 < bb - cf_head + req_size (kb + cf_head).
Proof.
intros Dt a0 ((b & e) & Hb & Hab). unfold ablocks_fp, PRH_FnPj.prhPj_hbl in Hb.
rewrite map_map, in_map_iff in Hb. destruct Hb as ((bb & kb) & Eb & Hbb). cbn [fst snd] in Eb. injection Eb as <- <-.
exists bb, kb. split; [exact Hbb|]. try unfold in_zr in Hab. cbn [fst snd] in Hab.
assert (Eh : @cf_head CfParams_preset = 16) by reflexivity. rewrite Eh. lia.
Qed.
(* two parts of a duplicate-free list share no member (Stdlib's List.NoDup) *)
Lemma cl_nodup_app : forall (l1 l2 : list Z) a, List.NoDup (l1 ++ l2) -> In a l1 -> ~ In a l2.
Proof.
induction l1 as [|b l1 IH]; intros l2 a Hn H1 H2; [destruct H1|]. cbn in Hn. inversion Hn as [|? ? Hb Hn']; subst.
destruct H1 as [<- | H1]; [apply Hb; apply in_or_app; right; exact H2 | exact (IH l2 a Hn' H1 H2)].
Qed.
(* the walk's three block lists are apart, by the ledger's NoDup heads (stdpp's NoDup, passed to Stdlib's by
   NoDup_ListNoDup as S1Ledger.v does) *)
Lemma cl_nodup_mid : forall (Lamc A B' L : list (Z * Z)) x, NoDup (map fst Lamc) ->
  Permutation Lamc ((A ++ x :: B') ++ L) ->
  ~ In x A /\ ~ In x B' /\ (forall y, In y A -> ~ In y B').
Proof.
intros Lamc A B' L [a k] Hnd HP. apply NoDup_ListNoDup in Hnd.
pose proof (Permutation_NoDup (Permutation_map fst HP) Hnd) as Hn.
rewrite !map_app in Hn. cbn [map fst] in Hn. rewrite <- app_assoc in Hn.
pose proof (NoDup_remove_2 _ _ _ Hn) as Hb. pose proof (NoDup_remove_1 _ _ _ Hn) as Hn1.
split; [|split].
- intros Hx. apply Hb. apply in_or_app. left. exact (in_map fst _ _ Hx).
- intros Hx. apply Hb. apply in_or_app. right. apply in_or_app. left. exact (in_map fst _ _ Hx).
- intros y HyA HyB. apply (cl_nodup_app _ _ (fst y) Hn1 (in_map fst _ _ HyA)).
  apply in_or_app. left. exact (in_map fst _ _ HyB).
Qed.
(* a byte of a block of Dx is outside the footprint of a tree of the class-3 frame over blocks other than that one *)
Lemma cl_hull_off_tree : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc bb kb y off Dt,
  livea lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc -> In (bb, kb) Lamc -> ~ In (bb, kb) Dt ->
  (forall b, In b Dt -> In b Lamc) -> 0 <= off -> off + 56 <= 512 ->
  bb - cf_head <= y < bb - cf_head + req_size (kb + cf_head) -> ~ pj_footR (frame_addr lyc CRT_CID pos + off) Dt y.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc bb kb y off Dt HL HbL HnD HDt Ho0 Ho1 Hy.
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ).
pose proof (crt_side_ledger (crt_live_side HL)) as HLDc.
pose proof HJ as (HARc & _).
pose proof (crt_frame_listed (crt_live_frame HL)) as Hin.
destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc bb kb _ _ HLDc HbL) as (Hk0 & Hab & _).
intros [Hf | ((b & kb2) & Hb2 & Hf)].
- pose proof (sep_block_frame_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ CRT_CID pos HARc Hab Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes CRT_CID) with 512 in Hd. lia.
- destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc b kb2 _ _ HLDc (HDt _ Hb2)) as (Hk2 & Hab2 & _).
  assert (Hne : (bb - cf_head, kb + cf_head) <> (b - cf_head, kb2 + cf_head)).
  { intros E. injection E as E1 E2. assert (bb = b) by lia. assert (kb = kb2) by lia. subst. exact (HnD Hb2). }
  pose proof (sep_blocks_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ _ _ HARc Hab Hab2 Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. unfold pj_holdsR in Hf. cbn [fst snd] in Hf.
  change (@cf_head CfParams_preset) with 16 in *. pose proof (req_size_pos (kb2 + 16) ltac:(lia)).
  assert (kb2 + 16 <= req_size (kb2 + 16)) by (unfold req_size; destruct (Z.eqb_spec (kb2 + 16) 0); lia). lia.
Qed.
(* a byte of a block of Dx: below the ceiling, application memory, outside the class-3 frame *)
Lemma cl_hull_app : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc bb kb y,
  livea lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc -> In (bb, kb) Lamc ->
  bb - cf_head <= y < bb - cf_head + req_size (kb + cf_head) ->
  4096 <= y < YM05.alloc_ceiling /\ in_app y 1 /\
  ~ (frame_addr lyc CRT_CID pos <= y < frame_addr lyc CRT_CID pos + 512).
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc bb kb y HL HbL Hy.
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ).
pose proof (crt_side_ledger (crt_live_side HL)) as HLDc.
pose proof HJ as (HARc & _).
pose proof (crt_frame_listed (crt_live_frame HL)) as Hin.
destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc bb kb _ _ HLDc HbL) as (Hk0 & Hab & _).
destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hab) as (_ & B4096 & Bce & Bapp & _).
pose proof (sep_block_frame_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ CRT_CID pos HARc Hab Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes CRT_CID) with 512 in Hd.
change (@cf_head CfParams_preset) with 16 in *.
pose proof (req_size_pos (kb + 16) ltac:(lia)).
split; [lia|]. split; [apply (in_app_sub _ _ _ _ Bapp); lia | lia].
Qed.

(* a byte of a block of Dx is outside the document's footprint (Crt102Rewrite.v's crt102rw_hull_off_doc, restated) *)
Lemma cl_hull_off_doc : forall lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc bb kb y,
  livea lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc -> In (bb, kb) Dx ->
  bb - cf_head <= y < bb - cf_head + req_size (kb + cf_head) -> ~ pj_footR doc D y.
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc bb kb y HL Hb Hy.
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ).
pose proof (crt_side_ledger (crt_live_side HL)) as HLDc.
pose proof (crt_side_doc_blocks (crt_live_side HL)) as HDL.
pose proof (crt_live_lam_perm HL) as HPL.
pose proof (crt_live_dx_apart HL) as HAP.
pose proof HJ as (HARc & HLYc & _ & _ & _ & HFRc & _).
pose proof HPRE as ((HAR & _) & _).
pose proof HTREE as (_ & _ & _ & _ & (cid & pos' & Hfin & Hfa1 & Hfa2) & _).
destruct (alx_layout SEGS B ARx LAWS ly S Hp W mem md lyc HAR HLYc) as (_ & Efa & _).
assert (HbL : In (bb, kb) Lamc) by (apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app; left; exact Hb).
destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc bb kb _ _ HLDc HbL) as (Hk0 & Hab & _).
intros [Hf | ((b & kb2) & Hb2 & Hf)].
- assert (Hfin' : In (cid, pos') (frames Sc)) by (rewrite HFRc; apply in_or_app; right; exact Hfin).
  pose proof (sep_block_frame_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ cid pos' HARc Hab Hfin') as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite (Efa cid pos') in Hd. lia.
- destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc b kb2 _ _ HLDc (HDL _ Hb2)) as (Hk2 & Hab2 & _).
  assert (Hne : (bb - cf_head, kb + cf_head) <> (b - cf_head, kb2 + cf_head)).
  { intros E. injection E as E1 E2. assert (bb = b) by lia. assert (kb = kb2) by lia. subst.
    exact (HAP _ Hb Hb2). }
  pose proof (sep_blocks_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ _ _ HARc Hab Hab2 Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. unfold pj_holdsR in Hf. cbn [fst snd] in Hf.
  change (@cf_head CfParams_preset) with 16 in *. pose proof (req_size_pos (kb2 + 16) ltac:(lia)).
  assert (kb2 + 16 <= req_size (kb2 + 16)) by (unfold req_size; destruct (Z.eqb_spec (kb2 + 16) 0); lia). lia.
Qed.
(* ---- the room position across fuzz_free (saved): crt_evs_L0's first event is pj_write's buffer's free, HFr of the
   last capacity plus the head (PresetReqAt.w_free); the text's transfer advances by it ---- *)
Lemma cl_pos_ff : forall Sc S2 ms cap,
  posa Sc (crt_evs_L0 ms) -> cap = last (PresetReqAt.wcaps (PresetReqAt.copy_set ms) true) 0 ->
  (forall (sm : list Z -> Z * Z) (xs : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm xs os i H0 hist Sc ->
     PRH_Base.prh_run_at sm xs os i [PresetReqAt.HFr (cap + cf_head)] ->
     exists hist', PresetRoomPos.iface_room_pos sm xs os (i + length [PresetReqAt.HFr (cap + cf_head)])%nat H0 hist' S2) ->
  posa S2 ([PresetReqAt.HBulk (PresetReqAt.fo (PresetReqAt.copy_set ms))] ++
           [PresetReqAt.HBulk (PresetReqAt.fo (PresetReqAt.copy_set ms))]).
Proof.
intros Sc S2 ms cap HP Ecap HTR.
destruct HP as [Hsm (pre & hist & HA)]. destruct HA as [Hsplit Hroom Hrun Hcons].
unfold crt_evs_L0, PresetReqAt.w_free in *. rewrite <- Ecap in *.
assert (EH : PresetReqAt.HEAD = @cf_head CfParams_preset) by reflexivity. rewrite EH in *.
change ([PresetReqAt.HFr (cap + cf_head)] ++ ([PresetReqAt.HBulk (PresetReqAt.fo (PresetReqAt.copy_set ms))] ++
  [PresetReqAt.HBulk (PresetReqAt.fo (PresetReqAt.copy_set ms))])) with
  ([PresetReqAt.HFr (cap + cf_head)] ++ [PresetReqAt.HBulk (PresetReqAt.fo (PresetReqAt.copy_set ms));
   PresetReqAt.HBulk (PresetReqAt.fo (PresetReqAt.copy_set ms))]) in *.
apply PRH_Base.prh_run_at_app_iff in Hrun as [Hr1 Hr2].
destruct (HTR _ _ _ _ _ _ Hroom Hr1) as (hist' & Hroom').
rewrite length_app in Hcons. cbn [length] in Hroom', Hr2, Hcons.
constructor; [exact Hsm|]. exists (pre ++ [PresetReqAt.HFr (cap + cf_head)]), hist'. constructor.
- rewrite Hsplit, <- app_assoc. reflexivity.
- rewrite length_app. cbn [length]. replace (rp_i + (length pre + 1))%nat with (rp_i + length pre + 1)%nat by lia.
  exact Hroom'.
- rewrite length_app. cbn [length]. replace (rp_i + (length pre + 1))%nat with (rp_i + length pre + 1)%nat by lia.
  exact Hr2.
- rewrite length_app. cbn [length]. replace (rp_i + (length pre + 1))%nat with (rp_i + length pre + 1)%nat by lia.
  apply PRH_Base.prh_cons_from_app_iff in Hcons as [_ Hc2]. exact Hc2.
Qed.
(* ---- the room position across pj_free (&back): one bulk free of back's order list, the model's HBulk (fo tc); an
   empty list makes no event and the model's HBulk [] is stepped over (prhPj_bulk_nil_pos) ---- *)
Lemma cl_pos_pjf : forall S2 S3 L E2 (Fb : list (Z * Z)),
  posa S2 ([PresetReqAt.HBulk L] ++ E2) -> map (fun b => snd b + cf_head) Fb = L ->
  (forall (sm : list Z -> Z * Z) (xs : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm xs os i H0 hist S2 ->
     PRH_Base.prh_run_at sm xs os i (PRH_FnPj.prhPj_free_evs Fb) ->
     exists hist', PresetRoomPos.iface_room_pos sm xs os (i + length (PRH_FnPj.prhPj_free_evs Fb))%nat H0 hist' S3) ->
  posa S3 E2.
Proof.
intros S2 S3 L E2 Fb HP EL HTR.
destruct HP as [Hsm (pre & hist & HA)]. destruct HA as [Hsplit Hroom Hrun Hcons].
apply PRH_Base.prh_run_at_app_iff in Hrun as [Hr1 Hr2]. rewrite length_app in Hcons. cbn [length] in Hr2, Hcons.
apply PRH_Base.prh_cons_from_app_iff in Hcons as [_ Hc2].
assert (Hroom3 : exists h3, PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + length pre + 1)%nat rp_H0 h3 S3).
{ destruct Fb as [|b Fb'].
  - cbn [map] in EL. subst L.
    destruct (HTR _ _ _ _ _ _ Hroom (PRH_FnPj.prhPj_free_evs_nil rp_sm rp_x rp_os _)) as (h' & Hh').
    cbn [PRH_FnPj.prhPj_free_evs length] in Hh'. rewrite Nat.add_0_r in Hh'.
    apply (proj1 (PRH_Base.prh_run_at_one rp_sm rp_x rp_os _ _)) in Hr1.
    exists h'. replace (rp_i + length pre + 1)%nat with (Datatypes.S (rp_i + length pre)) by lia.
    exact (proj1 (PRH_FnPj.prhPj_bulk_nil_pos rp_sm rp_x rp_os _ rp_H0 h' S3 Hr1) Hh').
  - assert (Ev : PRH_FnPj.prhPj_free_evs (b :: Fb') = [PresetReqAt.HBulk L]) by (cbn [PRH_FnPj.prhPj_free_evs]; rewrite EL; reflexivity).
    rewrite Ev in HTR. destruct (HTR _ _ _ _ _ _ Hroom Hr1) as (h' & Hh'). exists h'. exact Hh'. }
destruct Hroom3 as (h3 & Hroom3).
constructor; [exact Hsm|]. exists (pre ++ [PresetReqAt.HBulk L]), h3. constructor.
- rewrite Hsplit, <- app_assoc. reflexivity.
- rewrite length_app. cbn [length]. replace (rp_i + (length pre + 1))%nat with (rp_i + length pre + 1)%nat by lia.
  exact Hroom3.
- rewrite length_app. cbn [length]. replace (rp_i + (length pre + 1))%nat with (rp_i + length pre + 1)%nat by lia.
  exact Hr2.
- rewrite length_app. cbn [length]. replace (rp_i + (length pre + 1))%nat with (rp_i + length pre + 1)%nat by lia.
  exact Hc2.
Qed.

(* the STAMP literal, as the run leaves it (auipc / addi: A_OBJ 2 plus its offset) *)
Lemma cl_stamp_den : forall E, ew E 243 = Z_to_bv 64 (VAL 243) ->
  sv_denot E (SOff 243 70528) = Z_to_bv 64 CRT_STAMP_A.
Proof. intros E HE. apply bv_eq. rewrite denot_SOff, HE. vm_compute. reflexivity. Qed.

(* `slli x, 3` in the form prreg leaves (alu64 over the word) *)
Lemma cl_sll3_w : forall (w : word) a, bv_unsigned w = a -> 0 <= a < 2 ^ 61 ->
  alu64 ALU_SLL w (Z_to_bv 64 3) = w64 (8 * a).
Proof.
intros w a H Ha. rewrite (ts_alu_w64 ALU_SLL w (Z_to_bv 64 3) a 3 H) by (apply unsigned_lit_small; lia). f_equal.
unfold zalu64. rewrite (YP0m.zcanon_small a), (YP0m.zcanon_small 3) by lia. cbn [zalu_raw].
change (Z.land 3 63) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
rewrite Z.mul_comm. apply YP0m.zcanon_small. lia.
Qed.
(* the 64-bit wrap of a three-term sum, from its canonical parts *)
Lemma cl_mod3 : forall a b c, ((a mod 2 ^ 64 + b mod 2 ^ 64) mod 2 ^ 64 + c) mod 2 ^ 64 = (a + b + c) mod 2 ^ 64.
Proof.
intros a b c. rewrite Z.add_mod_idemp_l by lia. rewrite (Z.add_comm (a mod 2 ^ 64) (b mod 2 ^ 64)).
rewrite <- Z.add_assoc, Z.add_mod_idemp_l by lia. rewrite Z.add_assoc, (Z.add_comm b), <- Z.add_assoc.
rewrite Z.add_mod_idemp_l by lia. rewrite Z.add_assoc. reflexivity.
Qed.
(* the run's `slli` / `add` address of &back.keys[at] *)
Lemma cl_U_k8 : forall E a b, 0 <= U E b < 2 ^ 61 -> U E a + 8 * U E b < 2 ^ 64 ->
  U E (SAlu ALU_ADD a (SAlu ALU_SLL b (SLit 3))) = U E a + 8 * U E b.
Proof.
intros E a b Hb Hab. pose proof (U_range E a) as Ra. unfold M64 in Ra.
rewrite !U_SAlu, U_SLit. cbn [zalu_raw]. unfold zcanon, M64.
change (3 mod 2 ^ 64) with 3. change (Z.land 3 63) with 3. rewrite Z.shiftl_mul_pow2 by lia.
change (2 ^ 3) with 8. rewrite (Z.mod_small (U E b * 8)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
(* the run's `slli` / `sub` / `add` address of &back.kids[at] (s5 = 8 at survives the strcmp) *)
Lemma cl_U_kid : forall E k8 ka kk, U E k8 = 8 * U E ka -> U E ka < 2 ^ 54 -> U E kk + 56 * U E ka < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL k8 (SLit (2 ^ 64 - 1))) (SAlu ALU_SLL ka (SLit 6))) kk) =
  U E kk + 56 * U E ka.
Proof.
intros E k8 ka kk H8 Ha Hk. pose proof (U_range E ka) as Ra. pose proof (U_range E kk) as Rk. unfold M64 in *.
rewrite !U_SAlu, U_SMd, !U_SLit. cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
change ((2 ^ 64 - 1) mod 2 ^ 64) with (2 ^ 64 - 1). change (6 mod 2 ^ 64) with 6. change (Z.land 6 63) with 6.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 6) with 64. rewrite H8.
rewrite cl_mod3.
replace (8 * U E ka * (2 ^ 64 - 1) + U E ka * 64 + U E kk) with (U E kk + 56 * U E ka + (8 * U E ka) * 2 ^ 64) by ring.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(* ---- C's entry state (extras: 64 = saved, 65 = at, 66 = back.kids, 67 = back.keys, 68 = &back.keys[at],
   69 = back.keys[at]); the run reads 0x18 / 0x20 / 0x38 (s1), back's header, the key slot; it writes nothing ---- *)
Definition ss_C : sstate := mkSS (CRT_PC_A + CRT_C_OFF) cur_atoms
  [ YP09.mkRegion (Some (xr 9)) 24 64 0 0
      [YP09.mkChunk 24 (CVal 8 (SOff 64 0)); YP09.mkChunk 32 (CVal 8 (SOff 65 0)); YP09.mkChunk 56 (CVal 8 (SOff (xr 27) 32))];
    YP09.mkRegion (Some (xr 27)) 56 72 0 0 [YP09.mkChunk 56 (CVal 8 (SOff 66 0)); YP09.mkChunk 64 (CVal 8 (SOff 67 0))];
    YP09.mkRegion (Some 68%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 69 0))] ]
  None
  (mkFacts [(xr 9, mkAF (2 ^ 46) (2 ^ 47) 5); (xr 26, mkAF SHADOW_OFF SHADOW_OFF 0); (xr 27, mkAF 4096 (2 ^ 47 - 512) 5);
            (68%nat, mkAF 4096 (2 ^ 47 - 8) 3)] []
    [(SAlu ALU_ADD (SOff 67 0) (SAlu ALU_SLL (SOff 65 0) (SLit 3)), SOff 68 0)]).

Lemma cl_C_entry : forall (fxk : YK11.FPState) (Wc : world SEGS) memc rg saved atv F bkids bkeys bki,
  getr rg 9 = w64 (CRT_sp1 (regs := regs)) -> getr rg 26 = w64 SHADOW_OFF -> getr rg 27 = w64 F ->
  2 ^ 46 <= CRT_sp1 (regs := regs) -> CRT_sp1 (regs := regs) + 96 <= 2 ^ 47 -> CRT_sp1 (regs := regs) mod 32 = 0 ->
  4096 <= F -> F + 512 <= CRT_sp1 (regs := regs) -> F mod 32 = 0 ->
  4096 <= bkeys -> bkeys mod 8 = 0 -> bkeys + 8 * atv + 8 <= CRT_sp1 (regs := regs) -> 0 <= atv < 2 ^ 54 ->
  (bkeys + 8 * atv + 8 <= F \/ F + 512 <= bkeys + 8 * atv) ->
  0 <= saved < 2 ^ 64 -> 0 <= bkids < 2 ^ 64 -> 0 <= bki < 2 ^ 64 ->
  cl_sp2 Wc memc F saved -> crt_spill (regs := regs) Wc memc CRT_SP_AT atv ->
  rd_u64 SEGS (mrestrict (w_H Wc) memc) (F + 56) bkids -> rd_u64 SEGS (mrestrict (w_H Wc) memc) (F + 64) bkeys ->
  rd_u64 SEGS (mrestrict (w_H Wc) memc) (bkeys + 8 * atv) bki ->
  st_ok_pi SEGS VAL (TE regs rg [w64 saved; w64 atv; w64 bkids; w64 bkeys; w64 (bkeys + 8 * atv); w64 bki]) ss_C
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_A + CRT_C_OFF))) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS CL_Bx [] (TE regs rg [w64 saved; w64 atv; w64 bkids; w64 bkeys; w64 (bkeys + 8 * atv); w64 bki])
    (mrestrict (w_H Wc) memc).
Proof.
intros fxk Wc memc rg saved atv F bkids bkeys bki R9 R26 R27 H1 H2 H3 HF0 HF1 HF2 Hk4 Hk8 Hkc Hat HkF Hsv Hbk Hbki
  (VBK & VSV) VAT [_ VKD] [_ VKY] [_ VKI].
unfold crt_spill, CRT_SP_AT, CRT_SP_BACK, CRT_SP_SAVED, CRT_OFF_BACK in *.
set (sp1 := CRT_sp1 (regs := regs)) in *.
set (E := TE regs rg [w64 saved; w64 atv; w64 bkids; w64 bkeys; w64 (bkeys + 8 * atv); w64 bki]).
assert (W9 : ew E (xr 9) = w64 sp1) by (unfold E, xr; rewrite (te_cur regs rg _ 9%bv 9) by reflexivity; exact R9).
assert (W26 : ew E (xr 26) = w64 SHADOW_OFF) by (unfold E, xr; rewrite (te_cur regs rg _ 26%bv 26) by reflexivity; exact R26).
assert (W27 : ew E (xr 27) = w64 F) by (unfold E, xr; rewrite (te_cur regs rg _ 27%bv 27) by reflexivity; exact R27).
assert (E64 : ew E 64 = w64 saved) by exact (te_more_lt regs rg _ 0 ltac:(lia)).
assert (E65 : ew E 65 = w64 atv) by exact (te_more_lt regs rg _ 1 ltac:(lia)).
assert (E66 : ew E 66 = w64 bkids) by exact (te_more_lt regs rg _ 2 ltac:(lia)).
assert (E67 : ew E 67 = w64 bkeys) by exact (te_more_lt regs rg _ 3 ltac:(lia)).
assert (E68 : ew E 68 = w64 (bkeys + 8 * atv)) by exact (te_more_lt regs rg _ 4 ltac:(lia)).
assert (E69 : ew E 69 = w64 bki) by exact (te_more_lt regs rg _ 5 ltac:(lia)).
assert (UB : forall k v, ew E k = w64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E k) = v)
  by (intros k v Hk Hv; rewrite Hk; apply unsigned_lit_small; exact Hv).
split; [|unfold sh_ok; apply Forall_nil].
apply ts_st_ok.
all: try change (TE regs rg [w64 saved; w64 atv; w64 bkids; w64 bkeys; w64 (bkeys + 8 * atv); w64 bki]) with E.
- apply te_regs_ok.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
  + apply (ts_rok E _ (xr 9) sp1); [apply UB; [exact W9 | lia] | lia | lia | intros o Ho; lia |].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (ts_chunk E _ _ 24 8 (SOff 64 0) saved); [| cbn; lia | cbn; lia | exact VSV].
      rewrite denot_lit_U, (U_atom_off E 64 saved 0 E64) by lia. rewrite Z.add_0_r. reflexivity.
    * apply (ts_chunk E _ _ 32 8 (SOff 65 0) atv); [| cbn; lia | cbn; lia | exact VAT].
      rewrite denot_lit_U, (U_atom_off E 65 atv 0 E65) by lia. rewrite Z.add_0_r. reflexivity.
    * apply (ts_chunk E _ _ 56 8 (SOff (xr 27) 32) (F + 32)); [| cbn; lia | cbn; lia | exact VBK].
      rewrite denot_lit_U, (U_atom_off E (xr 27) F 32 W27) by lia. reflexivity.
  + apply (ts_rok E _ (xr 27) F); [apply UB; [exact W27 | lia] | lia | lia | intros o Ho; lia |].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (ts_chunk E _ _ 56 8 (SOff 66 0) bkids); [| cbn; lia | cbn; lia | exact VKD].
      rewrite denot_lit_U, (U_atom_off E 66 bkids 0 E66) by lia. rewrite Z.add_0_r. reflexivity.
    * apply (ts_chunk E _ _ 64 8 (SOff 67 0) bkeys); [| cbn; lia | cbn; lia | exact VKY].
      rewrite denot_lit_U, (U_atom_off E 67 bkeys 0 E67) by lia. rewrite Z.add_0_r. reflexivity.
  + apply (ts_rok E _ 68%nat (bkeys + 8 * atv)); [apply UB; [exact E68 | lia] | lia | lia | intros o Ho; lia |].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (ts_chunk E _ _ 0 8 (SOff 69 0) bki); [| cbn; lia | cbn; lia | rewrite Z.add_0_r; exact VKI].
    rewrite denot_lit_U, (U_atom_off E 69 bki 0 E69) by lia. rewrite Z.add_0_r. reflexivity.
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !ts_bv_some.
  rewrite (UB _ _ W9 ltac:(lia)), (UB _ _ W27 ltac:(lia)), (UB _ _ E68 ltac:(lia)).
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; try lia.
- split; [|split; [exact I | split; [|exact I]]].
  + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (UB _ _ W9 ltac:(lia)), (UB _ _ W26 ltac:(unfold SHADOW_OFF; lia)), (UB _ _ W27 ltac:(lia)),
      (UB _ _ E68 ltac:(lia)).
    change (2 ^ 5) with 32. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
    unfold SHADOW_OFF. repeat split; lia.
  + apply U_inj. rewrite (cl_U_k8 E (SOff 67 0) (SOff 65 0)); rewrite ?(U_atom E 67 bkeys E67), ?(U_atom E 65 atv E65) by lia;
      try lia.
    rewrite (U_atom E 68 (bkeys + 8 * atv) E68) by lia. reflexivity.
Qed.

(* C1r (+0x668), strcmp (back.keys[at], MOD_AT)'s return: it answered EQUAL (a0 = 0); s5 = 8 at *)
Definition cl_at_C1r (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Dc Lamc : list (Z * Z)) (peakc cset saved cap : Z)
  (Dback : list (Z * Z)) (ms : list (list Z * PjTree.jv)) (rg : bvmap 5 word) : Prop :=
  cl_rw fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms /\
  cl_sp2 Wc memc (frame_addr lyc CRT_CID pos) saved /\
  crt_bregs (regs := regs) rg (frame_addr lyc CRT_CID pos) /\
  crt_spill (regs := regs) Wc memc CRT_SP_AT (Z.of_nat (cm_at ms)) /\
  getr rg 21 = w64 (8 * Z.of_nat (cm_at ms)) /\ getr rg 10 = w64 0.

Section C0.
Hypothesis KC1r : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg,
  cl_at_C1r fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk (CRT_CMP3_CALL + 4) rg memc mdc) QFa.

(* ---- C -> the strcmp (back.keys[at], MOD_AT) at +0x664 -> C1r: the inline check of back's key slot (+0x738's report
   unreachable: back's key array is a ledger block, block_shadow gives the slot), and the compare says EQUAL: the
   member of the rewritten tree at `at` is (MOD_AT, JStr STAMP) (Crt102Model.cm_set_at), so the property abort of
   new:759's first half (`bnez a0` at +0x66c) is not taken ---- *)
Lemma cl_C_head : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg,
  cl_at_C fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk CRT_C_OFF rg memc mdc) QFa.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg HC.
destruct HC as (HRW & HSP2 & HBR & SAT).
pose proof HRW as (Et & HFZ & HFK & HL & Hcs & Hcin & Hsv & Hcopy & Hback & Hd8 & Hrad & Hrab & Hrav & Hpos & _).
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ).
pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPl.
pose proof (crt_live_frame HL) as HFRM.
pose proof (crt_live_memnorm HL) as HPM.
pose proof (crt_side_ledger HSD) as HLD.
pose proof (crt_side_arodata HSD) as HRO.
pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkp & _).
assert (Etc : tc = PjTree.JObj (PjTree.pj_set_model ms ck_MOD_AT (PjTree.JStr ck_STAMP))) by (unfold crt_tc; rewrite Et; reflexivity).
rewrite Etc in Hback.
pose proof (cm_set_at ms (PjTree.JStr ck_STAMP)) as Hnth'.
assert (HinL : forall bk, In bk (Dback ++ (saved, cap) :: Dc) -> In bk Lamc).
{ intros bk Hb. apply (Permutation_in _ (Permutation_sym HPl)). apply in_or_app. left. exact Hb. }
assert (HDb : forall bk, In bk Dback -> In bk Lamc) by (intros bk Hb; apply HinL; apply in_or_app; left; exact Hb).
destruct (cl_node_obj _ _ _ _ _ Hback) as (bnum & bkids & bkeys & bcap & bDi & _ & _ & Hbh & _).
pose proof Hbh as (_ & _ & _ & _ & Hbkd & Hbky & _).
destruct (cl_obj_key _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLD Hback HDb Hbky Hnth')
  as (kp & kb & Hkp & Hcstr & Hinkb & SXk & Hraslot & Hk4 & Hk8 & Hkce & kc & Hkd & Hkl & Hkcap).
pose proof (crt_bregs_sp HBR) as R2.
pose proof (crt_bregs_gp HBR) as R3.
pose proof (crt_bregs_tp HBR) as R4.
pose proof (crt_bregs_s0 HBR) as R8.
pose proof (crt_bregs_s1 HBR) as R9.
pose proof (crt_bregs_s2 HBR) as R18.
pose proof (crt_bregs_s4 HBR) as R20.
pose proof (crt_bregs_s3 HBR) as R19.
pose proof (crt_bregs_s7 HBR) as R23.
pose proof (crt_bregs_s10 HBR) as R26.
pose proof (crt_bregs_s11 HBR) as R27.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cl_sp0 as (H16 & Hsp0 & H47). pose proof cl_sp1 as (Hs32 & Hs1).
assert (HSTKC : STKC = 27632) by (vm_compute; reflexivity).
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc (crt_frame_listed HFRM))
  as (Fb1 & Fb2 & Fb3).
change (fs_frame_bytes CRT_CID) with 512 in Fb2.
destruct (alx_frames SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc (crt_frame_listed HFRM))
  as (F32 & _).
(* back's key array: a ledger block, apart from the class-3 frame *)
destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc _ SIZE_MAXZ 0 bkeys kc _ _ HLD Hkl) as (Hkc0 & Hkab & _).
pose proof (sep_block_frame_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ CRT_CID pos HARc Hkab (crt_frame_listed HFRM)) as HkF.
unfold zdisjoint in HkF. cbn [fst snd] in HkF. change (fs_frame_bytes CRT_CID) with 512 in HkF.
change (@cf_head CfParams_preset) with 16 in HkF.
pose proof (req_size_pos (kc + 16) ltac:(lia)) as Hrq.
assert (Hrq' : kc + 16 <= req_size (kc + 16)) by (unfold req_size; destruct (Z.eqb_spec (kc + 16) 0); lia).
set (F := frame_addr lyc CRT_CID pos) in *.
set (sp1 := CRT_sp1 (regs := regs)) in *.
assert (Hsv0 : 0 <= saved < 2 ^ 64).
{ assert (Hin : In (saved, cap) Lamc) by (apply HinL; apply in_or_app; right; left; reflexivity).
  destruct (cl_blk_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLD Hin) as (Hk & Ha & Hb).
  pose proof YM05.alloc_ceiling_lt. change (@cf_head CfParams_preset) with 16 in Ha. lia. }
set (atv := Z.of_nat (cm_at ms)) in *.
assert (Hat : (cm_at ms < length (PjTree.pj_set_model ms ck_MOD_AT (PjTree.JStr ck_STAMP)))%nat)
  by (apply nth_error_Some; rewrite Hnth'; discriminate).
assert (Hatv : 0 <= atv < 2 ^ 54) by (unfold atv; split; [lia|]; pose proof YM05.alloc_ceiling_lt; lia).
pose proof Hkp as [Rkp _]. pose proof Hbkd as [Rbkd _].
destruct (cl_C_entry fxk Wc memc rg saved atv F bkids bkeys kp R9 R26 R27 ltac:(lia) ltac:(lia) Hs32 ltac:(lia)
  ltac:(lia) F32 Hk4 Hk8 ltac:(pose proof YM05.alloc_ceiling_lt; unfold atv in *; lia) Hatv
  ltac:(unfold atv in *; lia) Hsv0 Rbkd Rkp HSP2 SAT
  ltac:(replace (F + 56) with (F + CRT_OFF_BACK + 24) by (unfold CRT_OFF_BACK; lia); exact Hbkd)
  ltac:(replace (F + 64) with (F + CRT_OFF_BACK + 32) by (unfold CRT_OFF_BACK; lia); exact Hbky) Hkp) as [HS SHOK].
set (E := TE regs rg [w64 saved; w64 atv; w64 bkids; w64 bkeys; w64 (bkeys + 8 * atv); w64 kp]) in *.
assert (HEI : img_env VAL A_LIM E) by apply te_env.
assert (W26 : ew E 58 = w64 SHADOW_OFF)
  by (change 58%nat with (xr 26); unfold E, xr; rewrite (te_cur regs rg _ 26%bv 26) by reflexivity; exact R26).
assert (E68 : ew E 68 = w64 (bkeys + 8 * atv)) by exact (te_more_lt regs rg _ 4 ltac:(lia)).
assert (E65 : ew E 65 = w64 atv) by exact (te_more_lt regs rg _ 1 ltac:(lia)).
pose (RUN := @crt_run_xw_inv fxk rc SK A_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (YSRrMemnorm.srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)) WS_HJ).
unfold crt_cfg.
paj_run_tok_x_inv RUN HS HJ SHOK HPM CL_SPAN.
all: try (cbn [ms_mem mkst restrict]; unfold CL_Bx; change (SOff (xr 26) 0) with (SOff 58 0);
  rewrite (U_atom E 68 _ E68) by lia; rewrite (U_atom E 58 SHADOW_OFF W26) by (unfold SHADOW_OFF; lia);
  exact Hraslot).
all: try (lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
  let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil).
apply frame_of_read_only in HF; [|vm_compute; reflexivity].
rewrite HF in HJ, HPM. clear HFr HG.
assert (KB : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms0) r = getr rg r).
{ intros r Hr. unfold E in HS. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [clkeep HS |]). destruct Hr. }
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (1%bv : bv 5) Q1. prreg HS (21%bv : bv 5) Q21.
assert (X10 : getr (ms_regs ms0) 10 = w64 kp).
{ rewrite Q10. rewrite ?ew_ewset_other by lia. exact (te_more_lt regs rg _ 5 ltac:(lia)). }
assert (X11 : getr (ms_regs ms0) 11 = w64 CRT_MOD_AT_A).
{ rewrite Q11. apply cl_modat_den. rewrite ?ew_ewset_other by lia. apply te_img. unfold A_TEXT, A_LIM. lia. }
assert (X1 : getr (ms_regs ms0) 1 = Z_to_bv 64 (BASE + (CRT_PC_A + (CRT_CMP3_CALL + 4)))).
{ rewrite Q1. vm_compute. reflexivity. }
assert (X21 : getr (ms_regs ms0) 21 = w64 (8 * atv)).
{ rewrite Q21. apply cl_sll3_w; [|lia]. rewrite E65. unfold w64. apply unsigned_lit_small. lia. }
pose proof (cl_bregs_eq rg (ms_regs ms0) F HBR ltac:(intros r Hr; apply KB; cbv [In] in Hr |- *; tauto)) as HBR1.
assert (SY : cl_sarg Wc memc CRT_MOD_AT_A (Z.of_nat (length ck_MOD_AT))).
{ apply cl_sarg_cstr. exact (crt_cstr_modat_A LAWS zs_aligned img_shadow_vis_x _ _ _ _ _ _ HARc HRO HKM). }
pose proof (cl_live_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sp1 sp1 HL HJ HB_HJ ltac:(lia) ltac:(unfold CRT_SP_F; lia)
  (fun a _ _ => eq_refl) (fun a Ha => Ha) HPM) as HL1.
rewrite <- HF in HL1, SXk, SY.
apply (cl_strcmp_call fxk Wc _ _ ms0 _ lyc Sc Hpc kj pos _ Lamc peakc _ 0 0 (CRT_CMP3_CALL + 4) kp CRT_MOD_AT_A
  (Z.of_nat (length ck_MOD_AT)) (Z.of_nat (length ck_MOD_AT)) HS ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) HL1 HBR1 X1 ltac:(unfold CRT_CMP3_CALL; lia) ltac:(unfold CRT_CMP3_CALL; lia)
  X10 X11 SXk SY).
intros regs2 mem2 md2 v WS_HJ2 HJ2 HB_HJ2 HP Hv Hcmp Hfr Hpr2 Hmn.
rewrite HF in Hfr, Hpr2, Hmn, Hcmp.
assert (HES : ESTACK = 4096) by reflexivity.
change (CRT_sp1 (regs := regs)) with sp1 in Hfr.
assert (Hhi : forall a, sp1 <= a < sp1 + CRT_SP_F -> aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. apply Hfr; unfold CRT_SP_F in Ha; lia. }
pose proof (crt_live_memnorm HL) as HMN0.
pose proof (cl_rw_keep _ _ _ _ _ memc mem2 _ _ _ _ _ _ _ _ _ _ _ _ _ (sp1 - 2 * ESTACK) sp1 HRW HJ2 HB_HJ2
  ltac:(lia) ltac:(unfold CRT_SP_F; lia) Hfr Hpr2 ltac:(intros H0; exact (Hmn (HMN0 H0)))) as HRW2.
pose proof (cl_bregs_eq _ regs2 F HBR1 ltac:(intros r Hr; apply (cl_cs_keep _ _ HP); cbv [In] in Hr |- *; tauto)) as HBR2.
apply (KC1r fxk lyc Sc Hpc Wc mem2 md2 kj pos Dc Lamc peakc cset saved cap Dback ms regs2).
destruct HSP2 as (SBK & SSV).
refine (conj HRW2 (conj (conj _ _) (conj HBR2 (conj _ (conj _ _))))).
- apply (cl_spill_keep Wc memc mem2); [exact Hhi | unfold CRT_SP_BACK; lia | unfold CRT_SP_BACK, CRT_SP_F; lia | exact SBK].
- apply (cl_spill_keep Wc memc mem2); [exact Hhi | unfold CRT_SP_SAVED; lia | unfold CRT_SP_SAVED, CRT_SP_F; lia | exact SSV].
- apply (cl_spill_keep Wc memc mem2); [exact Hhi | unfold CRT_SP_AT; lia | unfold CRT_SP_AT, CRT_SP_F; lia | exact SAT].
- rewrite (cl_cs_keep _ _ HP 21%bv) by (cbv [In]; tauto). exact X21.
- rewrite Hv. apply Hcmp.
  pose proof Hcstr as (_ & _ & _ & (_ & Gk)).
  pose proof (crt_cstr_modat_A LAWS zs_aligned img_shadow_vis_x _ _ _ _ _ _ HARc HRO HKM) as ((Gm & _) & _).
  exact (proj2 (cl_str_eq (w_H Wc) memc kp CRT_MOD_AT_A ck_MOD_AT ck_MOD_AT Gk Gm) eq_refl).
Qed.
End C0.

(* ---- member i of an object node in the walk's blocks: its value's node in the kids array (addressable), the kids
   array's bounds ---- *)
Lemma cl_obj_kid : forall lyc Sc Hpc (Wc : world SEGS) memc mdc Lamc peakc cntc failc ranc mostc ownc dp ms0 Dd kids i nm u,
  ARx lyc Sc Hpc Wc memc mdc -> prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc ->
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) dp (PjTree.JObj ms0) Dd -> (forall bk, In bk Dd -> In bk Lamc) ->
  rd_u64 SEGS (mrestrict (w_H Wc) memc) (dp + 24) kids -> nth_error ms0 i = Some (nm, u) ->
  exists D1, incl D1 Dd /\ pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) (kids + 56 * Z.of_nat i) u D1 /\
    range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (kids + 56 * Z.of_nat i) 56 /\
    4096 <= kids /\ kids mod 8 = 0 /\ kids + 56 * Z.of_nat (length ms0) <= YM05.alloc_ceiling /\
    exists kc, In (kids, kc) Lamc /\ 56 * Z.of_nat (length ms0) <= kc.
Proof.
intros lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc mostc ownc dp ms0 Dd kids i nm u HAR HL HN HDL Hk Hi.
destruct (cl_node_obj _ _ _ _ _ HN) as (num & kids' & keys & dcap & Di & _ & _ & Hhdr & Hncap & Hcap & EDi & Hmem).
pose proof Hhdr as (_ & _ & _ & _ & Hk' & _).
assert (Ek : kids' = kids) by (destruct Hk as [R1 V1]; destruct Hk' as [R2 V2]; exact (cl_vm_det _ _ _ _ _ V2 V1 R2 R1)).
subst kids'.
assert (Hlt : (i < length ms0)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
destruct Hcap as [(-> & _ & _) | (Hc0 & Hkd & _)]; [lia|].
destruct (cl_mems_nth _ _ _ _ _ _ _ _ _ _ Hmem Hi) as (kp & kb & D1 & _ & _ & _ & Hincl & HP).
destruct (cl_hblk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HL Hkd) as (_ & H16 & _ & Hce & H4 & Hbs & _).
exists D1. split.
{ intros b Hb. rewrite EDi. apply in_or_app. right. exact (Hincl b Hb). }
split; [exact HP|].
split; [exact (block_shadow_range _ SHADOW_OFF kids (56 * dcap) (kids + 56 * Z.of_nat i) 56 Hbs ltac:(lia) ltac:(lia))|].
split; [lia|]. split; [lia|]. split; [lia|].
exists (56 * dcap). split; [exact Hkd | lia].
Qed.

(* ---- a string node, unfolded: type 4, the string's pointer at +16, the string in its one block ---- *)
Lemma cl_node_str : forall (m : word -> option byte) lblk p s D',
  pj_nodeR SEGS m lblk p (PjTree.JStr s) D' ->
  exists num str k, pj_hdrR SEGS m p 4 num str 0 0 0 0 /\ pj_cstrR SEGS m lblk str k s /\ D' = [(str, k)].
Proof.
intros m lblk p s D' (_ & _ & num & str & kids & keys & n & cap & Hh & -> & -> & -> & -> & k & Hc & ->).
exists num, str, k. split; [exact Hh|]. split; [exact Hc | reflexivity].
Qed.

(* ---- C1r's entry state (extras: 64 = saved, 65 = at, 66 = back.kids, 67 = back.keys, 68 = &back.kids[at],
   69 = back.kids[at].str); a0 = 0 (the compare said EQUAL), s5 = 8 at. The run reads 0x18 / 0x20 / 0x38 (s1), back's
   header and the member's node; it writes nothing ---- *)
Definition ss_C1r : sstate := mkSS (CRT_PC_A + (CRT_CMP3_CALL + 4)) cur_atoms
  [ YP09.mkRegion (Some (xr 9)) 24 64 0 0
      [YP09.mkChunk 24 (CVal 8 (SOff 64 0)); YP09.mkChunk 32 (CVal 8 (SOff 65 0)); YP09.mkChunk 56 (CVal 8 (SOff (xr 27) 32))];
    YP09.mkRegion (Some (xr 27)) 56 72 0 0 [YP09.mkChunk 56 (CVal 8 (SOff 66 0)); YP09.mkChunk 64 (CVal 8 (SOff 67 0))];
    YP09.mkRegion (Some 68%nat) 0 24 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 4)); YP09.mkChunk 16 (CVal 8 (SOff 69 0))] ]
  None
  (mkFacts [(xr 9, mkAF (2 ^ 46) (2 ^ 47) 5); (xr 26, mkAF SHADOW_OFF SHADOW_OFF 0); (xr 27, mkAF 4096 (2 ^ 47 - 512) 5);
            (68%nat, mkAF 4096 (2 ^ 47 - 56) 3)] [cl_cR_eq]
    [(SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff (xr 21) 0) (SLit (2 ^ 64 - 1))) (SAlu ALU_SLL (SOff 65 0) (SLit 6)))
        (SOff 66 0), SOff 68 0)]).

Lemma cl_C1r_entry : forall (fxk : YK11.FPState) (Wc : world SEGS) memc rg saved atv F bkids bkeys sp,
  getr rg 9 = w64 (CRT_sp1 (regs := regs)) -> getr rg 10 = w64 0 -> getr rg 21 = w64 (8 * atv) ->
  getr rg 26 = w64 SHADOW_OFF -> getr rg 27 = w64 F ->
  2 ^ 46 <= CRT_sp1 (regs := regs) -> CRT_sp1 (regs := regs) + 96 <= 2 ^ 47 -> CRT_sp1 (regs := regs) mod 32 = 0 ->
  4096 <= F -> F + 512 <= CRT_sp1 (regs := regs) -> F mod 32 = 0 ->
  4096 <= bkids -> bkids mod 8 = 0 -> bkids + 56 * atv + 56 <= CRT_sp1 (regs := regs) -> 0 <= atv < 2 ^ 54 ->
  (bkids + 56 * atv + 24 <= F \/ F + 512 <= bkids + 56 * atv) ->
  0 <= saved < 2 ^ 64 -> 0 <= bkeys < 2 ^ 64 -> 0 <= sp < 2 ^ 64 ->
  cl_sp2 Wc memc F saved -> crt_spill (regs := regs) Wc memc CRT_SP_AT atv ->
  rd_u64 SEGS (mrestrict (w_H Wc) memc) (F + 56) bkids -> rd_u64 SEGS (mrestrict (w_H Wc) memc) (F + 64) bkeys ->
  rd_u32 SEGS (mrestrict (w_H Wc) memc) (bkids + 56 * atv) 4 ->
  rd_u64 SEGS (mrestrict (w_H Wc) memc) (bkids + 56 * atv + 16) sp ->
  st_ok_pi SEGS VAL (TE regs rg [w64 saved; w64 atv; w64 bkids; w64 bkeys; w64 (bkids + 56 * atv); w64 sp]) ss_C1r
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_A + (CRT_CMP3_CALL + 4)))) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS CL_Bx [] (TE regs rg [w64 saved; w64 atv; w64 bkids; w64 bkeys; w64 (bkids + 56 * atv); w64 sp])
    (mrestrict (w_H Wc) memc).
Proof.
intros fxk Wc memc rg saved atv F bkids bkeys sp R9 R10 R21 R26 R27 H1 H2 H3 HF0 HF1 HF2 Hk4 Hk8 Hkc Hat HkF Hsv Hbk Hsp
  (VBK & VSV) VAT [_ VKD] [_ VKY] [_ VTY] [_ VSP].
unfold crt_spill, CRT_SP_AT, CRT_SP_BACK, CRT_SP_SAVED, CRT_OFF_BACK in *.
set (sp1 := CRT_sp1 (regs := regs)) in *.
set (E := TE regs rg [w64 saved; w64 atv; w64 bkids; w64 bkeys; w64 (bkids + 56 * atv); w64 sp]).
assert (W9 : ew E (xr 9) = w64 sp1) by (unfold E, xr; rewrite (te_cur regs rg _ 9%bv 9) by reflexivity; exact R9).
assert (W10 : ew E (xr 10) = w64 0) by (unfold E, xr; rewrite (te_cur regs rg _ 10%bv 10) by reflexivity; exact R10).
assert (W21 : ew E (xr 21) = w64 (8 * atv)) by (unfold E, xr; rewrite (te_cur regs rg _ 21%bv 21) by reflexivity; exact R21).
assert (W26 : ew E (xr 26) = w64 SHADOW_OFF) by (unfold E, xr; rewrite (te_cur regs rg _ 26%bv 26) by reflexivity; exact R26).
assert (W27 : ew E (xr 27) = w64 F) by (unfold E, xr; rewrite (te_cur regs rg _ 27%bv 27) by reflexivity; exact R27).
assert (E64 : ew E 64 = w64 saved) by exact (te_more_lt regs rg _ 0 ltac:(lia)).
assert (E65 : ew E 65 = w64 atv) by exact (te_more_lt regs rg _ 1 ltac:(lia)).
assert (E66 : ew E 66 = w64 bkids) by exact (te_more_lt regs rg _ 2 ltac:(lia)).
assert (E67 : ew E 67 = w64 bkeys) by exact (te_more_lt regs rg _ 3 ltac:(lia)).
assert (E68 : ew E 68 = w64 (bkids + 56 * atv)) by exact (te_more_lt regs rg _ 4 ltac:(lia)).
assert (E69 : ew E 69 = w64 sp) by exact (te_more_lt regs rg _ 5 ltac:(lia)).
assert (UB : forall k v, ew E k = w64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E k) = v)
  by (intros k v Hk Hv; rewrite Hk; apply unsigned_lit_small; exact Hv).
split; [|unfold sh_ok; apply Forall_nil].
apply ts_st_ok.
all: try change (TE regs rg [w64 saved; w64 atv; w64 bkids; w64 bkeys; w64 (bkids + 56 * atv); w64 sp]) with E.
- apply te_regs_ok.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
  + apply (ts_rok E _ (xr 9) sp1); [apply UB; [exact W9 | lia] | lia | lia | intros o Ho; lia |].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (ts_chunk E _ _ 24 8 (SOff 64 0) saved); [| cbn; lia | cbn; lia | exact VSV].
      rewrite denot_lit_U, (U_atom_off E 64 saved 0 E64) by lia. rewrite Z.add_0_r. reflexivity.
    * apply (ts_chunk E _ _ 32 8 (SOff 65 0) atv); [| cbn; lia | cbn; lia | exact VAT].
      rewrite denot_lit_U, (U_atom_off E 65 atv 0 E65) by lia. rewrite Z.add_0_r. reflexivity.
    * apply (ts_chunk E _ _ 56 8 (SOff (xr 27) 32) (F + 32)); [| cbn; lia | cbn; lia | exact VBK].
      rewrite denot_lit_U, (U_atom_off E (xr 27) F 32 W27) by lia. reflexivity.
  + apply (ts_rok E _ (xr 27) F); [apply UB; [exact W27 | lia] | lia | lia | intros o Ho; lia |].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (ts_chunk E _ _ 56 8 (SOff 66 0) bkids); [| cbn; lia | cbn; lia | exact VKD].
      rewrite denot_lit_U, (U_atom_off E 66 bkids 0 E66) by lia. rewrite Z.add_0_r. reflexivity.
    * apply (ts_chunk E _ _ 64 8 (SOff 67 0) bkeys); [| cbn; lia | cbn; lia | exact VKY].
      rewrite denot_lit_U, (U_atom_off E 67 bkeys 0 E67) by lia. rewrite Z.add_0_r. reflexivity.
  + apply (ts_rok E _ 68%nat (bkids + 56 * atv)); [apply UB; [exact E68 | lia] | lia | lia | intros o Ho; lia |].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (ts_chunk E _ _ 0 4 (SLit 4) 4); [| cbn; lia | cbn; lia | rewrite Z.add_0_r; exact VTY].
      rewrite denot_lit_U, U_SLit. reflexivity.
    * apply (ts_chunk E _ _ 16 8 (SOff 69 0) sp); [| cbn; lia | cbn; lia | exact VSP].
      rewrite denot_lit_U, (U_atom_off E 69 sp 0 E69) by lia. rewrite Z.add_0_r. reflexivity.
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !ts_bv_some.
  rewrite (UB _ _ W9 ltac:(lia)), (UB _ _ W27 ltac:(lia)), (UB _ _ E68 ltac:(lia)).
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [|split; [|split; [|exact I]]].
  + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (UB _ _ W9 ltac:(lia)), (UB _ _ W26 ltac:(unfold SHADOW_OFF; lia)), (UB _ _ W27 ltac:(lia)),
      (UB _ _ E68 ltac:(lia)).
    change (2 ^ 5) with 32. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
    unfold SHADOW_OFF. repeat split; lia.
  + split; [|exact I]. unfold acond_ok, cl_cR_eq. cbn [ac_c ac_a ac_b].
    rewrite branch_eq_U, U_SLit. rewrite (U_atom E (xr 10) 0 W10) by lia. reflexivity.
  + apply U_inj. rewrite (cl_U_kid E (SOff (xr 21) 0) (SOff 65 0) (SOff 66 0));
      rewrite ?(U_atom E (xr 21) (8 * atv) W21), ?(U_atom E 65 atv E65), ?(U_atom E 66 bkids E66) by lia; try lia.
    rewrite (U_atom E 68 (bkids + 56 * atv) E68) by lia. reflexivity.
Qed.

(* C2r (+0x6c8), strcmp (back.kids[at].str, STAMP)'s return: it answered EQUAL (a0 = 0); s6 = saved *)
Definition cl_at_C2r (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Dc Lamc : list (Z * Z)) (peakc cset saved cap : Z)
  (Dback : list (Z * Z)) (ms : list (list Z * PjTree.jv)) (rg : bvmap 5 word) : Prop :=
  cl_rw fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms /\
  crt_spill (regs := regs) Wc memc CRT_SP_BACK (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) /\
  crt_bregs (regs := regs) rg (frame_addr lyc CRT_CID pos) /\
  getr rg 22 = w64 saved /\ getr rg 10 = w64 0.

Section C1.
Hypothesis KC2r : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg,
  cl_at_C2r fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk (CRT_CMP4_CALL + 4) rg memc mdc) QFa.

(* ---- C1r -> the strcmp (back.kids[at].str, STAMP) at +0x6c4 -> C2r: new:759's first half is not taken (a0 = 0),
   the two inline checks of the member's node (+0x700 / +0x73c's reports unreachable: back's kids array is a ledger
   block, block_shadow gives the node), its type word is 4 = PJ_STRING (new:759's second half, `bne a1, a2` at
   +0x680, not taken: the member is JStr STAMP), and the compare says EQUAL (new:764 not taken at C2r) ---- *)
Lemma cl_C1r : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg,
  cl_at_C1r fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk (CRT_CMP3_CALL + 4) rg memc mdc) QFa.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg HC.
destruct HC as (HRW & HSP2 & HBR & SAT & R21 & R10).
pose proof HRW as (Et & HFZ & HFK & HL & Hcs & Hcin & Hsv & Hcopy & Hback & Hd8 & Hrad & Hrab & Hrav & Hpos & _).
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ).
pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPl.
pose proof (crt_live_frame HL) as HFRM.
pose proof (crt_live_memnorm HL) as HPM.
pose proof (crt_side_ledger HSD) as HLD.
pose proof (crt_side_arodata HSD) as HRO.
pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkp & _).
assert (Etc : tc = PjTree.JObj (PjTree.pj_set_model ms ck_MOD_AT (PjTree.JStr ck_STAMP))) by (unfold crt_tc; rewrite Et; reflexivity).
rewrite Etc in Hback.
pose proof (cm_set_at ms (PjTree.JStr ck_STAMP)) as Hnth'.
assert (HinL : forall bk, In bk (Dback ++ (saved, cap) :: Dc) -> In bk Lamc).
{ intros bk Hb. apply (Permutation_in _ (Permutation_sym HPl)). apply in_or_app. left. exact Hb. }
assert (HDb : forall bk, In bk Dback -> In bk Lamc) by (intros bk Hb; apply HinL; apply in_or_app; left; exact Hb).
destruct (cl_node_obj _ _ _ _ _ Hback) as (bnum & bkids & bkeys & bcap & bDi & _ & _ & Hbh & _).
pose proof Hbh as (_ & _ & _ & _ & Hbkd & Hbky & _).
destruct (cl_obj_kid _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLD Hback HDb Hbkd Hnth')
  as (D1 & HD1 & Hkid & Hrakid & Hkd4 & Hkd8 & Hkdc & kc & Hkdl & Hkdcap).
destruct (cl_node_str _ _ _ _ _ Hkid) as (knum & sp & sk & Hkh & Hscs & ED1).
pose proof Hkh as (_ & Hty & _ & Hsp & _).
assert (Hinsp : In (sp, sk) Lamc) by (apply HDb; apply HD1; rewrite ED1; left; reflexivity).
pose proof Hscs as (_ & Hskb & Hsk32 & Hsby).
pose proof (cl_sarg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLD Hinsp Hsby Hskb Hsk32) as SXs.
pose proof (crt_bregs_sp HBR) as R2.
pose proof (crt_bregs_gp HBR) as R3.
pose proof (crt_bregs_tp HBR) as R4.
pose proof (crt_bregs_s0 HBR) as R8.
pose proof (crt_bregs_s1 HBR) as R9.
pose proof (crt_bregs_s2 HBR) as R18.
pose proof (crt_bregs_s4 HBR) as R20.
pose proof (crt_bregs_s3 HBR) as R19.
pose proof (crt_bregs_s7 HBR) as R23.
pose proof (crt_bregs_s10 HBR) as R26.
pose proof (crt_bregs_s11 HBR) as R27.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cl_sp0 as (H16 & Hsp0 & H47). pose proof cl_sp1 as (Hs32 & Hs1).
assert (HSTKC : STKC = 27632) by (vm_compute; reflexivity).
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc (crt_frame_listed HFRM))
  as (Fb1 & Fb2 & Fb3).
change (fs_frame_bytes CRT_CID) with 512 in Fb2.
destruct (alx_frames SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc (crt_frame_listed HFRM))
  as (F32 & _).
(* back's kids array: a ledger block, apart from the class-3 frame *)
destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc _ SIZE_MAXZ 0 bkids kc _ _ HLD Hkdl) as (Hkc0 & Hkab & _).
pose proof (sep_block_frame_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ CRT_CID pos HARc Hkab (crt_frame_listed HFRM)) as HkF.
unfold zdisjoint in HkF. cbn [fst snd] in HkF. change (fs_frame_bytes CRT_CID) with 512 in HkF.
change (@cf_head CfParams_preset) with 16 in HkF.
pose proof (req_size_pos (kc + 16) ltac:(lia)) as Hrq.
assert (Hrq' : kc + 16 <= req_size (kc + 16)) by (unfold req_size; destruct (Z.eqb_spec (kc + 16) 0); lia).
set (F := frame_addr lyc CRT_CID pos) in *.
set (sp1 := CRT_sp1 (regs := regs)) in *.
assert (Hsv0 : 0 <= saved < 2 ^ 64).
{ assert (Hin : In (saved, cap) Lamc) by (apply HinL; apply in_or_app; right; left; reflexivity).
  destruct (cl_blk_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLD Hin) as (Hk & Ha & Hb).
  pose proof YM05.alloc_ceiling_lt. change (@cf_head CfParams_preset) with 16 in Ha. lia. }
set (atv := Z.of_nat (cm_at ms)) in *.
assert (Hat : (cm_at ms < length (PjTree.pj_set_model ms ck_MOD_AT (PjTree.JStr ck_STAMP)))%nat)
  by (apply nth_error_Some; rewrite Hnth'; discriminate).
assert (Hatv : 0 <= atv < 2 ^ 54) by (unfold atv; split; [lia|]; pose proof YM05.alloc_ceiling_lt; lia).
pose proof Hbky as [Rbky _]. pose proof Hsp as [Rsp _]. pose proof Hbkd as [Rbkd _].
destruct (cl_C1r_entry fxk Wc memc rg saved atv F bkids bkeys sp R9 R10 R21 R26 R27 ltac:(lia) ltac:(lia) Hs32 ltac:(lia)
  ltac:(lia) F32 Hkd4 Hkd8 ltac:(pose proof YM05.alloc_ceiling_lt; unfold atv in *; lia) Hatv
  ltac:(unfold atv in *; lia) Hsv0 Rbky Rsp HSP2 SAT
  ltac:(replace (F + 56) with (F + CRT_OFF_BACK + 24) by (unfold CRT_OFF_BACK; lia); exact Hbkd)
  ltac:(replace (F + 64) with (F + CRT_OFF_BACK + 32) by (unfold CRT_OFF_BACK; lia); exact Hbky) Hty Hsp) as [HS SHOK].
set (E := TE regs rg [w64 saved; w64 atv; w64 bkids; w64 bkeys; w64 (bkids + 56 * atv); w64 sp]) in *.
assert (HEI : img_env VAL A_LIM E) by apply te_env.
assert (W26 : ew E 58 = w64 SHADOW_OFF)
  by (change 58%nat with (xr 26); unfold E, xr; rewrite (te_cur regs rg _ 26%bv 26) by reflexivity; exact R26).
assert (E68 : ew E 68 = w64 (bkids + 56 * atv)) by exact (te_more_lt regs rg _ 4 ltac:(lia)).
pose (RUN := @crt_run_xw_inv fxk rc SK A_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (YSRrMemnorm.srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)) WS_HJ).
unfold crt_cfg.
paj_run_tok_x_inv RUN HS HJ SHOK HPM CL_SPAN.
all: try (cbn [ms_mem mkst restrict]; unfold CL_Bx; change (SOff (xr 26) 0) with (SOff 58 0);
  first [rewrite (U_atom_off E 68 _ 16 E68) by lia | rewrite (U_atom E 68 _ E68) by lia];
  rewrite (U_atom E 58 SHADOW_OFF W26) by (unfold SHADOW_OFF; lia);
  apply (range_addressable_sub _ SHADOW_OFF (bkids + 56 * atv) 56 _ _ Hrakid); lia).
all: try (lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
  let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil).
apply frame_of_read_only in HF; [|vm_compute; reflexivity].
rewrite HF in HJ, HPM. clear HFr HG.
assert (KB : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms0) r = getr rg r).
{ intros r Hr. unfold E in HS. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [clkeep HS |]). destruct Hr. }
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (1%bv : bv 5) Q1. prreg HS (22%bv : bv 5) Q22.
assert (X10 : getr (ms_regs ms0) 10 = w64 sp).
{ rewrite Q10. rewrite ?ew_ewset_other by lia. exact (te_more_lt regs rg _ 5 ltac:(lia)). }
assert (X11 : getr (ms_regs ms0) 11 = w64 CRT_STAMP_A).
{ rewrite Q11. apply cl_stamp_den. rewrite ?ew_ewset_other by lia. apply te_img. unfold A_TEXT, A_LIM. lia. }
assert (X22 : getr (ms_regs ms0) 22 = w64 saved).
{ rewrite Q22. rewrite ?ew_ewset_other by lia. exact (te_more_lt regs rg _ 0 ltac:(lia)). }
assert (X1 : getr (ms_regs ms0) 1 = Z_to_bv 64 (BASE + (CRT_PC_A + (CRT_CMP4_CALL + 4)))).
{ rewrite Q1. vm_compute. reflexivity. }
pose proof (cl_bregs_eq rg (ms_regs ms0) F HBR ltac:(intros r Hr; apply KB; cbv [In] in Hr |- *; tauto)) as HBR1.
assert (SY : cl_sarg Wc memc CRT_STAMP_A (Z.of_nat (length ck_STAMP))).
{ apply cl_sarg_cstr. exact (crt_cstr_stamp_A LAWS zs_aligned img_shadow_vis_x _ _ _ _ _ _ HARc HRO HKS). }
pose proof (cl_live_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sp1 sp1 HL HJ HB_HJ ltac:(lia) ltac:(unfold CRT_SP_F; lia)
  (fun a _ _ => eq_refl) (fun a Ha => Ha) HPM) as HL1.
rewrite <- HF in HL1, SXs, SY.
apply (cl_strcmp_call fxk Wc _ _ ms0 _ lyc Sc Hpc kj pos _ Lamc peakc _ 0 0 (CRT_CMP4_CALL + 4) sp CRT_STAMP_A
  (Z.of_nat (length ck_STAMP)) (Z.of_nat (length ck_STAMP)) HS ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) HL1 HBR1 X1 ltac:(unfold CRT_CMP4_CALL; lia) ltac:(unfold CRT_CMP4_CALL; lia)
  X10 X11 SXs SY).
intros regs2 mem2 md2 v WS_HJ2 HJ2 HB_HJ2 HP Hv Hcmp Hfr Hpr2 Hmn.
rewrite HF in Hfr, Hpr2, Hmn, Hcmp.
assert (HES : ESTACK = 4096) by reflexivity.
change (CRT_sp1 (regs := regs)) with sp1 in Hfr.
assert (Hhi : forall a, sp1 <= a < sp1 + CRT_SP_F -> aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. apply Hfr; unfold CRT_SP_F in Ha; lia. }
pose proof (crt_live_memnorm HL) as HMN0.
pose proof (cl_rw_keep _ _ _ _ _ memc mem2 _ _ _ _ _ _ _ _ _ _ _ _ _ (sp1 - 2 * ESTACK) sp1 HRW HJ2 HB_HJ2
  ltac:(lia) ltac:(unfold CRT_SP_F; lia) Hfr Hpr2 ltac:(intros H0; exact (Hmn (HMN0 H0)))) as HRW2.
pose proof (cl_bregs_eq _ regs2 F HBR1 ltac:(intros r Hr; apply (cl_cs_keep _ _ HP); cbv [In] in Hr |- *; tauto)) as HBR2.
apply (KC2r fxk lyc Sc Hpc Wc mem2 md2 kj pos Dc Lamc peakc cset saved cap Dback ms regs2).
destruct HSP2 as (SBK & SSV).
refine (conj HRW2 (conj _ (conj HBR2 (conj _ _)))).
- apply (cl_spill_keep Wc memc mem2); [exact Hhi | unfold CRT_SP_BACK; lia | unfold CRT_SP_BACK, CRT_SP_F; lia | exact SBK].
- rewrite (cl_cs_keep _ _ HP 22%bv) by (cbv [In]; tauto). exact X22.
- rewrite Hv. apply Hcmp.
  pose proof Hsby as (_ & Gs).
  pose proof (crt_cstr_stamp_A LAWS zs_aligned img_shadow_vis_x _ _ _ _ _ _ HARc HRO HKS) as ((Gm & _) & _).
  exact (proj2 (cl_str_eq (w_H Wc) memc sp CRT_STAMP_A ck_STAMP ck_STAMP Gs Gm) eq_refl).
Qed.
End C1.

(* ---- A fuzz_free FROM check_round_trip AT THE REALIGNED sp (+0x6d0): the tfuzz_free_specX text through the Kit's
   call rule (crt102rw_call_ch, whose chain shape gives the free's trace by crt102rw_free_trace); a non-NULL pointer of a
   block the walk holds (Dx), freed at the call's footprint (its allocator block). The continuation receives the two
   journals, the kept registers and the text's p <> 0 post. ---- *)
Lemma cl_ff_call : forall (fxk : YK11.FPState) Wc E ss ms mdc lyc Sc Hpc kj pos Dx Lamc peakc cntc (p n : Z),
  frm_zero (@YK11.fp_csr fxk) ->
  @st_ok SEGS fxk E ss (restrict (w_H Wc) ms) -> ss_resv ss = None -> ss_pc ss = SIGMA AS_fuzz_free ->
  bv_unsigned (ew E 2) = sp0 ->
  livea lyc Sc Hpc Wc (ms_mem ms) mdc kj pos Dx Lamc peakc cntc 0 0 ->
  crt_bregs (regs := regs) (ms_regs ms) (frame_addr lyc CRT_CID pos) ->
  getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRT_PC_A + (CRT_FF2_CALL + 4))) ->
  getr (ms_regs ms) 10 = w64 p -> p <> 0 -> In (p, n) Dx ->
  YGcfRoomLive.ccnt24 Sc <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  (* the text's hull admission (tfuzz_free_specX, its own shape); the caller pays it from its
     run position (Crt102HullPos.hull_free_of_room_pos under HOS4) *)
  (p <> 0 -> PresetHullBudget.hull_budget Sc []) ->
  (forall (fx' : YK11.FPState) ly2 S2 Hp2 W2 regs2 mem2 md2 k1,
     frm_zero (@YK11.fp_csr fx') -> fregs_kept_x fxk fx' ->
     (exists WS, AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly2 S2 Hp2 W2 mem2 md2 (kj + k1) WS /\
     YCbqGwild.wbudget [] (prh_wk F_check_round_trip) WS) ->
     ajournal_xR (SK := SK) SEGS B PST ARx RZW (@STK_fuzz_free prh_img_A) (CRT_sp1 (regs := regs))
       (ablocks_fp [(p - cf_head, n + cf_head)]) lyc Sc Hpc Wc (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
     aregs_preserved (ms_regs ms) regs2 ->
     room_live_cf S2 ->
     (forall (sm : list Z -> Z * Z) (xs : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
        (H0 : list Z) (hist : list YG00.chunk),
        PresetRoomPos.iface_room_pos sm xs os i H0 hist Sc ->
        PRH_Base.prh_run_at sm xs os i [PresetReqAt.HFr (n + cf_head)] ->
        exists hist', PresetRoomPos.iface_room_pos sm xs os (i + length [PresetReqAt.HFr (n + cf_head)])%nat H0 hist' S2) ->
     (exists b1 b2, ablocks B lyc Sc = b1 ++ (p - cf_head, n + cf_head) :: b2 /\ ablocks B ly2 S2 = b1 ++ b2) ->
     (exists l1 l2, Lamc = l1 ++ (p, n) :: l2 /\
        prh_ledger B ly2 S2 Hp2 W2 mem2 (l1 ++ l2) peakc cntc SIZE_MAXZ 0 most 0) ->
     (YAkMemnorm.memnorm SEGS (ms_mem ms) -> YAkMemnorm.memnorm SEGS mem2) ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2
       (mkCfg (@YK11.mkst fx' regs2 (Z_to_bv 64 (BASE + (CRT_PC_A + (CRT_FF2_CALL + 4)))) mem2 (YK11.seg_rom SEGS)) md2) QFa) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg ms mdc) QFa.
Proof.
intros fxk Wc E ss ms mdc lyc Sc Hpc kj pos Dx Lamc peakc cntc p n HFZ HS Hrv Hpcs HE2 HL HBR Hra X10 Hp0 Hin HC24 HHB HK.
(* frm_zero's Z.land / Z.shiftr body defeats lia: kept behind a thunk (Crt102Tail.v's ct_J_call does the same) *)
assert (HFZ' : unit -> frm_zero (@YK11.fp_csr fxk)) by (intros _; exact HFZ). clear HFZ.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof YM05.alloc_ceiling_lt as Hc47.
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_side HL) as HSD.
pose proof (crt_side_ledger HSD) as HLc. pose proof (crt_side_room HSD) as HRL.
pose proof (crt_live_lam_perm HL) as HPl. pose proof (crt_live_blocks_perm HL) as HPb.
pose proof HJ as (HARc & HLYc & _).
pose proof HLYc as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof HPRE as ((HAR & Hra0 & Hra4 & Hgp & Htp & Hstk & _) & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & _).
pose proof cl_sp0 as (H16 & Hsp0 & H470). pose proof cl_sp1 as (Hs32 & Hs1).
assert (HinL : In (p, n) Lamc) by (apply (Permutation_in _ (Permutation_sym HPl)); apply in_or_app; left; exact Hin).
destruct (prh_ledger_hblock B lyc Sc Hpc Wc (ms_mem ms) Lamc peakc cntc SIZE_MAXZ 0 p n _ _ HLc HinL) as (Hn0 & Hab & _).
assert (HSTKs : 0 <= @STK_fuzz_free prh_img_A /\ @STK_fuzz_free prh_img_A + 240 <= STKC)
  by (vm_compute; split; discriminate).
destruct (crt102rw_ret (CRT_FF2_CALL + 4) ltac:(unfold CRT_FF2_CALL; lia) ltac:(unfold CRT_FF2_CALL; lia)) as (Hr1 & Hr2 & Hr3).
assert (Hspz : spZ (ms_regs ms) = CRT_sp1 (regs := regs)).
{ unfold spZ. rewrite (crt_bregs_sp HBR). unfold w64. apply unsigned_lit_small. lia. }
assert (Hs0z : s0Z (ms_regs ms) = sp0).
{ unfold s0Z. rewrite (crt_bregs_s0 HBR). unfold w64. apply unsigned_lit_small.
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr. exact Hr. }
assert (Hraz : raZ (ms_regs ms) = BASE + (CRT_PC_A + (CRT_FF2_CALL + 4)))
  by (unfold raZ; rewrite Hra; apply unsigned_lit_small; lia).
refine (crt102rw_call_ch LAWS HPRE fxk (@STK_fuzz_free prh_img_A) (if p =? 0 then [] else ablocks_fp [(p - cf_head, n + cf_head)])
  (CRT_FF2_CALL + 4) (SIGMA AS_fuzz_free) Wc E ss ms mdc lyc Sc Hpc kj pos Dx Lamc peakc cntc 0 0 _ (HFZ' tt) HS Hrv Hpcs HE2 HL
  HBR Hra ltac:(unfold CRT_FF2_CALL; lia) ltac:(unfold CRT_FF2_CALL; lia) (proj1 HSTKs) (proj2 HSTKs) _ _ _).
- (* the footprint: the freed block, taken since the entry *)
  intros a Ha. rewrite (proj2 (Z.eqb_neq p 0) Hp0) in Ha. right; left.
  destruct (crt102rw_fresh LAWS lyc Sc Hpc Wc (ms_mem ms) mdc Dx p n HARc HPb Hin Hn0) as (Hab' & Hnot).
  exists (p - cf_head), (n + cf_head). split; [exact Hab'|]. split; [exact Hnot|].
  destruct Ha as (r & Hr & Ha). destruct Hr as [<- | []]. cbn [fst snd] in Ha. exact Ha.
- (* the callee: the tfuzz_free_specX text at the landing cut (7cdbb61b5fa0). Its trace premise is `admits ..` and its
     post is budgeted at its own trace (PRH_FnAlloc.v:340, :352-353); the trace is a FIXED one of the universe (the
     return site's prh_trace at the observed context, crt102rw_free_trace), so it is admitted at every state
     (YCbqG.admits_ct_fix) and the budgeted post gives the plain one back (PRH_Base.fpost_of_fpostb_fix, at wle': the
     text's run and post are at wle' SEGS RZ_cf, read into the call rule's float form by YCbqG.apost_base_xR_F) *)
  intros ch1 Hch HPRE1.
  assert (Hfix : In (call_trace lyc (pc_free_ra0 (as_code B)) (ms_regs ms) ch1) (as_universe B)).
  { apply (crt102rw_free_trace HCL HCTX lyc (ms_regs ms) ch1 (BASE + (CRT_PC_A + (CRT_FF2_CALL + 4))));
      [rewrite Hspz, Etop; lia | exact Hraz | exact Hs0z | lia | exact Hch |].
    vm_compute. right. left. reflexivity. }
  eapply (YSRrG.SRr'_mono SEGS YGcfRehidePost.RZ_cf).
  + exact (FFREE fxk most 0 lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) mdc ch1 p n Lamc peakc cntc SIZE_MAXZ 0 HPRE1
      (fun _ => HRL) (fun _ => HC24) HHB (admits_ct_fix _ _ _ _ _ _ Hfix) X10 (or_intror HinL) HLc).
  + intros W' c' _ HPo. eapply fpost_of_fpostb_fix in HPo; [|exact Hfix].
    exact (YCbqG.apost_base_xR_F (fx := fxk) (SK := SK) SEGS B PST ARx RZW _ _ _ _ _ _ _ _ _ _ W' c' (HFZ' tt) HPo).
- (* the continuation: the text's p <> 0 post (its second conjunct, the hull use, is not read here) *)
  intros fx' ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HFZ2 HFK2 HJe HJc HP HQ.
  destruct HQ as (HQ & HMN2).
  (* fuzz_free's post (the text's Q, PRH_FnAlloc.tffP_Q) read through its named projections, never by position *)
  apply PRH_FnAlloc.tffP_R_of with (regs' := regs2) (md' := md2) in HQ.
  destruct (PRH_FnAlloc.tffP_arm HQ) as [HA1 | HA2];
    [exfalso; exact (Hp0 (PRH_FnAlloc.tffP1_null (PRH_FnAlloc.tffP_R1_of HA1)))|].
  destruct (PRH_FnAlloc.tffP_R2_of HA2) as (lf1 & lf2 & HR2).
  rewrite (proj2 (Z.eqb_neq p 0) Hp0) in HJc.
  exact (HK fx' ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HFZ2 HFK2 HJe HJc HP (PRH_FnAlloc.tffP_room HQ Hp0)
    (PRH_FnAlloc.tffP_pos_free HQ Hp0) (PRH_FnAlloc.tffP2_ablocks HR2)
    (ex_intro _ lf1 (ex_intro _ lf2 (conj (PRH_FnAlloc.tffP2_lam HR2) (PRH_FnAlloc.tffP2_ledger HR2)))) HMN2).
Qed.

(* ---- C2r's entry state: no region, a0 = 0 (the compare said EQUAL) ---- *)
Definition ss_C2r : sstate := mkSS (CRT_PC_A + (CRT_CMP4_CALL + 4)) cur_atoms [] None (mkFacts [] [cl_cR_eq] []).
Lemma cl_C2r_entry : forall (fxk : YK11.FPState) (Wc : world SEGS) memc rg,
  getr rg 10 = w64 0 ->
  st_ok_pi SEGS VAL (TE regs rg []) ss_C2r
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_A + (CRT_CMP4_CALL + 4)))) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS CL_Bx [] (TE regs rg []) (mrestrict (w_H Wc) memc).
Proof.
intros fxk Wc memc rg R10.
assert (W10 : ew (TE regs rg []) (xr 10) = w64 0) by (unfold xr; rewrite (te_cur regs rg _ 10%bv 10) by reflexivity; exact R10).
split; [|unfold sh_ok; apply Forall_nil].
apply ts_st_ok; [apply te_regs_ok | reflexivity | constructor | exact I |].
split; [exact I|]. split; [|exact I].
split; [|exact I]. unfold acond_ok, cl_cR_eq. cbn [ac_c ac_a ac_b].
rewrite branch_eq_U, U_SLit. rewrite (U_atom _ (xr 10) 0 W10) by lia. reflexivity.
Qed.

(* Cf (+0x6d4), fuzz_free (saved)'s return: saved's block is gone, the walk holds back's and copy's blocks; the room
   position has done pj_write's buffer's free, pj_free (&back) and pj_free (&copy) are left *)
Definition cl_at_Cf (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Dc Lamc : list (Z * Z)) (peakc cset : Z)
  (Dback : list (Z * Z)) (ms : list (list Z * PjTree.jv)) (rg : bvmap 5 word) : Prop :=
  t = PjTree.JObj ms /\ frm_zero (@YK11.fp_csr fxk) /\ fregs_kept_x fx fxk /\
  livea lyc Sc Hpc Wc memc mdc kj pos (Dback ++ Dc) Lamc peakc (cnt + ck_crt_count t cset) 0 0 /\
  0 <= cset <= 3 /\ (In ck_MOD_AT (map fst ms) -> cset = 0) /\
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) tc Dc /\
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) tc Dback /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) 56 /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (frame_addr lyc CRT_CID pos + CRT_OFF_V) 56 /\
  posa Sc ([PresetReqAt.HBulk (PresetReqAt.fo (PresetReqAt.copy_set ms))] ++
           [PresetReqAt.HBulk (PresetReqAt.fo (PresetReqAt.copy_set ms))]) /\
  pj_fdR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc /\
  Permutation (map (fun b => snd b + cf_head) Dc) (PresetReqAtNoMiss.tblk (crt_tree_J (t := t))) /\
  (exists Fc, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D
     (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc Fc /\
   map (fun b => snd b + cf_head) Fc = PresetReqAt.fo (crt_tree_J (t := t))) /\
  (PjTree.depth (crt_tree_J (t := t)) <= DOC_D)%nat /\
  (exists Fb, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D
     (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) Dback Fb /\
   map (fun b => snd b + cf_head) Fb = PresetReqAt.fo tc) /\
  crt_bregs (regs := regs) rg (frame_addr lyc CRT_CID pos) /\
  crt_spill (regs := regs) Wc memc CRT_SP_BACK (frame_addr lyc CRT_CID pos + CRT_OFF_BACK).

Section C2.
Hypothesis KCf : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset Dback ms rg,
  cl_at_Cf fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset Dback ms rg ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk (CRT_FF2_CALL + 4) rg memc mdc) QFa.

(* ---- C2r -> fuzz_free (saved) at +0x6d0 -> Cf: new:764 is not taken (a0 = 0); `mv a0, s6` hands saved to fuzz_free,
   which frees pj_write's buffer (the text's p <> 0 arm); every fact of the walk that fuzz_free's footprint (the
   buffer's allocator block) does not meet is kept ---- *)
Lemma cl_C2r : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg,
  cl_at_C2r fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk (CRT_CMP4_CALL + 4) rg memc mdc) QFa.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg HC.
destruct HC as (HRW & SBK & HBR & R22 & R10).
pose proof HRW as (Et & HFZ & HFK & HL & Hcs & Hcin & Hsv & Hcopy & Hback & Hd8 & Hrad & Hrab & Hrav & Hpos & Hfd & HPcp
  & HFco & Hdep & HPbk & HFbo & Ecap).
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ).
pose proof (crt_live_memnorm HL) as HPM.
destruct (cl_C2r_entry fxk Wc memc rg R10) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TE regs rg [])) by apply te_env.
assert (HE2 : bv_unsigned (ew (TE regs rg []) 2) = sp0) by (rewrite (te_entry regs rg _ 2%bv 2) by reflexivity; reflexivity).
pose (RUN := @crt_run_xw_inv fxk rc SK A_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (YSRrMemnorm.srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)) WS_HJ).
unfold crt_cfg.
paj_run_tok_x_inv RUN HS HJ SHOK HPM CL_SPAN.
all: try (lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
  let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end; apply awr_ok_nil).
apply frame_of_read_only in HF; [|vm_compute; reflexivity].
rewrite HF in HJ, HPM. clear HFr HG.
assert (KB : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms0) r = getr rg r).
{ intros r Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [clkeep HS |]). destruct Hr. }
prreg HS (10%bv : bv 5) Q10. prreg HS (1%bv : bv 5) Q1.
assert (X10 : getr (ms_regs ms0) 10 = w64 saved).
{ rewrite Q10. rewrite ?ew_ewset_other by lia. change 54%nat with (32 + 22)%nat.
  rewrite (te_cur regs rg _ 22%bv 22) by reflexivity. exact R22. }
assert (X1 : getr (ms_regs ms0) 1 = Z_to_bv 64 (BASE + (CRT_PC_A + (CRT_FF2_CALL + 4)))).
{ rewrite Q1. vm_compute. reflexivity. }
lazymatch type of HS with st_ok _ ?E2 _ _ => set (EE := E2) in * end.
assert (HE2' : bv_unsigned (ew EE 2) = sp0) by (unfold EE; rewrite ?ew_ewset_other by lia; exact HE2).
pose proof (cl_bregs_eq rg (ms_regs ms0) _ HBR ltac:(intros r Hr; apply KB; cbv [In] in Hr |- *; tauto)) as HBR1.
pose proof cl_sp0 as (H16 & Hsp0 & H47). pose proof cl_sp1 as (Hs32 & Hs1).
assert (HSTKC : STKC = 27632) by (vm_compute; reflexivity).
pose proof (cl_live_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (CRT_sp1 (regs := regs)) (CRT_sp1 (regs := regs)) HL HJ HB_HJ
  ltac:(clear - Hsp0 Hs1 HSTKC; lia) ltac:(unfold CRT_SP_F; clear; lia) (fun a _ _ => eq_refl) (fun a Ha => Ha) HPM) as HL1.
(* the live state at the run's end (its model), kept at memc for the facts after the call *)
pose proof HL1 as HLm. rewrite <- HF in HL1.
(* the class-24 bound at the call, from the room position *)
destruct (crt_pos_ex Hpos) as (pre & hist & HA).
pose proof (proj2 (PresetRoomCounts.counts_of_room_pos_rl _ _ _ _ _ _ _ (crt_pos_room HA))) as HC24.
assert (Hin : In (saved, cap) (Dback ++ (saved, cap) :: Dc)) by (apply in_or_app; right; left; reflexivity).
(* fuzz_free's hull admission at Sc, paid from the same position under the run bound HOS4 *)
apply (cl_ff_call fxk Wc _ _ ms0 _ lyc Sc Hpc kj pos _ Lamc peakc _ saved cap HFZ HS ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) HE2' HL1 HBR1 X1 X10 Hsv Hin HC24
  (Crt102HullPos.hull_free_of_room_pos _ _ _ _ _ _ _ saved HOS4 (crt_pos_room HA))).
intros fx' ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HFZ2 HFK2 HJe HJc HP HRL2 HTR2 Hab2 (l1 & l2 & ELam & HLED2) HMN2.
rewrite HF in HJc, HMN2.
(* the walk's facts before the call *)
clear HL HL1. rename HLm into HL.
pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPl.
pose proof (crt_live_blocks_perm HL) as HPb.
pose proof (crt_live_dx_apart HL) as HAP.
pose proof (crt_side_ledger HSD) as HLD.
pose proof (crt_side_doc_blocks HSD) as HDL.
pose proof (crt_frame_listed (crt_live_frame HL)) as Hinf.
pose proof HJ as (HARc & _).
set (F := frame_addr lyc CRT_CID pos) in *.
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc _ CRT_CID pos HARc Hinf) as (Fb1 & Fb2 & Fb3).
change (fs_frame_bytes CRT_CID) with 512 in Fb2. fold F in Fb1, Fb2, Fb3.
destruct (cl_nodup_mid Lamc Dback Dc Lam (saved, cap) ltac:(eapply prh_ledger_nodup; exact HLD)
  HPl) as (HnDb & HnDc & HDbDc).
assert (HinL : forall bk, In bk (Dback ++ (saved, cap) :: Dc) -> In bk Lamc).
{ intros bk Hb. apply (Permutation_in _ (Permutation_sym HPl)). apply in_or_app. left. exact Hb. }
assert (HsL : In (saved, cap) Lamc) by (apply HinL; exact Hin).
(* the lists after the call *)
assert (HrmL : forall bk, In bk Lamc -> bk <> (saved, cap) -> In bk (l1 ++ l2)).
{ intros bk Hb Hne. rewrite ELam in Hb. apply in_app_or in Hb as [Hb | [Hb | Hb]];
    [apply in_or_app; left; exact Hb | exfalso; exact (Hne (eq_sym Hb)) | apply in_or_app; right; exact Hb]. }
assert (HDc2 : forall bk, In bk Dc -> In bk (l1 ++ l2)).
{ intros bk Hb. apply HrmL; [apply HinL; apply in_or_app; right; right; exact Hb | intros E; subst bk; exact (HnDc Hb)]. }
assert (HDb2 : forall bk, In bk Dback -> In bk (l1 ++ l2)).
{ intros bk Hb. apply HrmL; [apply HinL; apply in_or_app; left; exact Hb | intros E; subst bk; exact (HnDb Hb)]. }
assert (HDc : forall bk, In bk Dc -> In bk Lamc) by (intros bk Hb; apply HinL; apply in_or_app; right; right; exact Hb).
assert (HDb : forall bk, In bk Dback -> In bk Lamc) by (intros bk Hb; apply HinL; apply in_or_app; left; exact Hb).
assert (HDL2 : forall bk, In bk D -> In bk (l1 ++ l2)).
{ intros bk Hb. apply HrmL; [exact (HDL bk Hb)|]. intros E; subst bk. apply (HAP (saved, cap) Hin Hb). }
assert (HPl2 : Permutation (l1 ++ l2) ((Dback ++ Dc) ++ Lam)).
{ rewrite ELam in HPl. rewrite <- !app_assoc in HPl |- *. cbn [app] in HPl.
  exact (Permutation_app_inv _ _ _ _ _ HPl). }
assert (HPb2 : Permutation (ablocks B ly2 S2) (ablocks B ly S ++ ck_hblks (Dback ++ Dc))).
{ destruct Hab2 as (b1 & b2 & Eb1 & Eb2). rewrite Eb2. rewrite Eb1 in HPb.
  unfold ck_hblks in HPb |- *. rewrite !map_app in HPb |- *. cbn [map fst snd] in HPb.
  rewrite app_assoc in HPb. rewrite app_assoc. exact (Permutation_app_inv _ _ _ _ _ HPb). }
assert (HAP2 : forall bk, In bk (Dback ++ Dc) -> ~ In bk D).
{ intros bk Hb. apply HAP. apply in_app_or in Hb as [Hb | Hb]; apply in_or_app; [left; exact Hb | right; right; exact Hb]. }
(* the footprint: saved's allocator block *)
assert (HFPy : forall a, inFP (ablocks_fp [(saved - cf_head, cap + cf_head)]) a ->
  saved - cf_head <= a < saved - cf_head + req_size (cap + cf_head)).
{ intros a ((b & e) & Hr & Ha). destruct Hr as [Er | []]. injection Er as <- <-. cbn [fst snd] in Ha. exact Ha. }
assert (HFP3 : forall a, inFP (ablocks_fp [(saved - cf_head, cap + cf_head)]) a ->
  a < YM05.alloc_ceiling /\ in_app a 1 /\ ~ (F + 504 <= a < F + 512)).
{ intros a Ha. destruct (cl_hull_app _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HL HsL (HFPy a Ha)) as (H1 & H2 & H3).
  fold F in H3. split; [lia|]. split; [exact H2 | lia]. }
assert (HFPa : forall a, inFP (ablocks_fp [(saved - cf_head, cap + cf_head)]) a -> a < YM05.alloc_ceiling /\ in_app a 1)
  by (intros a Ha; destruct (HFP3 a Ha) as (H1 & H2 & _); split; [exact H1 | exact H2]).
assert (HFP0 : Forall (fun r => 0 < fst r) (ablocks_fp [(saved - cf_head, cap + cf_head)])).
{ constructor; [|constructor]. cbn [fst].
  destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc _ SIZE_MAXZ 0 saved cap _ _ HLD HsL) as (_ & Hab & _).
  destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc Wc memc _ _ _ HARc Hab) as (_ & B4096 & _). lia. }
assert (HFPD : forall a, inFP (ablocks_fp [(saved - cf_head, cap + cf_head)]) a -> ~ pj_footR doc D a)
  by (intros a Ha; exact (cl_hull_off_doc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HL Hin (HFPy a Ha))).
assert (HFPc : forall a, inFP (ablocks_fp [(saved - cf_head, cap + cf_head)]) a -> ~ pj_footR (F + CRT_OFF_COPY) Dc a)
  by (intros a Ha; exact (cl_hull_off_tree _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a CRT_OFF_COPY Dc HL HsL HnDc HDc
        ltac:(unfold CRT_OFF_COPY; lia) ltac:(unfold CRT_OFF_COPY; lia) (HFPy a Ha))).
assert (HFPb : forall a, inFP (ablocks_fp [(saved - cf_head, cap + cf_head)]) a -> ~ pj_footR (F + CRT_OFF_BACK) Dback a)
  by (intros a Ha; exact (cl_hull_off_tree _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a CRT_OFF_BACK Dback HL HsL HnDb HDb
        ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia) (HFPy a Ha))).
(* the live state after the call *)
pose proof (crt102rw_side_call LAWS HPRE HTREE lyc Sc Hpc Wc memc _ kj pos _ Lamc peakc _ 0 0 _ _
  ly2 S2 Hp2 W2 mem2 md2 k1 (l1 ++ l2) peakc _ 0 0 HL HJc HFP0 HFPD HLED2 ltac:(lia) HRL2 HDL2) as HSD2.
pose proof (crt102rw_live_call LAWS HPRE lyc Sc Hpc Wc memc _ kj pos _ Lamc peakc _ 0 0 _ _
  ly2 S2 Hp2 W2 mem2 md2 k1 (Dback ++ Dc) (l1 ++ l2) peakc _ 0 0 HL HJe HJc ltac:(vm_compute; discriminate) HFP3 HSD2
  HPl2 HPb2 HAP2 HMN2) as HL2.
destruct (crt102rw_call_keep LAWS HPRE lyc Sc Hpc Wc memc _ kj pos _ _ ly2 S2 Hp2 W2 mem2 md2 k1 HJ HJc HFPa)
  as (EF2 & KS2 & KSH2).
fold F in EF2, KSH2.
assert (HFr : forall off, 0 <= off -> off + 56 <= 512 -> exists cid0 pos0, In (cid0, pos0) (frames Sc) /\
  frame_addr lyc cid0 pos0 <= F + off /\ F + off + 56 <= frame_addr lyc cid0 pos0 + fs_frame_bytes cid0).
{ intros off H0 H1. exists CRT_CID, pos. split; [exact Hinf|]. change (fs_frame_bytes CRT_CID) with 512. fold F. lia. }
pose proof (crt_live_side HL) as HSDx. pose proof (crt_side_ledger HSDx) as HLDx.
apply (KCf fx' ly2 S2 Hp2 W2 mem2 md2 (kj + k1) pos Dc (l1 ++ l2) peakc cset Dback ms regs2).
unfold cl_at_Cf. rewrite EF2.
refine (conj Et (conj HFZ2 (conj _ (conj HL2 (conj Hcs (conj Hcin (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
  (conj HPcp (conj _ (conj Hdep (conj _ (conj _ _))))))))))))))))).
- intros r0 Hr0. rewrite (HFK2 r0 Hr0). exact (HFK r0 Hr0).
- exact (crt102rw_tree_call LAWS lyc Sc Hpc Wc memc _ kj _ _ ly2 S2 Hp2 W2 mem2 md2 k1 Lamc peakc _ 0 (l1 ++ l2) peakc _ 0
    _ _ Dc HARc HJc HLDx HLED2 (HFr CRT_OFF_COPY ltac:(unfold CRT_OFF_COPY; lia) ltac:(unfold CRT_OFF_COPY; lia))
    HDc HDc2 HFPc Hcopy).
- exact (crt102rw_tree_call LAWS lyc Sc Hpc Wc memc _ kj _ _ ly2 S2 Hp2 W2 mem2 md2 k1 Lamc peakc _ 0 (l1 ++ l2) peakc _ 0
    _ _ Dback HARc HJc HLDx HLED2 (HFr CRT_OFF_BACK ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia))
    HDb HDb2 HFPb Hback).
- exact (proj1 (crt102rw_local_keep Wc W2 memc mem2 F CRT_OFF_BACK ltac:(lia)
    (proj1 (alx_frames SEGS B ARx LAWS lyc Sc Hpc Wc memc _ CRT_CID pos HARc Hinf)) ltac:(lia) KSH2
    ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia)) Hrab).
- exact (proj1 (crt102rw_local_keep Wc W2 memc mem2 F CRT_OFF_V ltac:(lia)
    (proj1 (alx_frames SEGS B ARx LAWS lyc Sc Hpc Wc memc _ CRT_CID pos HARc Hinf)) ltac:(lia) KSH2
    ltac:(unfold CRT_OFF_V; lia) ltac:(unfold CRT_OFF_V; lia)) Hrav).
- exact (cl_pos_ff Sc S2 ms cap Hpos Ecap HTR2).
- exact (crt102rw_fd_call LAWS lyc Sc Hpc Wc memc _ kj _ _ ly2 S2 Hp2 W2 mem2 md2 k1 Lamc peakc _ 0 (l1 ++ l2) peakc _ 0
    _ DOC_D Dc HARc HJc HLDx HLED2 (HFr CRT_OFF_COPY ltac:(unfold CRT_OFF_COPY; lia) ltac:(unfold CRT_OFF_COPY; lia))
    HDc HDc2 HFPc Hfd).
- destruct HFco as (Fc & Hfoc & Efoc). exists Fc. split; [|exact Efoc].
  exact (cl_fo_call _ _ _ _ _ _ kj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HJc HLDx HLED2
    (HFr CRT_OFF_COPY ltac:(unfold CRT_OFF_COPY; lia) ltac:(unfold CRT_OFF_COPY; lia)) HDc HDc2 HFPc Hfoc).
- destruct HFbo as (Fb & Hfob & Efob). exists Fb. split; [|exact Efob].
  exact (cl_fo_call _ _ _ _ _ _ kj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HJc HLDx HLED2
    (HFr CRT_OFF_BACK ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia)) HDb HDb2 HFPb Hfob).
- exact (cl_bregs_eq _ regs2 F HBR1 ltac:(intros r Hr; apply (cl_cs_keep _ _ HP); cbv [In] in Hr |- *; tauto)).
- exact (crt102rw_spill_keep HPRE Wc W2 memc mem2 CRT_SP_BACK _ KS2 ltac:(unfold CRT_SP_BACK; lia)
    ltac:(unfold CRT_SP_BACK; lia) SBK).
Qed.
End C2.

(* ---- pj_free (&back)'s helpers ---- *)
(* a present byte is visible *)
Lemma cl_present_av : forall (H : word -> bool) m a, apresent H m a -> aview SEGS H m a <> None.
Proof. intros H m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate. Qed.
(* the shadow hull of a 56-byte local of the class-3 frame lies in the frame's 64 shadow bytes, which are present *)
Lemma cl_local_hull : forall (H : word -> bool) m F off, 0 <= F -> F mod 32 = 0 -> 32 <= off <= 392 -> off mod 8 = 0 ->
  (forall i, 0 <= i < 64 -> apresent H m (shadow_addr F + i)) -> shadow_hull_vis (aview SEGS H m) (F + off) 56.
Proof.
intros H m F off H0 H32 Ho Ho8 HP s Hs. unfold shadow_addr in *.
assert (HSO : SHADOW_OFF mod 8 = 0 /\ 0 <= SHADOW_OFF) by (split; vm_compute; [reflexivity | discriminate]).
assert (Hi : 0 <= s - (SHADOW_OFF + F / 8) < 64) by lia.
pose proof (HP _ Hi) as Hps. replace (SHADOW_OFF + F / 8 + (s - (SHADOW_OFF + F / 8))) with s in Hps by lia.
exact (cl_present_av H m s Hps).
Qed.
(* two lists of the walk's blocks are apart, by the ledger's NoDup heads *)
Lemma cl_nodup_two : forall (Lamc A B' L : list (Z * Z)), NoDup (map fst Lamc) ->
  Permutation Lamc ((A ++ B') ++ L) -> forall y, In y A -> ~ In y B'.
Proof.
intros Lamc A B' L Hnd HP. apply NoDup_ListNoDup in Hnd.
pose proof (Permutation_NoDup (Permutation_map fst HP) Hnd) as Hn.
rewrite !map_app in Hn. rewrite <- app_assoc in Hn.
intros y HyA HyB. apply (cl_nodup_app _ _ (fst y) Hn (in_map fst _ _ HyA)).
apply in_or_app. left. exact (in_map fst _ _ HyB).
Qed.
(* a callee whose text concludes in the caller-window post at window 0 meets the call rule's float form
   (Crt102Rewrite.v's crt102rw_postW0, restated), at RZW (pj_free's text is fpostWmR at wle') *)
Lemma cl_postW0 : forall (fxk : YK11.FPState) STK FP rgc lyc Sc Hpc Wc memc mdc Q W' c',
  frm_zero (@YK11.fp_csr fxk) ->
  fpostWR (fx := fxk) B ARx SK RZW STK 0 FP rgc lyc Sc Hpc Wc memc mdc Q W' c' ->
  apost_base_xFR (fx := fxk) (SK := SK) SEGS B PST ARx RZW STK FP rgc lyc Sc Hpc Wc memc mdc Q W' c'.
Proof.
intros fxk STK FP rgc lyc Sc Hpc Wc memc mdc Q W' c' HFZ (ly' & S' & Hp' & regs' & mem' & md' & k & Hc & HJ & _ & HPr & HQ).
exists fxk, ly', S', Hp', regs', mem', md', k. rewrite !Z.add_0_r in HJ.
split; [exact Hc|]. split; [exact HFZ|]. split; [intros r _; reflexivity|].
split; [exact HJ|]. split; [exact HPr | exact HQ].
Qed.

(* ---- A pj_free (&back) FROM check_round_trip AT THE REALIGNED sp (+0x6d8): the tpj_free_specX text at n = DOC_D,
   window 0, through the Kit's call rule; back is a 56-byte local of the class-3 frame (crt102rw_frame_slot) holding a
   tree over blocks the walk holds, with its ordered free list. The continuation receives the two journals, the kept
   registers and the text's post. ---- *)
Lemma cl_pjf_call : forall (fxk : YK11.FPState) Wc E ss ms mdc lyc Sc Hpc kj pos Dx Lamc peakc cntc
    (Dt Ft : list (Z * Z)),
  frm_zero (@YK11.fp_csr fxk) ->
  @st_ok SEGS fxk E ss (restrict (w_H Wc) ms) -> ss_resv ss = None -> ss_pc ss = SIGMA AS_pj_free ->
  bv_unsigned (ew E 2) = sp0 ->
  livea lyc Sc Hpc Wc (ms_mem ms) mdc kj pos Dx Lamc peakc cntc 0 0 ->
  crt_bregs (regs := regs) (ms_regs ms) (frame_addr lyc CRT_CID pos) ->
  getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRT_PC_A + (CRT_PJF2_CALL + 4))) ->
  getr (ms_regs ms) 10 = w64 (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) ->
  PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) (ms_mem ms)) (prh_lin Lamc) DOC_D
    (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) Dt Ft ->
  range_addressable (aview SEGS (w_H Wc) (ms_mem ms)) SHADOW_OFF (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) 56 ->
  YGcfRoomLive.ccnt24 Sc <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  (* the text's hull admission (tpj_free_specX, v <> 0 -> hull_budget S []); the caller pays it
     from its run position (PresetHullPay.hull_budget_of_room_pos under HOS4) *)
  PresetHullBudget.hull_budget Sc [] ->
  (forall bk, In bk Dt -> In bk Dx) ->
  (forall (fx' : YK11.FPState) ly2 S2 Hp2 W2 regs2 mem2 md2 k1,
     frm_zero (@YK11.fp_csr fx') -> fregs_kept_x fxk fx' ->
     (exists WS, AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly2 S2 Hp2 W2 mem2 md2 (kj + k1) WS /\
     YCbqGwild.wbudget [] (prh_wk F_check_round_trip) WS) ->
     ajournal_xR (SK := SK) SEGS B PST ARx RZW (@STK_pj_free prh_img_A DOC_D) (CRT_sp1 (regs := regs))
       ((frame_addr lyc CRT_CID pos + CRT_OFF_BACK, frame_addr lyc CRT_CID pos + CRT_OFF_BACK + 56)
        :: ablocks_fp (PRH_FnPj.prhPj_hbl Dt)) lyc Sc Hpc Wc (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
     aregs_preserved (ms_regs ms) regs2 ->
     room_live_cf S2 ->
     (forall (sm : list Z -> Z * Z) (xs : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
        (H0 : list Z) (hist : list YG00.chunk),
        PresetRoomPos.iface_room_pos sm xs os i H0 hist Sc ->
        PRH_Base.prh_run_at sm xs os i (PRH_FnPj.prhPj_free_evs Ft) ->
        exists hist', PresetRoomPos.iface_room_pos sm xs os (i + length (PRH_FnPj.prhPj_free_evs Ft))%nat H0 hist' S2) ->
     (exists Lam', Permutation Lamc (Dt ++ Lam') /\
        Permutation (ablocks B lyc Sc) (PRH_FnPj.prhPj_hbl Dt ++ ablocks B ly2 S2) /\
        prh_ledger B ly2 S2 Hp2 W2 mem2 Lam' peakc cntc SIZE_MAXZ 0 most 0) ->
     (YAkMemnorm.memnorm SEGS (ms_mem ms) -> YAkMemnorm.memnorm SEGS mem2) ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2
       (mkCfg (@YK11.mkst fx' regs2 (Z_to_bv 64 (BASE + (CRT_PC_A + (CRT_PJF2_CALL + 4)))) mem2 (YK11.seg_rom SEGS)) md2) QFa) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg ms mdc) QFa.
Proof.
intros fxk Wc E ss ms mdc lyc Sc Hpc kj pos Dx Lamc peakc cntc Dt Ft HFZ HS Hrv Hpcs HE2 HL HBR Hra X10 HFO HRAb HC24
  HHB HDtx HK.
assert (HFZ' : unit -> frm_zero (@YK11.fp_csr fxk)) by (intros _; exact HFZ). clear HFZ.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof YM05.alloc_ceiling_lt as Hc47.
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_side HL) as HSD.
pose proof (crt_side_ledger HSD) as HLc. pose proof (crt_side_room HSD) as HRL.
pose proof (crt_live_blocks_perm HL) as HPb. pose proof (crt_live_lam_perm HL) as HPl.
pose proof HJ as (HARc & HLYc & _).
pose proof HLYc as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof HPRE as ((HAR & Hra0 & Hra4 & Hgp & Htp & Hstk & _) & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & _).
pose proof cl_sp0 as (H16 & Hsp0 & H470). pose proof cl_sp1 as (Hs32 & Hs1).
assert (HSTKC : STKC = 27632) by (vm_compute; reflexivity).
destruct (crt102rw_ff LAWS lyc Sc Hpc Wc (ms_mem ms) mdc kj pos HJ) as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
assert (Hspz : spZ (ms_regs ms) = CRT_sp1 (regs := regs)).
{ unfold spZ. rewrite (crt_bregs_sp HBR). unfold w64. apply unsigned_lit_small. lia. }
set (F := frame_addr lyc CRT_CID pos) in *.
assert (HSTKs : 0 <= @STK_pj_free prh_img_A DOC_D /\ @STK_pj_free prh_img_A DOC_D + 240 <= STKC)
  by (vm_compute; split; discriminate).
assert (HHV : shadow_hull_vis (aview SEGS (w_H Wc) (ms_mem ms)) (F + CRT_OFF_BACK) 56).
{ apply cl_local_hull; [lia | exact F32 | unfold CRT_OFF_BACK; lia | unfold CRT_OFF_BACK; reflexivity |].
  intros i Hi. exact (proj1 (Fsh i Hi)). }
pose proof (crt102rw_frame_slot LAWS HPRE lyc Sc Hpc Wc (ms_mem ms) mdc kj pos (@STK_pj_free prh_img_A DOC_D) 0
  CRT_OFF_BACK (ms_regs ms) Lamc HJ Hspz (proj1 HSTKs) (proj2 HSTKs) ltac:(unfold CRT_OFF_BACK; lia)
  ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; reflexivity) HRAb HHV) as HSLOT.
refine (crt102rw_call LAWS HPRE fxk (@STK_pj_free prh_img_A DOC_D)
  (if F + CRT_OFF_BACK =? 0 then [] else (F + CRT_OFF_BACK, F + CRT_OFF_BACK + 56) :: ablocks_fp (PRH_FnPj.prhPj_hbl Dt))
  (CRT_PJF2_CALL + 4) (SIGMA AS_pj_free) Wc E ss ms mdc lyc Sc Hpc kj pos Dx Lamc peakc cntc 0 0 _ (HFZ' tt) HS Hrv Hpcs HE2
  HL HBR Hra ltac:(unfold CRT_PJF2_CALL; lia) ltac:(unfold CRT_PJF2_CALL; lia) (proj1 HSTKs) (proj2 HSTKs) _ _ _).
- (* the footprint: back's 56 bytes (a slot of the own frame) and Dt's blocks (taken since the entry) *)
  intros a Ha.
  rewrite (proj2 (Z.eqb_neq (F + CRT_OFF_BACK) 0) ltac:(unfold CRT_OFF_BACK; lia)) in Ha.
  apply inFP_cons in Ha as [Ha | Ha].
  + right; right; left. exists (CRT_CID, pos). split; [left; reflexivity|].
    unfold in_zr, frame_rng. cbn [fst snd]. rewrite crt102rw_fb. fold F. try unfold in_zr in Ha. cbn [fst snd] in Ha.
    unfold CRT_OFF_BACK in Ha. lia.
  + right; left. destruct (cl_fp_hull Dt a Ha) as (bb & kb & Hbb & Hy).
    pose proof (HDtx _ Hbb) as Hbx.
    assert (HbL : In (bb, kb) Lamc) by (apply (Permutation_in _ (Permutation_sym HPl)); apply in_or_app; left; exact Hbx).
    destruct (prh_ledger_hblock B lyc Sc Hpc Wc (ms_mem ms) Lamc peakc cntc SIZE_MAXZ 0 bb kb _ _ HLc HbL) as (Hk0 & _).
    destruct (crt102rw_fresh LAWS lyc Sc Hpc Wc (ms_mem ms) mdc Dx bb kb HARc HPb Hbx Hk0) as (Hab' & Hnot).
    exists (bb - cf_head), (kb + cf_head). split; [exact Hab'|]. split; [exact Hnot | exact Hy].
- (* the callee: the tpj_free_specX text at n = DOC_D, window 0, v = &back; its run and post are at wle'
     (fpostWmR), read into the call rule's float form by cl_postW0 *)
  intros ch1 HPRE1. eapply (YSRrG.SRr'_mono SEGS YGcfRehidePost.RZ_cf).
  + refine (PJFREE fxk most 0 lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) mdc ch1 0 (F + CRT_OFF_BACK) Dt Ft Lamc peakc cntc
      SIZE_MAXZ 0 HPRE1 HCL HRL (fun _ => HC24) (fun _ => HHB) X10 _ _ CfParamsPreset.preset_head_wide HLc).
    * unfold fwin. split; [lia|]. split; [reflexivity|]. split; [rewrite Hspz, Etop; lia|]. intros a Ha. lia.
    * right. split; [unfold CRT_OFF_BACK; lia|]. split; [unfold CRT_OFF_BACK; lia|]. split; [exact HFO | exact HSLOT].
  + intros W' c' _ HPo. exact (cl_postW0 fxk _ _ _ _ _ _ _ _ _ _ W' c' (HFZ' tt) HPo).
- (* the continuation: the text's post (its second conjunct, the hull use, is not read here) *)
  intros fx' ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HFZ2 HFK2 HJe HJc HP HQ.
  destruct HQ as (HQ & HMN2).
  (* pj_free's post (the text's Q, PRH_FnPj.tpfP_Q) read through its named projections, never by position *)
  apply PRH_FnPj.tpfP_R_of with (regs' := regs2) (md' := md2) in HQ. destruct HQ as (Lam' & HQR).
  rewrite (proj2 (Z.eqb_neq (F + CRT_OFF_BACK) 0) ltac:(unfold CRT_OFF_BACK; lia)) in HJc.
  exact (HK fx' ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HFZ2 HFK2 HJe HJc HP (PRH_FnPj.tpfP_room HQR) (PRH_FnPj.tpfP_pos HQR)
    (ex_intro _ Lam' (conj (PRH_FnPj.tpfP_lam HQR) (conj (PRH_FnPj.tpfP_ablocks HQR) (PRH_FnPj.tpfP_ledger HQR))))
    HMN2).
Qed.

(* ---- Cf's entry state: the spill of &back at 0x38(s1) ---- *)
Definition ss_Cf : sstate := mkSS (CRT_PC_A + (CRT_FF2_CALL + 4)) cur_atoms
  [ YP09.mkRegion (Some (xr 9)) 56 64 0 0 [YP09.mkChunk 56 (CVal 8 (SOff (xr 27) 32))] ] None
  (mkFacts [(xr 9, mkAF (2 ^ 46) (2 ^ 47) 5); (xr 27, mkAF 4096 (2 ^ 47 - 512) 5)] [] []).
Lemma cl_Cf_entry : forall (fxk : YK11.FPState) (Wc : world SEGS) memc rg F,
  getr rg 9 = w64 (CRT_sp1 (regs := regs)) -> getr rg 27 = w64 F ->
  2 ^ 46 <= CRT_sp1 (regs := regs) -> CRT_sp1 (regs := regs) + 96 <= 2 ^ 47 -> CRT_sp1 (regs := regs) mod 32 = 0 ->
  4096 <= F -> F + 512 <= CRT_sp1 (regs := regs) -> F mod 32 = 0 ->
  crt_spill (regs := regs) Wc memc CRT_SP_BACK (F + CRT_OFF_BACK) ->
  st_ok_pi SEGS VAL (TE regs rg []) ss_Cf
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_A + (CRT_FF2_CALL + 4)))) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS CL_Bx [] (TE regs rg []) (mrestrict (w_H Wc) memc).
Proof.
intros fxk Wc memc rg F R9 R27 H1 H2 H3 HF0 HF1 HF2 VBK.
unfold crt_spill, CRT_SP_BACK, CRT_OFF_BACK in *.
set (sp1 := CRT_sp1 (regs := regs)) in *.
set (E := TE regs rg []).
assert (W9 : ew E (xr 9) = w64 sp1) by (unfold E, xr; rewrite (te_cur regs rg _ 9%bv 9) by reflexivity; exact R9).
assert (W27 : ew E (xr 27) = w64 F) by (unfold E, xr; rewrite (te_cur regs rg _ 27%bv 27) by reflexivity; exact R27).
assert (UB : forall k v, ew E k = w64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E k) = v)
  by (intros k v Hk Hv; rewrite Hk; apply unsigned_lit_small; exact Hv).
split; [|unfold sh_ok; apply Forall_nil].
apply ts_st_ok.
all: try change (TE regs rg []) with E.
- apply te_regs_ok.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
  apply (ts_rok E _ (xr 9) sp1); [apply UB; [exact W9 | lia] | lia | lia | intros o Ho; lia |].
  repeat apply Forall_cons; try apply Forall_nil.
  apply (ts_chunk E _ _ 56 8 (SOff (xr 27) 32) (F + 32)); [| cbn; lia | cbn; lia | exact VBK].
  rewrite denot_lit_U, (U_atom_off E (xr 27) F 32 W27) by lia. reflexivity.
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !ts_bv_some.
  cbn [zpairwise_disjoint zall_disjoint]. tauto.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite (UB _ _ W9 ltac:(lia)), (UB _ _ W27 ltac:(lia)).
  change (2 ^ 5) with 32. repeat split; lia.
Qed.

(* Cp (+0x6dc), pj_free (&back)'s return: the walk holds copy's blocks only; pj_free (&copy) is all that is left of
   round_trip *)
Definition cl_at_Cp (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Dc Lamc : list (Z * Z)) (peakc cset : Z)
  (ms : list (list Z * PjTree.jv)) (rg : bvmap 5 word) : Prop :=
  t = PjTree.JObj ms /\ frm_zero (@YK11.fp_csr fxk) /\ fregs_kept_x fx fxk /\
  livea lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc (cnt + ck_crt_count t cset) 0 0 /\
  0 <= cset <= 3 /\ (In ck_MOD_AT (map fst ms) -> cset = 0) /\
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) tc Dc /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) 56 /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (frame_addr lyc CRT_CID pos + CRT_OFF_V) 56 /\
  posa Sc [PresetReqAt.HBulk (PresetReqAt.fo (PresetReqAt.copy_set ms))] /\
  pj_fdR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc /\
  Permutation (map (fun b => snd b + cf_head) Dc) (PresetReqAtNoMiss.tblk (crt_tree_J (t := t))) /\
  (exists Fc, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D
     (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc Fc /\
   map (fun b => snd b + cf_head) Fc = PresetReqAt.fo (crt_tree_J (t := t))) /\
  (PjTree.depth (crt_tree_J (t := t)) <= DOC_D)%nat /\
  crt_bregs (regs := regs) rg (frame_addr lyc CRT_CID pos).

Section C3.
Hypothesis KCp : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset ms rg,
  cl_at_Cp fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset ms rg ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk (CRT_PJF2_CALL + 4) rg memc mdc) QFa.

(* ---- Cf -> pj_free (&back) at +0x6d8 -> Cp: `ld a0, 0x38(s1)` hands &back to pj_free, which frees the read-back's
   blocks in back's order (the model's HBulk (fo tc)); every fact of copy and of the frame that pj_free's footprint
   (back's 56 bytes and Dback's blocks) does not meet is kept ---- *)
Lemma cl_Cf : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset Dback ms rg,
  cl_at_Cf fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset Dback ms rg ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk (CRT_FF2_CALL + 4) rg memc mdc) QFa.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset Dback ms rg HC.
destruct HC as (Et & HFZ & HFK & HL & Hcs & Hcin & Hcopy & Hback & Hrab & Hrav & Hpos & Hfd & HPcp & HFco & Hdep & HFbo
  & HBR & SBK).
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ).
pose proof (crt_live_memnorm HL) as HPM.
pose proof (crt_bregs_s1 HBR) as R9. pose proof (crt_bregs_s11 HBR) as R27.
pose proof (crt_live_frame HL) as HFRM. pose proof HJ as (HARc0 & _).
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc0 (crt_frame_listed HFRM)) as (Fb1 & Fb2 & Fb3).
change (fs_frame_bytes CRT_CID) with 512 in Fb2, Fb3.
destruct (alx_frames SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc0 (crt_frame_listed HFRM)) as (F32 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cl_sp0 as (H16 & Hsp0 & H47). pose proof cl_sp1 as (Hs32 & Hs1).
assert (HSTKC : STKC = 27632) by (vm_compute; reflexivity).
pose proof YM05.alloc_ceiling_lt as Hc47.
destruct (cl_Cf_entry fxk Wc memc rg (frame_addr lyc CRT_CID pos) R9 R27
  ltac:(clear - Hsp0 Hs1 HSTKC C1 C2 C3 C4 C5 Hc47; lia) ltac:(clear - Hsp0 Hs1 HSTKC H47; lia) Hs32
  ltac:(clear - Fb1; lia) ltac:(clear - Fb2 Hsp0 Hs1 HSTKC; lia) F32 SBK) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TE regs rg [])) by apply te_env.
assert (HE2 : bv_unsigned (ew (TE regs rg []) 2) = sp0) by (rewrite (te_entry regs rg _ 2%bv 2) by reflexivity; reflexivity).
assert (W27 : ew (TE regs rg []) (xr 27) = w64 (frame_addr lyc CRT_CID pos))
  by (unfold xr; rewrite (te_cur regs rg _ 27%bv 27) by reflexivity; exact R27).
pose (RUN := @crt_run_xw_inv fxk rc SK A_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (YSRrMemnorm.srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)) WS_HJ).
unfold crt_cfg.
paj_run_tok_x_inv RUN HS HJ SHOK HPM CL_SPAN.
all: try (lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
  let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil).
apply frame_of_read_only in HF; [|vm_compute; reflexivity].
rewrite HF in HJ, HPM. clear HFr HG.
assert (KB : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms0) r = getr rg r).
{ intros r Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [clkeep HS |]). destruct Hr. }
prreg HS (10%bv : bv 5) Q10. prreg HS (1%bv : bv 5) Q1.
assert (X10 : getr (ms_regs ms0) 10 = w64 (frame_addr lyc CRT_CID pos + CRT_OFF_BACK)).
{ rewrite Q10. rewrite ?ew_ewset_other by lia.
  change (ew (TE regs rg []) 59) with (ew (TE regs rg []) (xr 27)). rewrite W27. unfold w64.
  rewrite unsigned_lit_small by lia. unfold CRT_OFF_BACK. reflexivity. }
assert (X1 : getr (ms_regs ms0) 1 = Z_to_bv 64 (BASE + (CRT_PC_A + (CRT_PJF2_CALL + 4)))).
{ rewrite Q1. vm_compute. reflexivity. }
lazymatch type of HS with st_ok _ ?E2 _ _ => set (EE := E2) in * end.
assert (HE2' : bv_unsigned (ew EE 2) = sp0) by (unfold EE; rewrite ?ew_ewset_other by lia; exact HE2).
pose proof (cl_bregs_eq rg (ms_regs ms0) _ HBR ltac:(intros r Hr; apply KB; cbv [In] in Hr |- *; tauto)) as HBR1.
pose proof (cl_live_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (CRT_sp1 (regs := regs)) (CRT_sp1 (regs := regs)) HL HJ HB_HJ
  ltac:(clear - Hsp0 Hs1 HSTKC; lia) ltac:(unfold CRT_SP_F; clear; lia) (fun a _ _ => eq_refl) (fun a Ha => Ha) HPM) as HL1.
pose proof HL1 as HLm. rewrite <- HF in HL1.
destruct (crt_pos_ex Hpos) as (pre & hist & HA).
pose proof (proj2 (PresetRoomCounts.counts_of_room_pos_rl _ _ _ _ _ _ _ (crt_pos_room HA))) as HC24.
(* pj_free's hull admission at Sc, paid from the run position under the run bound HOS4 (the
   empty list needs no allowance: nsec [] = 0, tsec [] = 0) *)
assert (HHB : PresetHullBudget.hull_budget Sc []).
{ apply (PresetHullPay.hull_budget_of_room_pos _ _ _ _ _ _ Sc [] HOS4 (crt_pos_room HA)).
  - rewrite PresetHullBudget.hull_nsec_nil, PresetSecTotal.NCALL_value. lia.
  - rewrite PresetHullBudget.hull_tsec_nil, PresetSecTotal.TCALL_value. lia. }
destruct HFbo as (Fb & Hfob & Efob).
pose proof Hfob as Hfob1. rewrite <- HF in Hfob1. pose proof Hrab as Hrab1. rewrite <- HF in Hrab1.
apply (cl_pjf_call fxk Wc _ _ ms0 _ lyc Sc Hpc kj pos _ Lamc peakc _ Dback Fb HFZ HS ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) HE2' HL1 HBR1 X1 X10 Hfob1 Hrab1 HC24 HHB
  ltac:(intros bk Hb; apply in_or_app; left; exact Hb)).
intros fx' ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HFZ2 HFK2 HJe HJc HP HRL2 HTR2 (Lam' & HPerm' & HAbl' & HLED2) HMN2.
rewrite HF in HJc, HMN2.
clear HL HL1. rename HLm into HL.
pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPl.
pose proof (crt_live_blocks_perm HL) as HPb.
pose proof (crt_live_dx_apart HL) as HAP.
pose proof (crt_side_ledger HSD) as HLD.
pose proof (crt_side_doc_blocks HSD) as HDL.
pose proof (crt_frame_listed (crt_live_frame HL)) as Hinf.
pose proof HJ as (HARc & _).
set (F := frame_addr lyc CRT_CID pos) in *.
pose proof (cl_nodup_two Lamc Dback Dc Lam ltac:(eapply prh_ledger_nodup; exact HLD) HPl) as HDbDc.
assert (HinL : forall bk, In bk (Dback ++ Dc) -> In bk Lamc).
{ intros bk Hb. apply (Permutation_in _ (Permutation_sym HPl)). apply in_or_app. left. exact Hb. }
assert (HDc : forall bk, In bk Dc -> In bk Lamc) by (intros bk Hb; apply HinL; apply in_or_app; right; exact Hb).
(* the lists after the call: Lam' = Lamc less back's blocks *)
assert (HPl2 : Permutation Lam' (Dc ++ Lam)).
{ apply (Permutation_app_inv_l Dback). rewrite app_assoc. exact (Permutation_trans (Permutation_sym HPerm') HPl). }
assert (HDc2 : forall bk, In bk Dc -> In bk Lam').
{ intros bk Hb. apply (Permutation_in _ (Permutation_sym HPl2)). apply in_or_app. left. exact Hb. }
assert (HDL2 : forall bk, In bk D -> In bk Lam').
{ intros bk Hb. pose proof (Permutation_in _ HPerm' (HDL bk Hb)) as H1. apply in_app_or in H1 as [H1 | H1]; [|exact H1].
  exfalso. apply (HAP bk); [apply in_or_app; left; exact H1 | exact Hb]. }
assert (HPb2 : Permutation (ablocks B ly2 S2) (ablocks B ly S ++ ck_hblks Dc)).
{ change (PRH_FnPj.prhPj_hbl Dback) with (ck_hblks Dback) in HAbl'.
  apply (Permutation_app_inv_l (ck_hblks Dback)).
  apply (Permutation_trans (Permutation_sym HAbl')). apply (Permutation_trans HPb).
  unfold ck_hblks. rewrite map_app. rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. }
assert (HAP2 : forall bk, In bk Dc -> ~ In bk D) by (intros bk Hb; apply HAP; apply in_or_app; right; exact Hb).
(* the footprint: back's 56 bytes and Dback's blocks *)
set (FP1 := (F + CRT_OFF_BACK, F + CRT_OFF_BACK + 56) :: ablocks_fp (PRH_FnPj.prhPj_hbl Dback)) in *.
assert (HFPw : forall a, inFP FP1 a -> F + CRT_OFF_BACK <= a < F + CRT_OFF_BACK + 56 \/
  exists bb kb, In (bb, kb) Dback /\ bb - cf_head <= a < bb - cf_head + req_size (kb + cf_head)).
{ intros a Ha. unfold FP1 in Ha. apply inFP_cons in Ha as [Ha | Ha].
  - left. try unfold in_zr in Ha. cbn [fst snd] in Ha. exact Ha.
  - right. exact (cl_fp_hull Dback a Ha). }
assert (HFP0 : Forall (fun r => 0 < fst r) FP1).
{ unfold FP1. constructor; [cbn [fst]; unfold CRT_OFF_BACK; lia|].
  apply Forall_forall. intros (b0 & e0) Hb0. unfold ablocks_fp, PRH_FnPj.prhPj_hbl in Hb0.
  rewrite map_map, in_map_iff in Hb0. destruct Hb0 as ((bb & kb) & Eb & Hbb). cbn [fst snd] in Eb |- *.
  injection Eb as <- <-.
  destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc _ SIZE_MAXZ 0 bb kb _ _ HLD
    (HinL _ (in_or_app _ _ _ (or_introl Hbb)))) as (Hk0 & Hab & _).
  destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc Wc memc _ _ _ HARc Hab) as (_ & B4096 & _).
  change (@cf_head CfParams_preset) with 16 in *. lia. }
clearbody FP1.
assert (HFP3 : forall a, inFP FP1 a -> a < YM05.alloc_ceiling /\ in_app a 1 /\ ~ (F + 504 <= a < F + 512)).
{ intros a Ha. destruct (HFPw a Ha) as [Hw | (bb & kb & Hbb & Hy)].
  - unfold CRT_OFF_BACK in Hw. split; [clear - Hw Fb2; lia|].
    split; [apply (in_app_sub _ _ _ _ Fb3); clear - Hw; lia | clear - Hw; lia].
  - destruct (cl_hull_app _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HL (HinL _ (in_or_app _ _ _ (or_introl Hbb))) Hy)
      as (H1 & H2 & H3).
    fold F in H3. split; [lia|]. split; [exact H2 | lia]. }
assert (HFPa : forall a, inFP FP1 a -> a < YM05.alloc_ceiling /\ in_app a 1)
  by (intros a Ha; destruct (HFP3 a Ha) as (H1 & H2 & _); split; [exact H1 | exact H2]).
assert (HFPD : forall a, inFP FP1 a -> ~ pj_footR doc D a).
{ intros a Ha. destruct (HFPw a Ha) as [Hw | (bb & kb & Hbb & Hy)].
  - exact (crt102rw_local_off_doc LAWS HPRE HTREE lyc Sc Hpc Wc memc _ kj pos _ Lamc peakc _ 0 0 CRT_OFF_BACK a
      HL ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia) ltac:(fold F; lia)).
  - exact (cl_hull_off_doc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HL (in_or_app _ _ _ (or_introl Hbb)) Hy). }
assert (HFPc : forall a, inFP FP1 a -> ~ pj_footR (F + CRT_OFF_COPY) Dc a).
{ intros a Ha. destruct (HFPw a Ha) as [Hw | (bb & kb & Hbb & Hy)].
  - intros [Hf | ((b & kb2) & Hb2 & Hf)].
    + unfold CRT_OFF_BACK, CRT_OFF_COPY in *. lia.
    + unfold pj_holdsR in Hf. cbn [fst snd] in Hf.
      assert (HbL : In (b, kb2) Lamc) by exact (HDc _ Hb2).
      destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lamc peakc _ SIZE_MAXZ 0 b kb2 _ _ HLD HbL) as (Hk2 & _).
      assert (Hrq : kb2 + cf_head <= req_size (kb2 + cf_head))
        by (unfold req_size; destruct (Z.eqb_spec (kb2 + cf_head) 0); lia).
      destruct (cl_hull_app _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HL HbL
        ltac:(change (@cf_head CfParams_preset) with 16 in *; lia)) as (_ & _ & H3).
      fold F in H3. unfold CRT_OFF_BACK in Hw. lia.
  - exact (cl_hull_off_tree _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a CRT_OFF_COPY Dc HL (HinL _ (in_or_app _ _ _ (or_introl Hbb)))
      (HDbDc _ Hbb) HDc ltac:(unfold CRT_OFF_COPY; lia) ltac:(unfold CRT_OFF_COPY; lia) Hy). }
(* the live state after the call *)
pose proof (crt102rw_side_call LAWS HPRE HTREE lyc Sc Hpc Wc memc _ kj pos _ Lamc peakc _ 0 0 _ _
  ly2 S2 Hp2 W2 mem2 md2 k1 Lam' peakc _ 0 0 HL HJc HFP0 HFPD HLED2 ltac:(lia) HRL2 HDL2) as HSD2.
pose proof (crt102rw_live_call LAWS HPRE lyc Sc Hpc Wc memc _ kj pos _ Lamc peakc _ 0 0 _ _
  ly2 S2 Hp2 W2 mem2 md2 k1 Dc Lam' peakc _ 0 0 HL HJe HJc ltac:(vm_compute; discriminate) HFP3 HSD2
  HPl2 HPb2 HAP2 HMN2) as HL2.
destruct (crt102rw_call_keep LAWS HPRE lyc Sc Hpc Wc memc _ kj pos _ _ ly2 S2 Hp2 W2 mem2 md2 k1 HJ HJc HFPa)
  as (EF2 & KS2 & KSH2).
fold F in EF2, KSH2.
assert (HFr : forall off, 0 <= off -> off + 56 <= 512 -> exists cid0 pos0, In (cid0, pos0) (frames Sc) /\
  frame_addr lyc cid0 pos0 <= F + off /\ F + off + 56 <= frame_addr lyc cid0 pos0 + fs_frame_bytes cid0).
{ intros off H0 H1. exists CRT_CID, pos. split; [exact Hinf|]. change (fs_frame_bytes CRT_CID) with 512. fold F. lia. }
assert (Etcs : tc = PresetReqAt.copy_set ms) by exact (cm_crt_tree_copy_set_eq t ms Et).
apply (KCp fx' ly2 S2 Hp2 W2 mem2 md2 (kj + k1) pos Dc Lam' peakc cset ms regs2).
unfold cl_at_Cp. rewrite EF2.
refine (conj Et (conj HFZ2 (conj _ (conj HL2 (conj Hcs (conj Hcin (conj _ (conj _ (conj _ (conj _ (conj _
  (conj HPcp (conj _ (conj Hdep _)))))))))))))).
- intros r0 Hr0. rewrite (HFK2 r0 Hr0). exact (HFK r0 Hr0).
- exact (crt102rw_tree_call LAWS lyc Sc Hpc Wc memc _ kj _ _ ly2 S2 Hp2 W2 mem2 md2 k1 Lamc peakc _ 0 Lam' peakc _ 0
    _ _ Dc HARc HJc HLD HLED2 (HFr CRT_OFF_COPY ltac:(unfold CRT_OFF_COPY; lia) ltac:(unfold CRT_OFF_COPY; lia))
    HDc HDc2 HFPc Hcopy).
- exact (proj1 (crt102rw_local_keep Wc W2 memc mem2 F CRT_OFF_BACK ltac:(lia) F32 ltac:(lia) KSH2
    ltac:(unfold CRT_OFF_BACK; lia) ltac:(unfold CRT_OFF_BACK; lia)) Hrab).
- exact (proj1 (crt102rw_local_keep Wc W2 memc mem2 F CRT_OFF_V ltac:(lia) F32 ltac:(lia) KSH2
    ltac:(unfold CRT_OFF_V; lia) ltac:(unfold CRT_OFF_V; lia)) Hrav).
- refine (cl_pos_pjf Sc S2 (PresetReqAt.fo (PresetReqAt.copy_set ms)) _ Fb Hpos _ HTR2).
  rewrite Efob, Etcs. reflexivity.
- exact (crt102rw_fd_call LAWS lyc Sc Hpc Wc memc _ kj _ _ ly2 S2 Hp2 W2 mem2 md2 k1 Lamc peakc _ 0 Lam' peakc _ 0
    _ DOC_D Dc HARc HJc HLD HLED2 (HFr CRT_OFF_COPY ltac:(unfold CRT_OFF_COPY; lia) ltac:(unfold CRT_OFF_COPY; lia))
    HDc HDc2 HFPc Hfd).
- destruct HFco as (Fc & Hfoc & Efoc). exists Fc. split; [|exact Efoc].
  exact (cl_fo_call _ _ _ _ _ _ kj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HJc HLD HLED2
    (HFr CRT_OFF_COPY ltac:(unfold CRT_OFF_COPY; lia) ltac:(unfold CRT_OFF_COPY; lia)) HDc HDc2 HFPc Hfoc).
- exact (cl_bregs_eq _ regs2 F HBR1 ltac:(intros r Hr; apply (cl_cs_keep _ _ HP); cbv [In] in Hr |- *; tauto)).
Qed.
End C3.

(* ---- Cp's entry state: no region ---- *)
Definition ss_Cp : sstate := mkSS (CRT_PC_A + (CRT_PJF2_CALL + 4)) cur_atoms [] None (mkFacts [] [] []).

(* ======================================================================================================== *)
(* X (+0x304): the shared re-poison of back / v, the boundary this slice ends in (crt_at_X, the glue's), at every
   state, its continuation the X seam (Crt102Top.v's crt102_top_X, by Crt102Kit.crt102rw_at_X of the J seam). *)
Section C4.
#[local] Notation Xa := (crt_at_X (fx := fx) (rc := rc) (PI := prh_img_A) (RL := RL) (SK := SK) (L := A_prog_listing)
  (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)).
Hypothesis KX : forall fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r,
  Xa fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk CRT_X_OFF rg memc mdc) QFa.

(* ---- Cp -> X: `mv s6, zero` (the value the function returns, r = 0) and `j` to +0x304: arm C4-full's crt_at_X, the
   join's r = 0 arm with the count cnt + ck_crt_count t cset and the room position at pj_free (&copy) ---- *)
Lemma cl_Cp : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset ms rg,
  cl_at_Cp fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset ms rg ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk (CRT_PJF2_CALL + 4) rg memc mdc) QFa.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset ms rg HC.
destruct HC as (Et & HFZ & HFK & HL & Hcs & Hcin & Hcopy & Hrab & Hrav & Hpos & Hfd & HPcp & HFco & Hdep & HBR).
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ).
pose proof (crt_live_memnorm HL) as HPM.
assert (HS : st_ok_pi SEGS VAL (TE regs rg []) ss_Cp
  (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_A + (CRT_PJF2_CALL + 4)))) memc (YK11.seg_rom SEGS)))).
{ apply ts_st_ok; [apply te_regs_ok | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
assert (SHOK : sh_ok SEGS CL_Bx [] (TE regs rg []) (mrestrict (w_H Wc) memc)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (TE regs rg [])) by apply te_env.
pose (RUNTO := @crt_run_to_xw_inv fxk rc SK A_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (YSRrMemnorm.srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)) WS_HJ).
unfold crt_cfg.
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM CL_SPAN (CRT_PC_A + CRT_X_OFF).
all: try (lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
  let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end; apply awr_ok_nil).
apply frame_of_read_only in HF; [|vm_compute; reflexivity].
rewrite HF in HJ, HPM. clear HFr HG.
assert (KB : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 23; 26; 27]%bv -> getr (ms_regs ms0) r = getr rg r).
{ intros r Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [clkeep HS |]). destruct Hr. }
prreg HS (22%bv : bv 5) Q22.
assert (X22 : getr (ms_regs ms0) 22 = w64 0) by (rewrite Q22; reflexivity).
pose proof (cl_bregs_eq rg (ms_regs ms0) _ HBR KB) as HBR1.
pose proof cl_sp0 as (H16 & Hsp0 & H47). pose proof cl_sp1 as (Hs32 & Hs1).
assert (HSTKC : STKC = 27632) by (vm_compute; reflexivity).
pose proof (cl_live_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (CRT_sp1 (regs := regs)) (CRT_sp1 (regs := regs)) HL HJ HB_HJ
  ltac:(clear - Hsp0 Hs1 HSTKC; lia) ltac:(unfold CRT_SP_F; clear; lia) (fun a _ _ => eq_refl) (fun a Ha => Ha) HPM) as HL1.
rewrite <- HF in HL1, Hcopy, Hrab, Hrav, Hfd, HFco.
pmkst HS.
lazymatch goal with |- context [Z_to_bv 64 (BASE + ?pc)] =>
  replace pc with (CRT_PC_A + CRT_X_OFF) by (vm_compute; reflexivity) end.
assert (Etcs : tc = PresetReqAt.copy_set ms) by exact (cm_crt_tree_copy_set_eq t ms Et).
apply (KX fxk lyc Sc Hpc Wc (ms_mem ms0) _ kj pos Lamc peakc (cnt + ck_crt_count t cset) 0 0 Dc (ms_regs ms0) 0).
refine {| crt_at_X_join := _; crt_at_X_back_open := Hrab; crt_at_X_v_open := Hrav |}.
refine {| crt_at_J_live := HL1; crt_at_J_frm_zero := HFZ; crt_at_J_fregs := HFK; crt_at_J_bregs := HBR1;
  crt_at_J_ret := X22; crt_at_J_copy_fd := Hfd; crt_at_J_r0 := eq_refl; crt_at_J_count := _ |}.
exists cset. split; [exact Hcs|]. split.
{ intros ms' Et' Hin. rewrite Et in Et'. injection Et' as <-. exact (Hcin Hin). }
right. split; [reflexivity|]. split; [reflexivity|]. split; [symmetry; exact HRAN|]. split; [reflexivity|].
split.
{ assert (EJ : crt_evs_J (t := t) = [PresetReqAt.HBulk (PresetReqAt.fo (PresetReqAt.copy_set ms))])
    by (unfold crt_evs_J; rewrite Et; reflexivity).
  rewrite EJ. exact Hpos. }
split.
{ assert (EJt : crt_tree_J (t := t) = tc) by (unfold crt_tree_J, crt_tc; rewrite Et; symmetry; exact (cm_crt_tree_copy_set ms)).
  rewrite EJt. exact Hcopy. }
split; [exact HPcp|]. split; [exact HFco | exact Hdep].
Qed.

(* ---- C: the three final checks and the exit, composed: C -> C1r -> C2r -> Cf -> Cp -> X ---- *)
Lemma cl_C : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg,
  cl_at_C fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk CRT_C_OFF rg memc mdc) QFa.
Proof. exact (cl_C_head (cl_C1r (cl_C2r (cl_Cf cl_Cp)))). Qed.

(* ======================================================================================================== *)
(* THE TAIL OF THE INLINED round_trip_rewrite, L0 .. C .. X: from every crt_at_L0 state (the boundary agreed with
   Crt102Rewrite), QF, given the X seam. L0 -> {L1 (doc->n <> 0), L2 (doc->n = 0)}; the at-search closes by the
   measure length ms - i (cl_L1_loop) into L2; L2 -> {L3 (i = 0), C}; the member loop closes by the same measure
   (cl_L3_loop) into C; C -> X (cl_C). *)
Theorem crt102_loops : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dx Lamc peakc cntc rg ms cset saved rcd,
  L0a fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dx Lamc peakc cntc rg ms cset saved rcd ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk CRT_L0_OFF rg memc mdc) QFa.
Proof.
assert (KL3 : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg bkeys dkeys,
  cl_at_L3 fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg 0 bkeys dkeys ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk CRT_L3_OFF rg memc mdc) QFa).
{ intros fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg bkeys dkeys H.
  exact (cl_L3_loop cl_C (length ms) fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg 0 bkeys dkeys
    (Nat.le_sub_l _ _) H). }
pose proof (cl_L2 KL3 cl_C) as KL2.
assert (KL1 : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg keys,
  cl_at_L1 fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg 0 keys ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfga fxk CRT_L1_OFF rg memc mdc) QFa).
{ intros fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg keys H.
  exact (cl_L1_loop KL2 (length ms) fxk lyc Sc Hpc Wc memc mdc kj pos Dc Lamc peakc cset saved cap Dback ms rg 0 keys
    (Nat.le_sub_l _ _) H). }
exact (cl_at_L0 KL1 KL2).
Qed.
End C4.

End g.
End A.

Print Assumptions crt102_loops.
