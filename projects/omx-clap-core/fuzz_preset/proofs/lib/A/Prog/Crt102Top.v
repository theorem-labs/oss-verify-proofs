(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumC.v, with its module paths and module names changed; 417 of its 458 lines of code are new or changed and 887 lines of the source are left out. *)
(* On the Step-1 contract texts (the re-hiding move):
   the text now concludes `SRr' segs YGcfRehidePost.RZ_cf .. (fpostFbm ..)` (fpostFbm is at wle') and takes the entry
   premise `(length rp_os <= 4)%nat` (HOS4, after ck_frm0). So the three stretch statements CRT_A_AT_J / _U / _X
   conclude YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf, crt_A_under takes HOS4 in the text's place, and HOS4 is handed to
   Crt102Arms.arms_at_M (by name), Crt102Rewrite.crt102rw_chain and Crt102Loops.crt102_loops (positional) and
   Crt102Tail.crt102_tail (by assumption). The post bridge runs under YSRrG.SRr'_mono. The callee texts RTT / PJFREE /
   PJSTR / PJSET / PJWRITE / PNOTING were taken at every universe closure; each is used only at the text's own CTX0, so
   Sections f and a now take CTX0 as a Variable and each text at it (the tops conclude at that CTX0). *)
(* fuzz_preset, slice Crt102Top: THE COMPOSITION of the walk of check_round_trip
   (fuzz_preset.c new:772-781, round_trip_rewrite new:715-769 inlined) into the contract text tcheck_round_trip_specX
   (lib/A/PRH_FnCheck.v, Section c :416, the definition at its end), image A' (asan pin 1be0f53d96cb9d6c, unstripped
   twin bff8519bbe3ea0e4).

   base: commit 2fdcfd7be069 (post-landing line).
   STATUS AT THE kb ROUND (the walk owner's brief, the internal file wild-budget-kb-reshape.md; the text
   PRH_FnCheck.v:1310-1390: no rp_sm binder, keyed on ReaderRes.jr_strtod, the wild room `wild_room (as_universe B) []
   (prh_wk F_check_round_trip) (st_depot S)` at :1366, a BUDGETED post fpostFbm .. (wbudget [] (prh_wk
   F_check_round_trip))). Every closed piece is its own Qed lemma. The named antecedent CRT_A_WILD_BUDGET is
   DISCHARGED (crt102_top_wild_budget, from the text's wild room, now a premise of crt_A_under). AT THE STEP-1 RULING
   (on 1409ad6e7e37) the Record CRT_A_OPEN_RW's four goals are proved at their sources in Crt102Rewrite (the callee
   texts' dead-arm conjuncts; pj_set's FREEORD-COPY conjunct carried K -> N) and RETIRED with the Record and
   CRT_A_SEAM_OPEN_RW, so THE CONTRACT IS Qed (crt102_top, crt102_top_TfibA); crt102_top_open / crt102_top_open_TfibA,
   the contract modulo that Record, are the same statements and are retired. Before the kb round the contract
   theorems were ABORTED at CRT_A_WILD_BUDGET (the walk owner's 11:54Z ruling for the B' twin, applied to A' at 14:44Z:
   an implication from an antecedent that may be false is provable and asserts nothing about the program).
   - crt102_top_J        Qed: the J seam, CLOSED by Crt102Tail.crt102_tail.
   - crt102_top_X        Qed: the X seam (the end of the rewrite / loops chain), by crt102_top_X_J of crt102_top_J.
   - crt102_top_X_J      Qed: the J seam gives the X seam, by Crt102Kit.crt102rw_at_X.
   - crt102_top_of       Qed, AN IMPLICATION CRT_A_WILD_BUDGET -> CRT_A_SEAM_U -> the contract, generic in B and in the
                         text's a_mod_at / a_stamp. By Crt102Entry.crt102_entry (entry .. M), whose continuation is
                         discharged by Crt102Arms.arms_at_M (Qed; M .. R1 / R2 / T into J or U; C1 / C2 unreachable,
                         rtt's r = 1 arm dead; rtt1's copy bridge closed inside it by Crt102Arms.arms_rtt_bridge from the
                         cut's own copy-arm conjuncts) with the J seam closed (crt102_top_J), the U seam as an
                         antecedent, arms_at_M's trailing premise arms_wild_budget given by CRT_A_WILD_BUDGET, and the
                         post bridge QF -> the text's budgeted post (kb round: QF is that post at the glue's journal budget,
                         the inner memnorm keep dropped).
   - crt102_top_of_TfibA Qed: the same at the A' INSTANCE B := AD2l.TfibB, Crt102Entry's four image stand-ins
                         discharged (PALibA.palib_A, crt102_uar_img_TfibA, Crt102AF0lCheck.crt102_af0l_stack_malloc3,
                         Crt102PALibCheck.crt102_tfib_pst_static_A).
  - crt102_top_U        Qed, AN IMPLICATION CRT_A_WILD_BUDGET -> CRT_A_SEAM_U at the text's instance
                        (a_mod_at := CRT_MOD_AT_A, a_stamp := CRT_STAMP_A), by Crt102Rewrite.crt102rw_chain (U .. L0),
                        its parse_noting gap Crt102Rewrite.crt102rw_wild_budget_pn given by CRT_A_WILD_BUDGET, its L0
                        continuation supplied by Crt102Loops.crt102_loops (L0 .. X, Qed) at crt102_top_X / J.
  - crt102_top_wild_budget Qed: CRT_A_WILD_BUDGET, by Crt102Arms.arms_wild_budget_goal and
                        Crt102Rewrite.crt102rw_wild_budget_pn_goal from the text's wild room (kb round).
  - crt102_top / crt102_top_TfibA: THE CONTRACT. Qed.
  THE OPEN SET: empty. What it held, each with its close:
    CLOSED at the kb round: CRT_A_WILD_BUDGET (crt102_top_wild_budget). Before it, as found at the landing cut 7cdbb61b5fa0:
    CRT_A_WILD_BUDGET (THE A' TWIN OF Crt102TopB's CRT_B_WILD_BUDGET, retired on B' at the kb round; route: the kb re-shape,
     the walk owner's brief, the internal file wild-budget-kb-reshape.md), under the text's premises, the
      conjunction of
      Crt102Arms.arms_wild_budget (the A' twin of Crt102B_RRT.crtb_wild_budget): at every live state of the walk,
        `wild_room (as_universe B) [] (prh_wk F_round_trip_text) (st_depot Sc)` and, for every WS1 with
        `wbudget [] (prh_wk F_round_trip_text) WS1`, rtt's budgeted journals `AJW .. WS1` (the caller's and the
        callee's) as the glue's AJ;
      Crt102Rewrite.crt102rw_wild_budget_pn (its parse_noting twin): at every live state,
        `wild_room (as_universe B) [] (prh_wk F_parse_noting) (st_depot Sc)` and parse_noting's budgeted journal
        `AJW .. WS1` (wbudget [] (prh_wk F_parse_noting) WS1) as AJ.
      MEASURED: the only budgeted call rule (YCbqGwild.aj_call_xbF / _sp, YCbqGwild.v:721-788) leaves the caller at
      AJW .. (WS0 ++ WS1), never at AJ; the glue (Crt102Glue.v) keeps crt_live_journal at AJ and QF at fpostFm and
      states no room, and nothing at the cut bounds WS1 to [].
    CLOSED at the Step-1 ruling: CRT_A_SEAM_OPEN_RW, the Record CRT_A_OPEN_RW, one field per goal, each proved at
    its source in Crt102Rewrite and retired:
      crt_A_open_pjstring     OPEN_K0_DEAD_PJSTRING: pj_string's refused arm at +0x24c (crt102rw_at_U).
      crt_A_open_pjset        OPEN_K0_DEAD_PJSET: pj_set's res = -1 arm at +0x278 (crt102rw_G_taken).
      crt_A_open_pjwrite      OPEN_K0_DEAD_PJWRITE: pj_write's refused arm at +0x2b0 (crt102rw_Wgo).
      crt_A_open_freeord_copy OPEN_K0_FREEORD_COPY: copy's ordered free list after pj_set (crt102rw_copy_fo).
      RETIRED at the cut: crt_A_open_src_ceil (OPEN_K0_SRC_CEIL, `q + len + 8 <= alloc_ceiling` at parse_noting: the
      cut's src_rd asks `q + len <= alloc_ceiling`, PRH_Base.v:1660, which the harness block holding the text gives
      at the call) and crt_A_open_univ_end (OPEN_K0_UNIV_END, the landing cut takes no DW).
    RETIRED at the cut: CRT_A_SEAM_RTT_COPY / CRT_A_RTT_COPY (rtt1's copy bridge): the cut's tround_trip_text_specX
      copy arm states FREEORD-COPY and pj_ncapR (PRH_FnCheck.v:1290-1301), and Crt102Arms.arms_rtt_bridge proves
      the bridge from them (CAP (pj_ncapR) through Crt102Glue.crt_copy_cap_of_ncap48).
    crt102rw_L0K is NOT open: Crt102Loops.crt102_loops supplies it.
   VACUITY, the walk owner's sentence, to travel with every green result: this statement goes through prh_univ_closure,
     whose clause 4 is false on B' for data words; it is vacuous at its instance until the texts' batch lands the 4a / 4b
     split (4a: the code word stays a fixed In; 4b: inU (as_universe B) (prh_trace pc_free_ra0 r [w])) and removes
     DW. This file discharges no universe fact: the text's prh_univ_closure B CTX0 is a pass-through premise of
     every statement here, and DW leaves these statements at that rebind. At A' the cursor frees read the code word
     only (the walk owner's finding), so this A' file's vacuity closes with the split.

   THE STATEMENT. crt102_top is the text at image A': L := A_prog_listing, PA := PI_prog_A, PI := prh_img_A,
   ci := CfImg_A, cp := CfParams_preset, RL / fx / rc / SK the Section's, B ARx free (crt102_top_TfibA: B := TfibB,
   ARx free), at the instance the text's own comment names for its two string arguments (the image strings .str.10 /
   .str.30): a_mod_at := CRT_MOD_AT_A, a_stamp := CRT_STAMP_A (Crt102Img.v :613-614, pa_val of the listing). The binary
   reads the two literals at those fixed addresses, so the text is true at them only (this walk's ruling,
   2026-10-29). crt102_top_of and the seams stay generic in a_mod_at / a_stamp: they pass them through.

   SECTION HYPOTHESES (each with its owner; they are listed again at each one):
     LAWS  (AR_laws_x at cf_head)         engine fold YCbqG c3b5d0111037; at ARcf YGcallcf.AR_laws_x_cf.
     ASM3  (astack_malloc_realizes_xm 3)  the frame-class lane (FCm3s.v pays the _xm contracts at the instance).
     OWNLOW (ARx_owned_low_law)           engine (YGcallx.v); at ARcf owned_low_cf.
     AMS   (aintrin_realizes_xm OSet at the listing's __asan_memset) the libc row (po_asan_memset_cf).
     RTT   (tround_trip_text_specX at the Section's CTX0, every float state)  the contract text; it has its own walk.
     ASFX / FFLX / SFX  (aj_flag_store_x's three, Crt102Tail's)  engine: YG0dcf astack_free_law_cf,
                                          AR_flag_law_ok_cf / AR_client_img_law_ok_cf, YGcallScf stack_free_x_any.
     FFLP  (the frame's flag byte present, Crt102Tail's)  AR_flag_law_ok_cf's first conjunct.
     SETSH (aset_shadow_realizes_xm at __asan_set_shadow_f5, 0xf5, Crt102Tail's)  the frame-class lane.
     PJFREE (tpj_free_specX at the Section's CTX0, every float state, Crt102Tail's)  the contract text
                                         (PRH_FnPj.v dc0d0aa79c0f).
     PAL, pal_uar_img, pal_stack_malloc3, pal_pst_static (crt102_top_of / crt102_top, generic B)  the image
                                         binding of B; NOT hypotheses at the A' instance (crt102_top_of_TfibA).
    zs_aligned (as_zero_shadow B 8-aligned) MARKED STAND-IN (the image binding of B); Crt102Rewrite's /
                                         Crt102Loops' (from Crt102Kit's crt_cstr_img).
    img_shadow_vis_x (the image band's shadow is present under ARx) MARKED STAND-IN.
    PJSTR / PJSET / PJWRITE / PNOTING (tpj_string / tpj_set / tpj_write / tparse_noting at the Section's CTX0, every float
                                         state), RANOUT (tfuzz_alloc_ran_out), SAME (tsame), FFREE (tfuzz_free):
                                         the contract texts.
    STRLEN / STRCMP (astrlen / astrcmp_realizes_xrom at the listing's __wrap_strlen / __wrap_strcmp)  the libc rows.

  INPUTS OF RECORD (taken by path; base commit 99138946d790):
  - the contract texts at the kit tip of record 3ac20a5c9e30: lib/A/PRH_FnCheck.v 0844ed8c0608, PRH_Base.v
    ee2f5cd7ed35, PRH_FnPj.v dc0d0aa79c0f, PRH_FnWriter.v 98737c36ea08, PRH_FnAlloc.v 95e26ff95e63, PRH_FnEx.v
    45ddb7a7d5ae; model lib/Spec/PresetReqAt.v 43c958024221; CfParamsPreset.v b60d0f63c926 (of record).
  - engine of record at s1b bb085d091bbe (YCbqG.v c3b5d0111037, YGcallMxmn.v b47cf7942c3d).
  - listing v3 (commit 74dcda1eda12): lib/A/Listing_prog.v 7ed1529926bd, lib/A/PAImg_prog.v
    505a51ff7d08; image files: AF0l dfca6bb1a8d7, AF0m 97f423adf6eb, PRH_Img 934516a622e8, YImgTop d2a97d3111ce.
  - the lane's files (all on the glue's Records): Crt102Glue.v d65f66b784a1, Crt102Img.v 176eec830b61, Crt102Entry.v
    6cd098c3ba17, Crt102Arms.v 605107281144, Crt102Kit.v fb64ea6c3126, Crt102AF0lCheck.v 76548b0b655e, Crt102Tail.v
    d38ea142ecbc, Crt102Rewrite.v c56e5c84cf47, Crt102Loops.v f781285e67bc, Crt102PALibCheck.v 405c59509186; the A'
    instance: lib/A/AD2l.v eb321db7a357, lib/A/PALibA.v 88c72c8175cf (by path from commit
    83ac1a932a8d). PresetCfnA is in the closure (through the text and Crt102Loops) and is NOT cited here.
   - build route pins102: the internal file zfb-targets.85055e6079bccb28.sh (self-hashing), FACTS 8f3e7e1a07f1,
     PAU pau-preset-102.
   - rule 24: no function proved (RULE24.md (sha256 96ef6f3404f0; internal record) on the lane base: census-1 sweep complete, 14980 refs,
     7934 hit refs, 1479 files, 0 errors, positive control OK; the ACrt* / BCrt* walks are old-pin, entry 0x82550;
     released refs carry plain / ubsan proofs only; proof-index check_round_trip, exit 0,
     an internal record of that lookup). Written new.

   NUMERALS. ADDRESS: none (the two string addresses are Crt102Img's CRT_MOD_AT_A / CRT_STAMP_A, pa_val of the
   listing; every code address is pa_sigma of the listing). LENGTH, as the text states them: 3 * 2 ^ 20, 3, 56, 54
   (the text's length bounds), 2 ^ 62 - 2 ^ 30 (its count bound), 10 (the a0 register index). WORD: 0 (the flags at
   entry), 3 (frame class 3, as Crt102Entry states pal_stack_malloc3). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm YCbqGcallW YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Img CfImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_PjOrder PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AF0m AD2l PALibA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1ImgA Crt102Glue Crt102Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Crt102Entry Crt102Arms Crt102Kit Crt102Tail Crt102AF0lCheck Crt102PALibCheck.
(* the re-hiding move, used qualified: YA0nH (SRr'), YSRrG (SRr'_mono), YGcfRehidePost (RZ_cf) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost YSRrG.
(* the U composition's two slices (Crt102Rewrite: U .. L0 by crt102rw_chain; Crt102Loops: L0 .. X by crt102_loops) and
   the callee texts their Section hypotheses name; all used qualified *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnWriter PRH_FnAlloc PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Crt102Rewrite Crt102Loops.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance CfImg_A.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_A.
Context {SK : YI16.sink_head} {RL : PrhRoomLive}.
#[local] Notation PA := (PI_prog_A).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation PST := (@prh_pst prh_img_A).
#[local] Notation STKC := (@STK_check_round_trip prh_img_A).
#[local] Notation CFG := (crt_cfg (rc := rc) (L := A_prog_listing) (PA := PA) (CRT_PC := CRT_PC_A)).
#[local] Notation RLO := (@pa_relro_lo _ A_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ A_prog_listing PA).

Section f.
(* B and ARx are Context, so every use of this file's names outside the Section names them *)
Context {B : asyms}.
Context {ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop}.

(* ---- THE STRETCH STATEMENTS at image A' (the B' shape, Crt102Glue's CRT_B_AT_X / _C / _L3 / _L0): from any state a cut
   describes, at any float state fxk, the run reaches QF. The contract's binders are Context, so every use names
   them; the entry float state is the Section's fx, passed by name to every predicate that takes one. ---- *)
Section s.
Context {rp_sm : list Z -> Z * Z} {rp_x : list Z} {rp_os : list (option nat * option nat * option nat)}
  {rp_i : nat} {rp_H0 : list Z}.
Context {ly : alayout} {S : astate} {Hp : list Z} {W : world SEGS} {regs : bvmap 5 word}
  {mem : word -> option byte} {md : Model} {doc : Z} {t : PjTree.jv} {D : list (Z * Z)} {Lam : list (Z * Z)}
  {peak cnt ran most : Z}.
#[local] Notation QFA := (QF (fx := fx) (rc := rc) (PI := prh_img_A) (RL := RL) (SK := SK) (L := A_prog_listing)
  (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)).

(* J (+0x340), the join *)
Definition CRT_A_AT_J : Prop :=
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r,
  crt_at_J (fx := fx) (rc := rc) (PI := prh_img_A) (RL := RL) (SK := SK) (L := A_prog_listing) (PA := PA) (B := B)
    (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
    (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
    (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)
    fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (CFG fxk CRT_J_OFF rg memc mdc) QFA.

(* U (+0x1e4), the head of the inlined round_trip_rewrite *)
Definition CRT_A_AT_U : Prop :=
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms,
  crt_at_U (fx := fx) (rc := rc) (PI := prh_img_A) (RL := RL) (SK := SK) (L := A_prog_listing) (PA := PA) (B := B)
    (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
    (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
    (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)
    fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (CFG fxk CRT_U_OFF rg memc mdc) QFA.

(* X (+0x304), the shared re-poison of back / v *)
Definition CRT_A_AT_X : Prop :=
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r,
  crt_at_X (fx := fx) (rc := rc) (PI := prh_img_A) (RL := RL) (SK := SK) (L := A_prog_listing) (PA := PA) (B := B)
    (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
    (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
    (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)
    fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (CFG fxk CRT_X_OFF rg memc mdc) QFA.

End s.

(* ---- tcheck_round_trip_specX's binders and premises at A' (the landing cut's PRH_FnCheck.v:1310-1390 with the
   4b8f95c0455c conjunct, the text's order), in front of a conclusion K at the binders K reads, with TWO differences,
   both in the conclusion's favour: the run's strtod model is a binder rp_sm with the tie `rp_sm =
   ReaderRes.jr_strtod` where the text writes ReaderRes.jr_strtod (crt102_top_of instantiates it at
   ReaderRes.jr_strtod and the tie by reflexivity: the lane's slices keep crt_pos's rp_sm); and the text's last
   premise `YGcallStackUp.astack_up_x segs ly W (spZ regs) mem` (:1390) is left out (no seam reads it: crt102_top_of
   hands it straight to Crt102Arms.arms_at_M's Section hypothesis HUP0). The text's wild-room premise (:1366) is
   taken (kb round), in the text's place after ck_frm0: CRT_A_WILD_BUDGET is discharged from it
   (crt102_top_wild_budget). The text's new entry premise `(length rp_os <= 4)%nat` (HOS4,
   PRH_FnCheck.v:2363) is taken in the text's place, between ck_frm0 and the wild room. crt102_top_of hands the text's
   own premises to it, so any other premise here does not typecheck there. ---- *)
Definition crt_A_under (CTX0 : list (list Z)) (a_mod_at a_stamp : Z)
  (K : (list Z -> Z * Z) -> list Z -> list (option nat * option nat * option nat) -> nat -> list Z ->
       alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model ->
       Z -> PjTree.jv -> list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> Z -> Prop) : Prop :=
  forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
    (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk),
  forall (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (ch : list (Z * Z * Z)) (doc : Z) (t : PjTree.jv) (D : list (Z * Z)) (x : list Z)
    (Lam : list (Z * Z)) (peak cnt ran most : Z),
  fpre (fx := fx) (PA := PA) B ARx STKC ly S Hp W regs mem md ch ->
  YAkMemnorm.memnorm SEGS mem ->
  prh_univ_closure B CTX0 -> prh_ctx CTX0 F_check_round_trip (raZ regs :: spine ch) ->
  getr regs 10 = w64 doc ->
  ck_tree_ok (PA := PA) ly S Lam W mem doc t D ->
  ck_read x = Some t -> Z.of_nat (length x) <= 3 * 2 ^ 20 ->
  kept_img B a_mod_at (Z.of_nat (length ck_MOD_AT) + 1) -> kept_img B a_stamp (Z.of_nat (length ck_STAMP) + 1) ->
  PjWriteHyp.wlen t false <= 3 * Z.of_nat (length x) -> PjWriteHyp.wlen t true <= 56 * Z.of_nat (length x) - 54 ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran most 0 -> cnt < 2 ^ 62 - 2 ^ 30 ->
  prh_run_at rp_sm rp_x rp_os rp_i (PresetReqAt.round_trip rp_sm t) ->
  ran = 0 ->
  RQA_crt t <= most ->
  blocks_bytes S + LIVE_check_round_trip t <= LIVE_MAX -> RQ_crt t + cf_head < cf_malloc_max ->
  Z.of_nat (length (frames S)) <= ck_FRAMES_CAP - FR_check_round_trip ->
  room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S -> ck_frm0 (fx := fx) ->
  (length rp_os <= 4)%nat ->
  YCbqGwild.wild_room (as_universe B) [] (prh_wk F_check_round_trip) (st_depot S) ->
  rp_sm = ReaderRes.jr_strtod ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (PresetReqAt.round_trip rp_sm t)) ->
  K rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md doc t D Lam peak cnt ran most.

(* ---- THE SEAMS J, U and X, each a stretch statement under the text's premises ---- *)
Definition CRT_A_SEAM_J (CTX0 : list (list Z)) (a_mod_at a_stamp : Z) : Prop :=
  crt_A_under CTX0 a_mod_at a_stamp
    (fun rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md doc t D Lam peak cnt ran most =>
     CRT_A_AT_J (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (ly := ly) (S := S)
       (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D) (Lam := Lam)
       (peak := peak) (cnt := cnt) (ran := ran) (most := most)).
Definition CRT_A_SEAM_U (CTX0 : list (list Z)) (a_mod_at a_stamp : Z) : Prop :=
  crt_A_under CTX0 a_mod_at a_stamp
    (fun rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md doc t D Lam peak cnt ran most =>
     CRT_A_AT_U (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (ly := ly) (S := S)
       (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D) (Lam := Lam)
       (peak := peak) (cnt := cnt) (ran := ran) (most := most)).
Definition CRT_A_SEAM_X (CTX0 : list (list Z)) (a_mod_at a_stamp : Z) : Prop :=
  crt_A_under CTX0 a_mod_at a_stamp
    (fun rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md doc t D Lam peak cnt ran most =>
     CRT_A_AT_X (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (ly := ly) (S := S)
       (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D) (Lam := Lam)
       (peak := peak) (cnt := cnt) (ran := ran) (most := most)).
(* ---- THE WILD-BUDGET ANTECEDENT, THE A' TWIN OF Crt102TopB's CRT_B_WILD_BUDGET (retired on B' at the kb round; route: the kb re-shape, brief
   of the walk's owner, the internal file wild-budget-kb-reshape.md), under the text's premises: rtt's
   (Crt102Arms.arms_wild_budget, the twin of Crt102B_RRT.crtb_wild_budget, the trailing premise of
   Crt102Arms.arms_at_M) and parse_noting's (Crt102Rewrite.crt102rw_wild_budget_pn, a premise of crt102rw_chain),
   both in the kb form. DISCHARGED by crt102_top_wild_budget (kb round) from the text's
   wild-room premise, through Crt102Arms.arms_wild_budget_goal and Crt102Rewrite.crt102rw_wild_budget_pn_goal. ---- *)
Definition CRT_A_WILD_BUDGET (CTX0 : list (list Z)) (a_mod_at a_stamp : Z) : Prop :=
  crt_A_under CTX0 a_mod_at a_stamp
    (fun rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md doc t D Lam peak cnt ran most =>
     Crt102Arms.arms_wild_budget (rc := rc) (SK := SK) (RL := RL) B ARx ly S Hp W regs mem md doc t D Lam peak ran most
     /\ Crt102Rewrite.crt102rw_wild_budget_pn (rc := rc) (RL := RL) (SK := SK) B ARx ly S Hp W regs mem md doc t D Lam
          peak most).

(* ---- THE WILD BUDGET, DISCHARGED (kb round): under the text's premises, its wild room at entry (`wild_room (as_universe
   B) [] (prh_wk F_check_round_trip) (st_depot S)`, PRH_FnCheck.v:1366) gives both conjuncts: rtt's by
   Crt102Arms.arms_wild_budget_goal and parse_noting's by Crt102Rewrite.crt102rw_wild_budget_pn_goal (each Qed, the
   arithmetic of YCbqGwild.ajournal_xw_room / wild_room_le / wbudget_app at the per-boundary kb). ---- *)
Lemma crt102_top_wild_budget : forall CTX0 a_mod_at a_stamp, CRT_A_WILD_BUDGET CTX0 a_mod_at a_stamp.
Proof using.
intros CTX0 a_mod_at a_stamp. unfold CRT_A_WILD_BUDGET, crt_A_under.
intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc t D x Lam peak cnt ran most
  HPRE HMN HCL HCTX H10 HTREE HREAD HLENX HKM HKS HWL0 HWL1 HLED HCNT HRUN HRAN HRQA HLIVE HRQ HFRM
  HROOM HIFC HFRM0 HOS4 HWR HSM HCONS.
cbv beta. split.
- eapply Crt102Arms.arms_wild_budget_goal. exact HWR.
- eapply Crt102Rewrite.crt102rw_wild_budget_pn_goal. exact HWR.
Qed.

(* ---- SECTION HYPOTHESES, each with its owner ---- *)
(* the allocator laws at the cf instance's head (engine fold, YCbqG c3b5d0111037; at ARcf YGcallcf.AR_laws_x_cf);
   Crt102Entry, Crt102Arms and Crt102Kit take the same *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* frame class 3 with the memnorm keep (owner: the frame-class lane, FCm3s.v); Crt102Entry's ASM3 *)
Hypothesis ASM3 : YGcallMxmn.astack_malloc_realizes_xm (fx := fx) SEGS B ARx 3.
(* runtime-owned bytes below the ceiling (engine, YGcallx.v; at ARcf owned_low_cf); Crt102Entry's OWNLOW *)
Hypothesis OWNLOW : ARx_owned_low_law SEGS B ARx.
(* __asan_memset (OSet) at the listing's own pc with the memnorm keep (owner: the libc row,
   po_asan_memset_cf); Crt102Entry's AMS *)
Hypothesis AMS : YGcallMxmn.aintrin_realizes_xm (fx := fx) SEGS B ARx OSet (SIGMA AS___asan_memset).
(* the universe closure of the text's call (tcheck_round_trip_specX's CTX0). Every callee text below (RTT, PJFREE, PJSTR,
   PJSET, PJWRITE, PNOTING) is used only at this CTX0, so each is taken at it (before, each was taken at every
   closure) *)
Variable CTX0 : list (list Z).
(* round_trip_text's contract text (PRH_FnCheck.v 0844ed8c0608; it has its own walk), at CTX0 and every float
   state: Crt102Arms' RTT *)
Hypothesis RTT : forall fxk : YK11.FPState,
  tround_trip_text_specX (fx := fxk) (rc := rc) (ci := CfImg_A) (cp := CfParams_preset) (PI := prh_img_A) (RL := RL)
    (L := A_prog_listing) (PA := PA) B ARx SK CTX0.
(* ---- Crt102Tail's Section hypotheses (crt102_tail, Qed on the lane base), VERBATIM, each with Crt102Tail's owner.
   Its ENV (api_env SEGS B) is not a hypothesis here: it is PALib's pal_env (Section p) ---- *)
(* the inline release: exactly the three hypotheses of YGcallSx.v's aj_flag_store_x (ASFX = YG0dcf.v
   astack_free_law_cf, FFLX = AR_flag_law_ok_cf / AR_client_img_law_ok_cf, SFX = YGcallScf.v stack_free_x_any) *)
Hypothesis ASFX : forall ly S Hp W mem md mem' md' cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aview SEGS (w_H W) mem' (flag_addr ly cid pos) = Some 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> a <> flag_addr ly cid pos -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, aview SEGS (w_H W) mem a <> None -> aview SEGS (w_H W) mem' a <> None) ->
  m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
  (forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
  ARx ly (stack_free_state cid pos S) Hp W mem' md'.
Hypothesis FFLX : forall ly S Hp (W : world SEGS) mem md cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aowned B ly S (flag_addr ly cid pos) /\ (app_addr (flag_addr ly cid pos) /\ ~ in_img SEGS (flag_addr ly cid pos)).
Hypothesis SFX : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  exists l1 l2, frames S = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos S) = l1 ++ l2.
(* the frame's flag byte is present (at ARcf: AR_flag_law_ok_cf's first conjunct) *)
Hypothesis FFLP : forall ly S Hp (W : world SEGS) mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  apresent (w_H W) mem (flag_addr ly cid pos).
(* __asan_set_shadow_f5 at the poison value 0xf5, the engine's _xm contract (owner: the frame-class lane that
   discharges FCiface contracts at the instance) *)
Hypothesis SETSH : forall fxk : YK11.FPState,
  YGcallMxmn.aset_shadow_realizes_xm (fx := fxk) SEGS B ARx (SIGMA AS___asan_set_shadow_f5) 245.
(* pj_free's contract text (PRH_FnPj.v), at CTX0 and every float state: Crt102Tail's PJFREE *)
Hypothesis PJFREE : forall fxk : YK11.FPState, tpj_free_specX (fx := fxk) B ARx SK CTX0 DOC_D.
(* ---- the U composition's Section hypotheses: Crt102Rewrite's and Crt102Loops' own, VERBATIM, each with its owner ---- *)
(* MARKED STAND-IN (the unit's image binding of B; ARcf gives it by amc_syms / aso_zshadow, YG0f.v:191) *)
Hypothesis zs_aligned : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow B).
(* MARKED STAND-IN (FuzzStrdup.v's img_shadow_vis_cf restated over ARx) *)
Hypothesis img_shadow_vis_x : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> IMG_LO <= a < IMG_TOP ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
(* the rewrite's callee contract texts, at CTX0 and every float state *)
Hypothesis PJSTR : forall fxk : YK11.FPState, PRH_FnPj.tpj_string_specX (fx := fxk) B ARx SK CTX0.
Hypothesis PJSET : forall fxk : YK11.FPState, PRH_FnPj.tpj_set_specX (fx := fxk) B ARx SK CTX0 DOC_D.
Hypothesis RANOUT : forall fxk : YK11.FPState, PRH_FnAlloc.tfuzz_alloc_ran_out_specX (fx := fxk) B ARx SK.
Hypothesis PJWRITE : forall fxk : YK11.FPState, PRH_FnWriter.tpj_write_specX (fx := fxk) B ARx SK CTX0 DOC_D.
Hypothesis PNOTING : forall fxk : YK11.FPState, tparse_noting_specX (fx := fxk) B ARx SK CTX0.
(* the libc rows: __wrap_strlen (the rewrite, +0x2d0) and __wrap_strcmp (the loops) *)
Hypothesis STRLEN : forall fxq : YK11.FPState,
  @YGcallMxmn.astrlen_realizes_xrom fxq SEGS B ARx RLO RHI (SIGMA AS___wrap_strlen).
Hypothesis STRCMP : forall fxq : YK11.FPState,
  @YGcallMxmn.astrcmp_realizes_xrom fxq SEGS B ARx RLO RHI (SIGMA AS___wrap_strcmp).
(* the loops' callee contract texts: same (+0x5f0) at n = DOC_D, fuzz_free (+0x6d0) *)
Hypothesis SAME : forall fxq : YK11.FPState, PRH_FnEx.tsame_specX (fx := fxq) B ARx SK DOC_D.
Hypothesis FFREE : forall fxq : YK11.FPState, PRH_FnAlloc.tfuzz_free_specX (fx := fxq) B ARx SK.

(* ---- X from J: Crt102Kit's segment X (+0x304 .. +0x33c) ---- *)
Lemma crt102_top_X_J : forall a_mod_at a_stamp,
  CRT_A_SEAM_J CTX0 a_mod_at a_stamp -> CRT_A_SEAM_X CTX0 a_mod_at a_stamp.
Proof.
intros a_mod_at a_stamp SJ. unfold CRT_A_SEAM_X, crt_A_under.
intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc t D x Lam peak cnt ran most
  HPRE HMN HCL HCTX H10 HTREE HREAD HLENX HKM HKS HWL0 HWL1 HLED HCNT HRUN HRAN HRQA HLIVE HRQ HFRM
  HROOM HIFC HFRM0 HOS4 HWR HSM HCONS.
pose proof (SJ rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc t D x Lam peak cnt ran most
  HPRE HMN HCL HCTX H10 HTREE HREAD HLENX HKM HKS HWL0 HWL1 HLED HCNT HRUN HRAN HRQA HLIVE HRQ HFRM
  HROOM HIFC HFRM0 HOS4 HWR HSM HCONS) as HJ.
cbv beta in HJ |- *. unfold CRT_A_AT_J in HJ. unfold CRT_A_AT_X.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r HX.
apply @Crt102Kit.crt102rw_at_X with (fx := fx) (rc := rc) (RL := RL) (SK := SK) (B := B) (ARx := ARx) (LAWS := LAWS)
  (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (ly := ly) (S := S) (Hp := Hp)
  (W := W) (regs := regs) (mem := mem) (md := md) (ch := ch) (doc := doc) (t := t) (D := D) (Lam := Lam)
  (peak := peak) (cnt := cnt) (ran := ran) (most := most) (HPRE := HPRE) (HTREE := HTREE) (TAIL := HJ)
  (fxk := fxk) (lyc := lyc) (Sc := Sc) (Hpc := Hpc) (Wc := Wc) (memc := memc) (mdc := mdc) (kj := kj) (pos := pos)
  (Lamc := Lamc) (peakc := peakc) (cntc := cntc) (ownc := ownc) (ranc := ranc) (Dc := Dc) (rg := rg) (r := r).
exact HX.
Qed.

(* ---- the image stand-ins Crt102Entry takes (the unit's image binding of B), for generic B; at the A'
   instance B := AD2l.TfibB each is discharged (Section a below) ---- *)
Section p.
(* MARKED STAND-IN (Crt102Entry's PAL; at TfibB: PALibA.palib_A) *)
Hypothesis PAL : PALib (L := A_prog_listing) (PI := PA) B.
(* MARKED STAND-IN (Crt102Entry's pal_uar_img; at TfibB: crt102_uar_img_TfibA) *)
Hypothesis pal_uar_img : IMG_LO <= as_uar_cell B /\ as_uar_cell B + 4 <= IMG_TOP.
(* MARKED STAND-IN (Crt102Entry's pal_stack_malloc3; at TfibB: Crt102AF0lCheck.crt102_af0l_stack_malloc3) *)
Hypothesis pal_stack_malloc3 : SIGMA AS___asan_stack_malloc_3 = pc_stack_malloc (as_code B) 3.
(* MARKED STAND-IN (Crt102Entry's pal_pst_static; at TfibB: Crt102PALibCheck.crt102_tfib_pst_static_A) *)
Hypothesis pal_pst_static : forall a, Exists (in_zr a) PST ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).

(* ---- THE J SEAM, CLOSED: Crt102Tail.crt102_tail (Qed on the lane base). Its Section hypotheses are this Section's
   (LAWS, OWNLOW, ASFX, FFLX, SFX, FFLP, SETSH, and PJFREE at the Section's CTX0) and the text's own premises; its ENV is PAL's
   pal_env. Only the variables are named in the application (they are the binders of crt102_tail's statement); each
   remaining premise is a hypothesis of this context, found by its type. ---- *)
Lemma crt102_top_J : forall a_mod_at a_stamp, CRT_A_SEAM_J CTX0 a_mod_at a_stamp.
Proof.
intros a_mod_at a_stamp. unfold CRT_A_SEAM_J, crt_A_under.
intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc t D x Lam peak cnt ran most
  HPRE HMN HCL HCTX H10 HTREE HREAD HLENX HKM HKS HWL0 HWL1 HLED HCNT HRUN HRAN HRQA HLIVE HRQ HFRM
  HROOM HIFC HFRM0 HOS4 HWR HSM HCONS.
cbv beta. unfold CRT_A_AT_J.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r HJA.
pose proof (pal_env (PI := PA) B PAL) as ENV.
apply @Crt102Tail.crt102_tail with (fx := fx) (rc := rc) (SK := SK) (RL := RL) (B := B) (ARx := ARx)
  (CTX0 := CTX0)
  (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (ch := ch) (doc := doc) (t := t)
  (D := D) (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)
  (fxk := fxk) (lyc := lyc) (Sc := Sc) (Hpc := Hpc) (Wc := Wc) (memc := memc) (mdc := mdc) (kj := kj) (pos := pos)
  (Lamc := Lamc) (peakc := peakc) (cntc := cntc) (ownc := ownc) (ranc := ranc) (Dc := Dc) (rg := rg) (r := r).
all: assumption.
Qed.

(* ---- THE X SEAM, CLOSED: Crt102Kit's segment X into the J seam (the end of the rewrite / loops chain) ---- *)
Lemma crt102_top_X : forall a_mod_at a_stamp, CRT_A_SEAM_X CTX0 a_mod_at a_stamp.
Proof.
intros a_mod_at a_stamp.
apply @crt102_top_X_J with (a_mod_at := a_mod_at) (a_stamp := a_stamp).
apply @crt102_top_J with (a_mod_at := a_mod_at) (a_stamp := a_stamp).
Qed.

(* ---- THE COMPOSITION: entry .. M (Crt102Entry), M .. J / U (Crt102Arms.arms_at_M, Qed), J closed (crt102_top_J);
   the antecedents are the wild budget (arms_at_M's trailing premise arms_wild_budget, from CRT_A_WILD_BUDGET) and the
   U seam. The cut's text keys on ReaderRes.jr_strtod: the seams are taken at rp_sm := ReaderRes.jr_strtod with the
   tie by reflexivity; the text's wild-room premise (:1366) is handed to the seams (crt_A_under takes it); its last
   premise, astack_up_x at the entry sp (HUP0, :1390), goes to arms_at_M, whose rtt calls read it ---- *)
Lemma crt102_top_of : forall a_mod_at a_stamp,
  CRT_A_WILD_BUDGET CTX0 a_mod_at a_stamp -> CRT_A_SEAM_U CTX0 a_mod_at a_stamp ->
  tcheck_round_trip_specX (fx := fx) (rc := rc) (ci := CfImg_A) (cp := CfParams_preset) (PI := prh_img_A) (RL := RL)
    (L := A_prog_listing) (PA := PA) B ARx SK CTX0 a_mod_at a_stamp.
Proof.
intros a_mod_at a_stamp WB SU. unfold tcheck_round_trip_specX.
intros rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc t D x Lam peak cnt ran most
  HPRE HMN HCL HCTX H10 HTREE HREAD HLENX HKM HKS HWL0 HWL1 HLED HCNT HRUN HRAN HRQA HLIVE HRQ HFRM
  HROOM HIFC HFRM0 HOS4 HWR HCONS HUP0.
set (rp_sm := ReaderRes.jr_strtod).
assert (HSM : rp_sm = ReaderRes.jr_strtod) by reflexivity.
pose proof (crt102_top_J a_mod_at a_stamp rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc t D x Lam peak cnt ran most
  HPRE HMN HCL HCTX H10 HTREE HREAD HLENX HKM HKS HWL0 HWL1 HLED HCNT HRUN HRAN HRQA HLIVE HRQ HFRM
  HROOM HIFC HFRM0 HOS4 HWR HSM HCONS) as HJ.
pose proof (SU rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc t D x Lam peak cnt ran most
  HPRE HMN HCL HCTX H10 HTREE HREAD HLENX HKM HKS HWL0 HWL1 HLED HCNT HRUN HRAN HRQA HLIVE HRQ HFRM
  HROOM HIFC HFRM0 HOS4 HWR HSM HCONS) as HU.
pose proof (WB rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc t D x Lam peak cnt ran most
  HPRE HMN HCL HCTX H10 HTREE HREAD HLENX HKM HKS HWL0 HWL1 HLED HCNT HRUN HRAN HRQA HLIVE HRQ HFRM
  HROOM HIFC HFRM0 HOS4 HWR HSM HCONS) as HWB.
cbv beta in HJ, HU, HWB. unfold CRT_A_AT_J in HJ. unfold CRT_A_AT_U in HU. destruct HWB as [HWBa _].
eapply (YSRrG.SRr'_mono SEGS YGcfRehidePost.RZ_cf).
{ (* entry .. M: Crt102Entry *)
  apply @Crt102Entry.crt102_entry with (fx := fx) (rc := rc) (SK := SK) (RL := RL) (B := B) (ARx := ARx)
    (LAWS := LAWS) (PAL := PAL) (pal_uar_img := pal_uar_img) (pal_stack_malloc3 := pal_stack_malloc3)
    (pal_pst_static := pal_pst_static) (ASM3 := ASM3) (OWNLOW := OWNLOW) (AMS := AMS)
    (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (rp_hist := rp_hist)
    (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (ch := ch) (doc := doc) (t := t)
    (D := D) (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most).
  all: try assumption.
  (* M .. J / U: Crt102Arms.arms_at_M with the J and U stretch statements; its trailing premise arms_wild_budget is
     HWBa (CRT_A_WILD_BUDGET's rtt conjunct) *)
  intros fxk lyc Sc Hpc Wc memc mdc kj pos rg HFZ HFK HL HDR HCZ HPOS.
  apply @Crt102Arms.arms_at_M with (fx := fx) (rc := rc) (SK := SK) (RL := RL) (B := B) (ARx := ARx) (LAWS := LAWS)
    (CTX0 := CTX0) (RTT := RTT)
    (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
    (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (ch := ch) (doc := doc) (t := t)
    (D := D) (x := x) (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)
    (HPRE := HPRE) (HMN := HMN) (HCL := HCL) (HCTX := HCTX) (HTREE := HTREE) (HREAD := HREAD) (HLENX := HLENX)
    (HWL0 := HWL0) (HWL1 := HWL1) (HCNT := HCNT) (HRAN := HRAN) (HRQA := HRQA) (HLIVE := HLIVE) (HRQ := HRQ)
    (HFR := HFRM) (HOS4 := HOS4) (HTAIL := HJ) (HNEXT := HU)
    (fxk := fxk) (lyc := lyc) (Sc := Sc) (Hpc := Hpc) (Wc := Wc) (memc := memc) (mdc := mdc) (kj := kj) (pos := pos)
    (rg := rg).
  all: try assumption. }
(* the post: QF is the text's budgeted post (kb round: fpostFbm .. (wbudget [] (prh_wk F_check_round_trip)) of
   fQmn mem QT, the journal at the same budget WS), and QT is the text's post by unfolding (the inner memnorm keep
   dropped) *)
intros W' c' _ HQ. unfold QF, fpostFbm, fpostFb, YCbqGwild.apost_base_xbFR in HQ |- *.
destruct HQ as (fx2 & ly' & S' & Hp' & regs' & mem' & md' & k & WS & Hc & HFZ' & HFK' & HPW & HJW & Hpr &
  [[HQT _] Hm]).
exists fx2, ly', S', Hp', regs', mem', md', k, WS.
split; [exact Hc|]. split; [exact HFZ'|]. split; [exact HFK'|]. split; [exact HPW|]. split; [exact HJW|].
split; [exact Hpr|]. split; [exact HQT | exact Hm].
Qed.

(* ---- THE U SEAM, at the text's instance of the two strings: Crt102Rewrite.crt102rw_chain (U .. L0, Qed; the four
   goals proved at their sources and retired), its L0 continuation supplied by Crt102Loops.crt102_loops (L0 .. X, Qed)
   at the X seam crt102_top_X (closed), its join TAIL by crt102_top_J (closed). Left: the chain's wild budget
   crt102rw_wild_budget_pn, from CRT_A_WILD_BUDGET (its parse_noting conjunct) ---- *)
Lemma crt102_top_U :
  CRT_A_WILD_BUDGET CTX0 (CRT_MOD_AT_A (rc := rc)) (CRT_STAMP_A (rc := rc)) ->
  CRT_A_SEAM_U CTX0 (CRT_MOD_AT_A (rc := rc)) (CRT_STAMP_A (rc := rc)).
Proof.
intros WB. unfold CRT_A_SEAM_U, crt_A_under.
intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc t D x Lam peak cnt ran most
  HPRE HMN HCL HCTX H10 HTREE HREAD HLENX HKM HKS HWL0 HWL1 HLED HCNT HRUN HRAN HRQA HLIVE HRQ HFRM
  HROOM HIFC HFRM0 HOS4 HWR HSM HCONS.
pose proof (WB rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc t D x Lam peak cnt ran most
  HPRE HMN HCL HCTX H10 HTREE HREAD HLENX HKM HKS HWL0 HWL1 HLED HCNT HRUN HRAN HRQA HLIVE HRQ HFRM
  HROOM HIFC HFRM0 HOS4 HWR HSM HCONS) as HWB.
cbv beta in HWB. destruct HWB as [_ HWBp].
pose proof (crt102_top_J _ _ rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc t D x Lam peak cnt
  ran most HPRE HMN HCL HCTX H10 HTREE HREAD HLENX HKM HKS HWL0 HWL1 HLED HCNT HRUN HRAN HRQA HLIVE HRQ HFRM
  HROOM HIFC HFRM0 HOS4 HWR HSM HCONS) as HJ.
pose proof (crt102_top_X _ _ rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc t D x Lam peak cnt
  ran most HPRE HMN HCL HCTX H10 HTREE HREAD HLENX HKM HKS HWL0 HWL1 HLED HCNT HRUN HRAN HRQA HLIVE HRQ HFRM
  HROOM HIFC HFRM0 HOS4 HWR HSM HCONS) as HX.
cbv beta in HJ, HX |- *. unfold CRT_A_AT_J in HJ. unfold CRT_A_AT_X in HX. unfold CRT_A_AT_U.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms HU.
exact (@Crt102Rewrite.crt102rw_chain fx rc RL SK B ARx LAWS zs_aligned img_shadow_vis_x
  rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md ch doc t D x Lam peak cnt ran most CTX0
  HPRE HTREE HMN HCL HREAD HLENX HKM HKS HWL0 HWL1 HCNT HLED HRAN HRQA HLIVE HRQ HFRM HOS4
  PJSTR PJSET RANOUT PJWRITE PNOTING STRLEN HJ HWBp
  (@Crt102Loops.crt102_loops fx rc SK RL B ARx LAWS STRCMP zs_aligned img_shadow_vis_x SAME FFREE
     rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md ch doc t D x Lam peak cnt ran most CTX0
     HREAD HLENX HWL0 HWL1 HLED HCNT HRAN HRQA HKM HKS HOS4 HPRE HTREE HMN HCL HCTX PJFREE HX)
  fxk lyc Sc Hpc Wc memc mdc kj pos Db Lamc peakc cntc rg ms HU).
Qed.

(* ---- THE CONTRACT AT A', generic in B, at the text's instance of its two string addresses: Qed. crt102_top_of's and
   crt102_top_U's premise CRT_A_WILD_BUDGET is crt102_top_wild_budget (kb round, from the text's own wild-room premise),
   and the U seam owes nothing more: the four goals (DEAD-PJSTRING / -PJSET / -PJWRITE, FREEORD-COPY) are proved
   at their sources in Crt102Rewrite and retired with the Record CRT_A_OPEN_RW (the Step-1 ruling on 1409ad6e7e37;
   the contract modulo that Record, crt102_top_open, is this statement and is retired with it). ---- *)
Theorem crt102_top :
  tcheck_round_trip_specX (fx := fx) (rc := rc) (ci := CfImg_A) (cp := CfParams_preset) (PI := prh_img_A) (RL := RL)
    (L := A_prog_listing) (PA := PA) B ARx SK CTX0 (CRT_MOD_AT_A (rc := rc)) (CRT_STAMP_A (rc := rc)).
Proof using LAWS ASM3 OWNLOW AMS RTT ASFX FFLX SFX FFLP SETSH PJFREE zs_aligned img_shadow_vis_x PJSTR PJSET RANOUT
  PJWRITE PNOTING STRLEN STRCMP SAME FFREE PAL pal_uar_img pal_stack_malloc3 pal_pst_static.
pose proof (crt102_top_wild_budget CTX0 (CRT_MOD_AT_A (rc := rc)) (CRT_STAMP_A (rc := rc))) as WB.
exact (crt102_top_of (CRT_MOD_AT_A (rc := rc)) (CRT_STAMP_A (rc := rc)) WB (crt102_top_U WB)).
Qed.

End p.
End f.

(* ======================================================================================================== *)
(* ---- THE A' INSTANCE OF B: AD2l.TfibB, the A' asan image's generated record (lib/A/AD2l.v eb321db7a357,
   TfibB_syms : AF0m.TfibSyms TfibB). Crt102Entry's four image stand-ins are discharged here, not assumed:
     PAL               PALibA.palib_A (the A' witness, lib/A/PALibA.v 88c72c8175cf by path from
                       commit 83ac1a932a8d; every field by vm_compute on AF0l dfca6bb1a8d7), which
                       also gives Crt102Tail's ENV (pal_env);
     pal_stack_malloc3 Crt102AF0lCheck.crt102_af0l_stack_malloc3 (the listing's symbol = AF0l's pc_stack_malloc 3;
                       as_code TfibB is Tfib_code by its definition);
     pal_uar_img       crt102_uar_img_TfibA below, by computation on TfibB's as_uar_cell;
     pal_pst_static    Crt102PALibCheck.crt102_tfib_pst_static_A at TfibB_syms (by computation over prh_pst).
   ARx stays free: the allocator-side hypotheses keep their owners (header). ---- *)
Section a.
Context {ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop}.
#[local] Notation TA := (AD2l.TfibB).
(* the Section hypotheses of Section f, at B := TfibB; owners as there *)
Hypothesis LAWS : AR_laws_x SEGS TA ARx cf_head.
Hypothesis ASM3 : YGcallMxmn.astack_malloc_realizes_xm (fx := fx) SEGS TA ARx 3.
Hypothesis OWNLOW : ARx_owned_low_law SEGS TA ARx.
Hypothesis AMS : YGcallMxmn.aintrin_realizes_xm (fx := fx) SEGS TA ARx OSet (SIGMA AS___asan_memset).
(* the universe closure of the text's call; the callee texts at it, as in Section f *)
Variable CTX0 : list (list Z).
Hypothesis RTT : forall fxk : YK11.FPState,
  tround_trip_text_specX (fx := fxk) (rc := rc) (ci := CfImg_A) (cp := CfParams_preset) (PI := prh_img_A) (RL := RL)
    (L := A_prog_listing) (PA := PA) TA ARx SK CTX0.
Hypothesis ASFX : forall ly S Hp W mem md mem' md' cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aview SEGS (w_H W) mem' (flag_addr ly cid pos) = Some 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned TA ly S a -> a <> flag_addr ly cid pos -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, aview SEGS (w_H W) mem a <> None -> aview SEGS (w_H W) mem' a <> None) ->
  m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
  (forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
  ARx ly (stack_free_state cid pos S) Hp W mem' md'.
Hypothesis FFLX : forall ly S Hp (W : world SEGS) mem md cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aowned TA ly S (flag_addr ly cid pos) /\ (app_addr (flag_addr ly cid pos) /\ ~ in_img SEGS (flag_addr ly cid pos)).
Hypothesis SFX : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  exists l1 l2, frames S = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos S) = l1 ++ l2.
Hypothesis FFLP : forall ly S Hp (W : world SEGS) mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  apresent (w_H W) mem (flag_addr ly cid pos).
Hypothesis SETSH : forall fxk : YK11.FPState,
  YGcallMxmn.aset_shadow_realizes_xm (fx := fxk) SEGS TA ARx (SIGMA AS___asan_set_shadow_f5) 245.
Hypothesis PJFREE : forall fxk : YK11.FPState, tpj_free_specX (fx := fxk) TA ARx SK CTX0 DOC_D.
(* the U composition's Section hypotheses at B := TfibB; owners as in Section f. img_shadow_vis_x stays a MARKED
   STAND-IN (it reads ARx, which stays free); zs_aligned is DISCHARGED below by computation on
   TfibB's zero-shadow table (crt102_zs_aligned_TfibA) *)
Hypothesis img_shadow_vis_x : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> IMG_LO <= a < IMG_TOP ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
Hypothesis PJSTR : forall fxk : YK11.FPState, PRH_FnPj.tpj_string_specX (fx := fxk) TA ARx SK CTX0.
Hypothesis PJSET : forall fxk : YK11.FPState, PRH_FnPj.tpj_set_specX (fx := fxk) TA ARx SK CTX0 DOC_D.
Hypothesis RANOUT : forall fxk : YK11.FPState, PRH_FnAlloc.tfuzz_alloc_ran_out_specX (fx := fxk) TA ARx SK.
Hypothesis PJWRITE : forall fxk : YK11.FPState, PRH_FnWriter.tpj_write_specX (fx := fxk) TA ARx SK CTX0 DOC_D.
Hypothesis PNOTING : forall fxk : YK11.FPState, tparse_noting_specX (fx := fxk) TA ARx SK CTX0.
Hypothesis STRLEN : forall fxq : YK11.FPState,
  @YGcallMxmn.astrlen_realizes_xrom fxq SEGS TA ARx RLO RHI (SIGMA AS___wrap_strlen).
Hypothesis STRCMP : forall fxq : YK11.FPState,
  @YGcallMxmn.astrcmp_realizes_xrom fxq SEGS TA ARx RLO RHI (SIGMA AS___wrap_strcmp).
Hypothesis SAME : forall fxq : YK11.FPState, PRH_FnEx.tsame_specX (fx := fxq) TA ARx SK DOC_D.
Hypothesis FFREE : forall fxq : YK11.FPState, PRH_FnAlloc.tfuzz_free_specX (fx := fxq) TA ARx SK.

(* zs_aligned at TfibB, by computation: every zero-shadow range of the A' image record starts and ends 8-aligned *)
Lemma crt102_zs_aligned_TfibA : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow TA).
Proof.
apply Forall_forall. intros r Hr.
assert (Hb : forallb (fun r => (fst r mod 8 =? 0) && (snd r mod 8 =? 0)) (as_zero_shadow TA) = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in Hb. specialize (Hb r Hr). apply andb_true_iff in Hb as [H1 H2].
split; apply Z.eqb_eq; assumption.
Qed.

Lemma crt102_uar_img_TfibA : IMG_LO <= as_uar_cell TA /\ as_uar_cell TA + 4 <= IMG_TOP.
Proof. split; apply Z.leb_le; vm_compute; reflexivity. Qed.

Lemma crt102_top_of_TfibA : forall a_mod_at a_stamp,
  CRT_A_WILD_BUDGET (B := TA) (ARx := ARx) CTX0 a_mod_at a_stamp ->
  CRT_A_SEAM_U (B := TA) (ARx := ARx) CTX0 a_mod_at a_stamp ->
  tcheck_round_trip_specX (fx := fx) (rc := rc) (ci := CfImg_A) (cp := CfParams_preset) (PI := prh_img_A) (RL := RL)
    (L := A_prog_listing) (PA := PA) TA ARx SK CTX0 a_mod_at a_stamp.
Proof.
intros a_mod_at a_stamp WB SU.
apply @crt102_top_of with (B := TA) (ARx := ARx)
  (LAWS := LAWS) (ASM3 := ASM3) (OWNLOW := OWNLOW) (AMS := AMS) (RTT := RTT)
  (PAL := PALibA.palib_A (rc := rc))
  (pal_uar_img := crt102_uar_img_TfibA)
  (pal_stack_malloc3 := Crt102AF0lCheck.crt102_af0l_stack_malloc3 (rc := rc))
  (pal_pst_static := Crt102PALibCheck.crt102_tfib_pst_static_A TA AD2l.TfibB_syms)
  (CTX0 := CTX0) (a_mod_at := a_mod_at) (a_stamp := a_stamp).
(* the antecedents by name; Crt102Tail's hypotheses (those crt102_tail uses) are this Section's, found by their type *)
all: first [exact WB | exact SU | assumption].
Qed.

(* ---- THE CONTRACT AT THE A' INSTANCE (B := TfibB, the strings at CRT_MOD_AT_A / CRT_STAMP_A), with Crt102Entry's
   four image stand-ins and zs_aligned discharged: Qed, as crt102_top (CRT_A_WILD_BUDGET at TfibB is
   crt102_top_wild_budget at B := TfibB; no Record is owed). img_shadow_vis_x is the one stand-in left (header). ---- *)
Theorem crt102_top_TfibA :
  tcheck_round_trip_specX (fx := fx) (rc := rc) (ci := CfImg_A) (cp := CfParams_preset) (PI := prh_img_A) (RL := RL)
    (L := A_prog_listing) (PA := PA) TA ARx SK CTX0 (CRT_MOD_AT_A (rc := rc)) (CRT_STAMP_A (rc := rc)).
Proof using LAWS ASM3 OWNLOW AMS RTT ASFX FFLX SFX FFLP SETSH PJFREE img_shadow_vis_x PJSTR PJSET RANOUT PJWRITE PNOTING
  STRLEN STRCMP SAME FFREE.
pose proof (crt102_top_wild_budget (B := TA) (ARx := ARx) CTX0 (CRT_MOD_AT_A (rc := rc)) (CRT_STAMP_A (rc := rc))) as WB.
apply (crt102_top_of_TfibA _ _ WB).
apply @crt102_top_U with (B := TA) (ARx := ARx) (LAWS := LAWS) (OWNLOW := OWNLOW)
  (PAL := PALibA.palib_A (rc := rc))
  (zs_aligned := crt102_zs_aligned_TfibA) (img_shadow_vis_x := img_shadow_vis_x)
  (PJSTR := PJSTR) (PJSET := PJSET) (RANOUT := RANOUT) (PJWRITE := PJWRITE) (PNOTING := PNOTING)
  (STRLEN := STRLEN) (STRCMP := STRCMP) (SAME := SAME) (FFREE := FFREE)
  (CTX0 := CTX0).
(* the antecedent by name; Crt102Tail's hypotheses are this Section's, found by their type *)
all: first [exact WB | assumption].
Qed.
End a.
End w.

(* ---- the FPState elaboration check (the walk owner's rule and its amendment, 2026-10-29): theorems by `Check @`, with
   implicits shown; every Prop-bodied definition of this file by `Print`, implicits on and notations off, so the body
   is read. The class position of every FPState-taking constant must hold the Section's `fx`; a bound `fxk` may appear
   only as an explicit argument (crt_cfg .. fxk, inside the glue's crt_at_* bodies) or as RTT's own binder. ---- *)
Set Printing Implicit.
Check @crt102_top_J.
Check @crt102_top_X.
Check @crt102_top_of.
Check @crt102_top_of_TfibA.
Check @crt102_top_X_J.
Check @crt102_top_U.
(* the wild budget (kb round) and the four CRT_A_OPEN_RW goals (proved at their sources, the Step-1 ruling) are
   discharged, so the contract is a constant (Qed) *)
Check @crt102_top_wild_budget.
Check @crt102_top.
Check @crt102_top_TfibA.
Unset Printing Notations.
Print CRT_A_AT_J.
Print CRT_A_AT_U.
Print CRT_A_AT_X.
Print crt_A_under.
Print CRT_A_SEAM_J.
Print CRT_A_SEAM_U.
Print CRT_A_SEAM_X.
Print CRT_A_WILD_BUDGET.
Set Printing Notations.
Unset Printing Implicit.

(* every exported name resolves to the compiled constant of THIS file (Locate against the .vo, not a text search) *)
Locate crt102_top_of.
Locate crt102_top_of_TfibA.
Locate crt102_top_X_J.
Locate crt102_top_J.
Locate crt102_top_X.
Locate CRT_A_WILD_BUDGET.
Locate crt102_top_wild_budget.
Locate crt102_top.
Locate crt102_top_TfibA.
Locate crt102_uar_img_TfibA.
Locate CRT_A_SEAM_J.
Locate CRT_A_SEAM_U.
Locate crt102_top_U.
Locate crt102_zs_aligned_TfibA.

Print Assumptions crt102_top_of.
Print Assumptions crt102_top_of_TfibA.
Print Assumptions crt102_top_X_J.
Print Assumptions crt102_top_J.
Print Assumptions crt102_top_X.
Print Assumptions crt102_top_U.
Print Assumptions crt102_top_wild_budget.
Print Assumptions crt102_top.
Print Assumptions crt102_top_TfibA.
